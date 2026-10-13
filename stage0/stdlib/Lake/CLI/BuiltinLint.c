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
uint8_t v___x_173_; 
v___x_173_ = lean_nat_dec_le(v___x_171_, v___x_171_);
if (v___x_173_ == 0)
{
if (v___x_172_ == 0)
{
v___y_157_ = v___x_169_;
goto v___jp_156_;
}
else
{
size_t v___x_174_; size_t v___x_175_; lean_object* v___x_176_; 
v___x_174_ = ((size_t)0ULL);
v___x_175_ = lean_usize_of_nat(v___x_171_);
v___x_176_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_leanOptOverrides_spec__2(v_linterOverrides_154_, v___x_174_, v___x_175_, v___x_169_);
v___y_157_ = v___x_176_;
goto v___jp_156_;
}
}
else
{
size_t v___x_177_; size_t v___x_178_; lean_object* v___x_179_; 
v___x_177_ = ((size_t)0ULL);
v___x_178_ = lean_usize_of_nat(v___x_171_);
v___x_179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_leanOptOverrides_spec__2(v_linterOverrides_154_, v___x_177_, v___x_178_, v___x_169_);
v___y_157_ = v___x_179_;
goto v___jp_156_;
}
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
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_leanOptOverrides___boxed(lean_object* v_args_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lake_BuiltinLint_leanOptOverrides(v_args_180_);
lean_dec_ref(v_args_180_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0(lean_object* v_init_182_, lean_object* v_t_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0(v_init_182_, v_t_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0___boxed(lean_object* v_init_185_, lean_object* v_t_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0(v_init_185_, v_t_186_);
lean_dec(v_t_186_);
return v_res_187_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__1(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_189_ = lean_box(0);
v___x_190_ = l_Lean_instInhabitedPosition_default;
v___x_191_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_192_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v___x_190_);
lean_ctor_set(v___x_192_, 2, v___x_189_);
return v___x_192_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_instInhabitedExceptionRecord_default(void){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = lean_obj_once(&l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__1, &l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__1_once, _init_l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__1);
return v___x_193_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_instInhabitedExceptionRecord(void){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lake_BuiltinLint_instInhabitedExceptionRecord_default;
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorIdx___impl(lean_object* v_x_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = lean_obj_tag_nat(v_x_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorIdx___impl___boxed(lean_object* v_x_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorIdx___impl(v_x_197_);
lean_dec_ref(v_x_197_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___redArg(lean_object* v_t_199_, lean_object* v_k_200_){
_start:
{
switch(lean_obj_tag(v_t_199_))
{
case 0:
{
uint8_t v_failed_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v_failed_201_ = lean_ctor_get_uint8(v_t_199_, 0);
lean_dec_ref_known(v_t_199_, 0);
v___x_202_ = lean_box(v_failed_201_);
v___x_203_ = lean_apply_1(v_k_200_, v___x_202_);
return v___x_203_;
}
case 1:
{
lean_object* v_records_204_; uint8_t v_unlocated_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v_records_204_ = lean_ctor_get(v_t_199_, 0);
lean_inc_ref(v_records_204_);
v_unlocated_205_ = lean_ctor_get_uint8(v_t_199_, sizeof(void*)*1);
lean_dec_ref_known(v_t_199_, 1);
v___x_206_ = lean_box(v_unlocated_205_);
v___x_207_ = lean_apply_2(v_k_200_, v_records_204_, v___x_206_);
return v___x_207_;
}
default: 
{
lean_object* v_entries_208_; lean_object* v___x_209_; 
v_entries_208_ = lean_ctor_get(v_t_199_, 0);
lean_inc_ref(v_entries_208_);
lean_dec_ref_known(v_t_199_, 1);
v___x_209_ = lean_apply_1(v_k_200_, v_entries_208_);
return v___x_209_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim(lean_object* v_motive_210_, lean_object* v_ctorIdx_211_, lean_object* v_t_212_, lean_object* v_h_213_, lean_object* v_k_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___redArg(v_t_212_, v_k_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___boxed(lean_object* v_motive_216_, lean_object* v_ctorIdx_217_, lean_object* v_t_218_, lean_object* v_h_219_, lean_object* v_k_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim(v_motive_216_, v_ctorIdx_217_, v_t_218_, v_h_219_, v_k_220_);
lean_dec(v_ctorIdx_217_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_reported_elim___redArg(lean_object* v_t_222_, lean_object* v_reported_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___redArg(v_t_222_, v_reported_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_reported_elim(lean_object* v_motive_225_, lean_object* v_t_226_, lean_object* v_h_227_, lean_object* v_reported_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___redArg(v_t_226_, v_reported_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_recorded_elim___redArg(lean_object* v_t_230_, lean_object* v_recorded_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___redArg(v_t_230_, v_recorded_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_recorded_elim(lean_object* v_motive_233_, lean_object* v_t_234_, lean_object* v_h_235_, lean_object* v_recorded_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___redArg(v_t_234_, v_recorded_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_codeQualityChecks_elim___redArg(lean_object* v_t_238_, lean_object* v_codeQualityChecks_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___redArg(v_t_238_, v_codeQualityChecks_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_codeQualityChecks_elim(lean_object* v_motive_241_, lean_object* v_t_242_, lean_object* v_h_243_, lean_object* v_codeQualityChecks_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___redArg(v_t_242_, v_codeQualityChecks_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorIdx___impl(lean_object* v_x_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = lean_obj_tag_nat(v_x_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorIdx___impl___boxed(lean_object* v_x_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorIdx___impl(v_x_248_);
lean_dec_ref(v_x_248_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(lean_object* v_t_250_, lean_object* v_k_251_){
_start:
{
if (lean_obj_tag(v_t_250_) == 0)
{
uint8_t v_failed_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v_failed_252_ = lean_ctor_get_uint8(v_t_250_, 0);
lean_dec_ref_known(v_t_250_, 0);
v___x_253_ = lean_box(v_failed_252_);
v___x_254_ = lean_apply_1(v_k_251_, v___x_253_);
return v___x_254_;
}
else
{
lean_object* v_records_255_; uint8_t v_unlocated_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_records_255_ = lean_ctor_get(v_t_250_, 0);
lean_inc_ref(v_records_255_);
v_unlocated_256_ = lean_ctor_get_uint8(v_t_250_, sizeof(void*)*1);
lean_dec_ref_known(v_t_250_, 1);
v___x_257_ = lean_box(v_unlocated_256_);
v___x_258_ = lean_apply_2(v_k_251_, v_records_255_, v___x_257_);
return v___x_258_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim(lean_object* v_motive_259_, lean_object* v_ctorIdx_260_, lean_object* v_t_261_, lean_object* v_h_262_, lean_object* v_k_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(v_t_261_, v_k_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___boxed(lean_object* v_motive_265_, lean_object* v_ctorIdx_266_, lean_object* v_t_267_, lean_object* v_h_268_, lean_object* v_k_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim(v_motive_265_, v_ctorIdx_266_, v_t_267_, v_h_268_, v_k_269_);
lean_dec(v_ctorIdx_266_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_reported_elim___redArg(lean_object* v_t_271_, lean_object* v_reported_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(v_t_271_, v_reported_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_reported_elim(lean_object* v_motive_274_, lean_object* v_t_275_, lean_object* v_h_276_, lean_object* v_reported_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(v_t_275_, v_reported_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_recorded_elim___redArg(lean_object* v_t_279_, lean_object* v_recorded_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(v_t_279_, v_recorded_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_recorded_elim(lean_object* v_motive_282_, lean_object* v_t_283_, lean_object* v_h_284_, lean_object* v_recorded_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(v_t_283_, v_recorded_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(lean_object* v_pkgRoot_287_, lean_object* v_as_288_, size_t v_i_289_, size_t v_stop_290_, lean_object* v_b_291_){
_start:
{
lean_object* v___y_293_; uint8_t v___x_297_; 
v___x_297_ = lean_usize_dec_eq(v_i_289_, v_stop_290_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; uint8_t v___y_300_; lean_object* v_fst_302_; lean_object* v_snd_303_; uint8_t v___x_304_; 
v___x_298_ = lean_array_uget_borrowed(v_as_288_, v_i_289_);
v_fst_302_ = lean_ctor_get(v___x_298_, 0);
v_snd_303_ = lean_ctor_get(v___x_298_, 1);
v___x_304_ = l_Lean_Name_isPrefixOf(v_pkgRoot_287_, v_fst_302_);
if (v___x_304_ == 0)
{
v___y_300_ = v___x_304_;
goto v___jp_299_;
}
else
{
lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_305_ = lean_array_get_size(v_snd_303_);
v___x_306_ = lean_unsigned_to_nat(0u);
v___x_307_ = lean_nat_dec_eq(v___x_305_, v___x_306_);
if (v___x_307_ == 0)
{
v___y_300_ = v___x_304_;
goto v___jp_299_;
}
else
{
v___y_293_ = v_b_291_;
goto v___jp_292_;
}
}
v___jp_299_:
{
if (v___y_300_ == 0)
{
v___y_293_ = v_b_291_;
goto v___jp_292_;
}
else
{
lean_object* v___x_301_; 
lean_inc(v___x_298_);
v___x_301_ = lean_array_push(v_b_291_, v___x_298_);
v___y_293_ = v___x_301_;
goto v___jp_292_;
}
}
}
else
{
return v_b_291_;
}
v___jp_292_:
{
size_t v___x_294_; size_t v___x_295_; 
v___x_294_ = ((size_t)1ULL);
v___x_295_ = lean_usize_add(v_i_289_, v___x_294_);
v_i_289_ = v___x_295_;
v_b_291_ = v___y_293_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0___boxed(lean_object* v_pkgRoot_308_, lean_object* v_as_309_, lean_object* v_i_310_, lean_object* v_stop_311_, lean_object* v_b_312_){
_start:
{
size_t v_i_boxed_313_; size_t v_stop_boxed_314_; lean_object* v_res_315_; 
v_i_boxed_313_ = lean_unbox_usize(v_i_310_);
lean_dec(v_i_310_);
v_stop_boxed_314_ = lean_unbox_usize(v_stop_311_);
lean_dec(v_stop_311_);
v_res_315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(v_pkgRoot_308_, v_as_309_, v_i_boxed_313_, v_stop_boxed_314_, v_b_312_);
lean_dec_ref(v_as_309_);
lean_dec(v_pkgRoot_308_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(lean_object* v_env_318_, lean_object* v_pkgRoot_319_){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_320_ = lean_unsigned_to_nat(0u);
v___x_321_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0));
v___x_322_ = l_Lean_Linter_getAllLints(v_env_318_);
v___x_323_ = lean_array_get_size(v___x_322_);
v___x_324_ = lean_nat_dec_lt(v___x_320_, v___x_323_);
if (v___x_324_ == 0)
{
lean_dec_ref(v___x_322_);
return v___x_321_;
}
else
{
uint8_t v___x_325_; 
v___x_325_ = lean_nat_dec_le(v___x_323_, v___x_323_);
if (v___x_325_ == 0)
{
if (v___x_324_ == 0)
{
lean_dec_ref(v___x_322_);
return v___x_321_;
}
else
{
size_t v___x_326_; size_t v___x_327_; lean_object* v___x_328_; 
v___x_326_ = ((size_t)0ULL);
v___x_327_ = lean_usize_of_nat(v___x_323_);
v___x_328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(v_pkgRoot_319_, v___x_322_, v___x_326_, v___x_327_, v___x_321_);
lean_dec_ref(v___x_322_);
return v___x_328_;
}
}
else
{
size_t v___x_329_; size_t v___x_330_; lean_object* v___x_331_; 
v___x_329_ = ((size_t)0ULL);
v___x_330_ = lean_usize_of_nat(v___x_323_);
v___x_331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(v_pkgRoot_319_, v___x_322_, v___x_329_, v___x_330_, v___x_321_);
lean_dec_ref(v___x_322_);
return v___x_331_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___boxed(lean_object* v_env_332_, lean_object* v_pkgRoot_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(v_env_332_, v_pkgRoot_333_);
lean_dec(v_pkgRoot_333_);
lean_dec_ref(v_env_332_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__0(size_t v_sz_335_, size_t v_i_336_, lean_object* v_bs_337_){
_start:
{
uint8_t v___x_338_; 
v___x_338_ = lean_usize_dec_lt(v_i_336_, v_sz_335_);
if (v___x_338_ == 0)
{
return v_bs_337_;
}
else
{
lean_object* v_v_339_; lean_object* v_entry_340_; lean_object* v___x_341_; lean_object* v_bs_x27_342_; size_t v___x_343_; size_t v___x_344_; lean_object* v___x_345_; 
v_v_339_ = lean_array_uget_borrowed(v_bs_337_, v_i_336_);
v_entry_340_ = lean_ctor_get(v_v_339_, 1);
lean_inc_ref(v_entry_340_);
v___x_341_ = lean_unsigned_to_nat(0u);
v_bs_x27_342_ = lean_array_uset(v_bs_337_, v_i_336_, v___x_341_);
v___x_343_ = ((size_t)1ULL);
v___x_344_ = lean_usize_add(v_i_336_, v___x_343_);
v___x_345_ = lean_array_uset(v_bs_x27_342_, v_i_336_, v_entry_340_);
v_i_336_ = v___x_344_;
v_bs_337_ = v___x_345_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__0___boxed(lean_object* v_sz_347_, lean_object* v_i_348_, lean_object* v_bs_349_){
_start:
{
size_t v_sz_boxed_350_; size_t v_i_boxed_351_; lean_object* v_res_352_; 
v_sz_boxed_350_ = lean_unbox_usize(v_sz_347_);
lean_dec(v_sz_347_);
v_i_boxed_351_ = lean_unbox_usize(v_i_348_);
lean_dec(v_i_348_);
v_res_352_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__0(v_sz_boxed_350_, v_i_boxed_351_, v_bs_349_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__1(lean_object* v_linterOpts_353_, lean_object* v_as_354_, size_t v_i_355_, size_t v_stop_356_, lean_object* v_b_357_){
_start:
{
lean_object* v___y_359_; uint8_t v___x_363_; 
v___x_363_ = lean_usize_dec_eq(v_i_355_, v_stop_356_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; lean_object* v_linter_x3f_365_; 
v___x_364_ = lean_array_uget_borrowed(v_as_354_, v_i_355_);
v_linter_x3f_365_ = lean_ctor_get(v___x_364_, 0);
if (lean_obj_tag(v_linter_x3f_365_) == 0)
{
lean_object* v___x_366_; 
lean_inc(v___x_364_);
v___x_366_ = lean_array_push(v_b_357_, v___x_364_);
v___y_359_ = v___x_366_;
goto v___jp_358_;
}
else
{
lean_object* v_val_367_; uint8_t v___x_368_; 
v_val_367_ = lean_ctor_get(v_linter_x3f_365_, 0);
v___x_368_ = l_Lean_Linter_isLinterEnabledByOptions(v_val_367_, v_linterOpts_353_);
if (v___x_368_ == 0)
{
v___y_359_ = v_b_357_;
goto v___jp_358_;
}
else
{
lean_object* v___x_369_; 
lean_inc(v___x_364_);
v___x_369_ = lean_array_push(v_b_357_, v___x_364_);
v___y_359_ = v___x_369_;
goto v___jp_358_;
}
}
}
else
{
return v_b_357_;
}
v___jp_358_:
{
size_t v___x_360_; size_t v___x_361_; 
v___x_360_ = ((size_t)1ULL);
v___x_361_ = lean_usize_add(v_i_355_, v___x_360_);
v_i_355_ = v___x_361_;
v_b_357_ = v___y_359_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__1___boxed(lean_object* v_linterOpts_370_, lean_object* v_as_371_, lean_object* v_i_372_, lean_object* v_stop_373_, lean_object* v_b_374_){
_start:
{
size_t v_i_boxed_375_; size_t v_stop_boxed_376_; lean_object* v_res_377_; 
v_i_boxed_375_ = lean_unbox_usize(v_i_372_);
lean_dec(v_i_372_);
v_stop_boxed_376_ = lean_unbox_usize(v_stop_373_);
lean_dec(v_stop_373_);
v_res_377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__1(v_linterOpts_370_, v_as_371_, v_i_boxed_375_, v_stop_boxed_376_, v_b_374_);
lean_dec_ref(v_as_371_);
lean_dec_ref(v_linterOpts_370_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__2(lean_object* v_args_380_, lean_object* v_linterOpts_381_, lean_object* v_mod_382_, lean_object* v_as_383_, size_t v_sz_384_, size_t v_i_385_, lean_object* v_b_386_){
_start:
{
lean_object* v_a_388_; uint8_t v___x_392_; 
v___x_392_ = lean_usize_dec_lt(v_i_385_, v_sz_384_);
if (v___x_392_ == 0)
{
return v_b_386_;
}
else
{
lean_object* v_a_393_; lean_object* v_fst_394_; lean_object* v_snd_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_437_; 
v_a_393_ = lean_array_uget(v_as_383_, v_i_385_);
v_fst_394_ = lean_ctor_get(v_a_393_, 0);
v_snd_395_ = lean_ctor_get(v_a_393_, 1);
v_isSharedCheck_437_ = !lean_is_exclusive(v_a_393_);
if (v_isSharedCheck_437_ == 0)
{
v___x_397_ = v_a_393_;
v_isShared_398_ = v_isSharedCheck_437_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_snd_395_);
lean_inc(v_fst_394_);
lean_dec(v_a_393_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_437_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v_fst_399_; lean_object* v_snd_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_436_; 
v_fst_399_ = lean_ctor_get(v_b_386_, 0);
v_snd_400_ = lean_ctor_get(v_b_386_, 1);
v_isSharedCheck_436_ = !lean_is_exclusive(v_b_386_);
if (v_isSharedCheck_436_ == 0)
{
v___x_402_ = v_b_386_;
v_isShared_403_ = v_isSharedCheck_436_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_snd_400_);
lean_inc(v_fst_399_);
lean_dec(v_b_386_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_436_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___y_405_; lean_object* v___y_406_; uint8_t v___y_419_; lean_object* v___x_433_; uint8_t v___x_434_; 
v___x_433_ = l_Lean_Name_getRoot(v_mod_382_);
v___x_434_ = l_Lean_Name_isPrefixOf(v___x_433_, v_fst_394_);
lean_dec(v___x_433_);
if (v___x_434_ == 0)
{
v___y_419_ = v___x_434_;
goto v___jp_418_;
}
else
{
uint8_t v___x_435_; 
v___x_435_ = l_Lean_NameSet_contains(v_fst_399_, v_fst_394_);
if (v___x_435_ == 0)
{
v___y_419_ = v___x_434_;
goto v___jp_418_;
}
else
{
lean_del_object(v___x_402_);
lean_dec(v_snd_395_);
lean_dec(v_fst_394_);
goto v___jp_414_;
}
}
v___jp_404_:
{
size_t v_sz_407_; size_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_412_; 
v_sz_407_ = lean_array_size(v___y_406_);
v___x_408_ = ((size_t)0ULL);
v___x_409_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__0(v_sz_407_, v___x_408_, v___y_406_);
v___x_410_ = l_Array_append___redArg(v_snd_400_, v___x_409_);
lean_dec_ref(v___x_409_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 1, v___x_410_);
lean_ctor_set(v___x_402_, 0, v___y_405_);
v___x_412_ = v___x_402_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___y_405_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v___x_410_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
v_a_388_ = v___x_412_;
goto v___jp_387_;
}
}
v___jp_414_:
{
lean_object* v___x_416_; 
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 1, v_snd_400_);
lean_ctor_set(v___x_397_, 0, v_fst_399_);
v___x_416_ = v___x_397_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_fst_399_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_snd_400_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
v_a_388_ = v___x_416_;
goto v___jp_387_;
}
}
v___jp_418_:
{
if (v___y_419_ == 0)
{
lean_del_object(v___x_402_);
lean_dec(v_snd_395_);
lean_dec(v_fst_394_);
goto v___jp_414_;
}
else
{
uint8_t v_lintOnly_420_; lean_object* v___x_421_; 
lean_del_object(v___x_397_);
v_lintOnly_420_ = lean_ctor_get_uint8(v_args_380_, sizeof(void*)*4);
v___x_421_ = l_Lean_NameSet_insert(v_fst_399_, v_fst_394_);
if (v_lintOnly_420_ == 0)
{
v___y_405_ = v___x_421_;
v___y_406_ = v_snd_395_;
goto v___jp_404_;
}
else
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; uint8_t v___x_425_; 
v___x_422_ = lean_unsigned_to_nat(0u);
v___x_423_ = lean_array_get_size(v_snd_395_);
v___x_424_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__2___closed__0));
v___x_425_ = lean_nat_dec_lt(v___x_422_, v___x_423_);
if (v___x_425_ == 0)
{
lean_dec(v_snd_395_);
v___y_405_ = v___x_421_;
v___y_406_ = v___x_424_;
goto v___jp_404_;
}
else
{
uint8_t v___x_426_; 
v___x_426_ = lean_nat_dec_le(v___x_423_, v___x_423_);
if (v___x_426_ == 0)
{
if (v___x_425_ == 0)
{
lean_dec(v_snd_395_);
v___y_405_ = v___x_421_;
v___y_406_ = v___x_424_;
goto v___jp_404_;
}
else
{
size_t v___x_427_; size_t v___x_428_; lean_object* v___x_429_; 
v___x_427_ = ((size_t)0ULL);
v___x_428_ = lean_usize_of_nat(v___x_423_);
v___x_429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__1(v_linterOpts_381_, v_snd_395_, v___x_427_, v___x_428_, v___x_424_);
lean_dec(v_snd_395_);
v___y_405_ = v___x_421_;
v___y_406_ = v___x_429_;
goto v___jp_404_;
}
}
else
{
size_t v___x_430_; size_t v___x_431_; lean_object* v___x_432_; 
v___x_430_ = ((size_t)0ULL);
v___x_431_ = lean_usize_of_nat(v___x_423_);
v___x_432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__1(v_linterOpts_381_, v_snd_395_, v___x_430_, v___x_431_, v___x_424_);
lean_dec(v_snd_395_);
v___y_405_ = v___x_421_;
v___y_406_ = v___x_432_;
goto v___jp_404_;
}
}
}
}
}
}
}
}
v___jp_387_:
{
size_t v___x_389_; size_t v___x_390_; 
v___x_389_ = ((size_t)1ULL);
v___x_390_ = lean_usize_add(v_i_385_, v___x_389_);
v_i_385_ = v___x_390_;
v_b_386_ = v_a_388_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__2___boxed(lean_object* v_args_438_, lean_object* v_linterOpts_439_, lean_object* v_mod_440_, lean_object* v_as_441_, lean_object* v_sz_442_, lean_object* v_i_443_, lean_object* v_b_444_){
_start:
{
size_t v_sz_boxed_445_; size_t v_i_boxed_446_; lean_object* v_res_447_; 
v_sz_boxed_445_ = lean_unbox_usize(v_sz_442_);
lean_dec(v_sz_442_);
v_i_boxed_446_ = lean_unbox_usize(v_i_443_);
lean_dec(v_i_443_);
v_res_447_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__2(v_args_438_, v_linterOpts_439_, v_mod_440_, v_as_441_, v_sz_boxed_445_, v_i_boxed_446_, v_b_444_);
lean_dec_ref(v_as_441_);
lean_dec(v_mod_440_);
lean_dec_ref(v_linterOpts_439_);
lean_dec_ref(v_args_438_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality(lean_object* v_args_450_, lean_object* v_linterOpts_451_, lean_object* v_env_452_, lean_object* v_mod_453_, lean_object* v_collectedModules_454_){
_start:
{
lean_object* v_acc_455_; lean_object* v___x_456_; lean_object* v___x_457_; size_t v_sz_458_; size_t v___x_459_; lean_object* v___x_460_; lean_object* v_fst_461_; lean_object* v_snd_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
v_acc_455_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality___closed__0));
v___x_456_ = l_Lean_Linter_getAllCodeQualityEntries(v_env_452_);
v___x_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_457_, 0, v_collectedModules_454_);
lean_ctor_set(v___x_457_, 1, v_acc_455_);
v_sz_458_ = lean_array_size(v___x_456_);
v___x_459_ = ((size_t)0ULL);
v___x_460_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__2(v_args_450_, v_linterOpts_451_, v_mod_453_, v___x_456_, v_sz_458_, v___x_459_, v___x_457_);
lean_dec_ref(v___x_456_);
v_fst_461_ = lean_ctor_get(v___x_460_, 0);
v_snd_462_ = lean_ctor_get(v___x_460_, 1);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_469_ == 0)
{
v___x_464_ = v___x_460_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_snd_462_);
lean_inc(v_fst_461_);
lean_dec(v___x_460_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 1, v_fst_461_);
lean_ctor_set(v___x_464_, 0, v_snd_462_);
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_snd_462_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_fst_461_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality___boxed(lean_object* v_args_470_, lean_object* v_linterOpts_471_, lean_object* v_env_472_, lean_object* v_mod_473_, lean_object* v_collectedModules_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality(v_args_470_, v_linterOpts_471_, v_env_472_, v_mod_473_, v_collectedModules_474_);
lean_dec(v_mod_473_);
lean_dec_ref(v_env_472_);
lean_dec_ref(v_linterOpts_471_);
lean_dec_ref(v_args_470_);
return v_res_475_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(lean_object* v_modData_476_){
_start:
{
uint8_t v_isModule_478_; 
v_isModule_478_ = lean_ctor_get_uint8(v_modData_476_, sizeof(void*)*5);
return v_isModule_478_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule___boxed(lean_object* v_modData_479_, lean_object* v_a_480_){
_start:
{
uint8_t v_res_481_; lean_object* v_r_482_; 
v_res_481_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(v_modData_479_);
lean_dec_ref(v_modData_479_);
v_r_482_ = lean_box(v_res_481_);
return v_r_482_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_isIndentChar(uint32_t v_c_485_){
_start:
{
uint32_t v___x_486_; uint8_t v___x_487_; 
v___x_486_ = 32;
v___x_487_ = lean_uint32_dec_eq(v_c_485_, v___x_486_);
if (v___x_487_ == 0)
{
uint32_t v___x_488_; uint8_t v___x_489_; 
v___x_488_ = 9;
v___x_489_ = lean_uint32_dec_eq(v_c_485_, v___x_488_);
return v___x_489_;
}
else
{
return v___x_487_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_isIndentChar___boxed(lean_object* v_c_490_){
_start:
{
uint32_t v_c_boxed_491_; uint8_t v_res_492_; lean_object* v_r_493_; 
v_c_boxed_491_ = lean_unbox_uint32(v_c_490_);
lean_dec(v_c_490_);
v_res_492_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_isIndentChar(v_c_boxed_491_);
v_r_493_ = lean_box(v_res_492_);
return v_r_493_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace_spec__0(lean_object* v_s_494_, lean_object* v_stopPos_495_, lean_object* v_i_496_){
_start:
{
uint8_t v___y_498_; lean_object* v___x_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_501_ = lean_unsigned_to_nat(1u);
v___x_502_ = lean_nat_add(v_i_496_, v___x_501_);
v___x_503_ = lean_nat_dec_le(v___x_502_, v_stopPos_495_);
lean_dec(v___x_502_);
if (v___x_503_ == 0)
{
return v_i_496_;
}
else
{
if (v___x_503_ == 0)
{
v___y_498_ = v___x_503_;
goto v___jp_497_;
}
else
{
uint32_t v___x_504_; uint8_t v___x_505_; 
v___x_504_ = lean_string_utf8_get(v_s_494_, v_i_496_);
v___x_505_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_isIndentChar(v___x_504_);
v___y_498_ = v___x_505_;
goto v___jp_497_;
}
}
v___jp_497_:
{
if (v___y_498_ == 0)
{
return v_i_496_;
}
else
{
lean_object* v___x_499_; 
v___x_499_ = lean_string_utf8_next(v_s_494_, v_i_496_);
lean_dec(v_i_496_);
v_i_496_ = v___x_499_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace_spec__0___boxed(lean_object* v_s_506_, lean_object* v_stopPos_507_, lean_object* v_i_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Substring_Raw_takeWhileAux___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace_spec__0(v_s_506_, v_stopPos_507_, v_i_508_);
lean_dec(v_stopPos_507_);
lean_dec_ref(v_s_506_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace(lean_object* v_line_510_){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v_e_513_; lean_object* v___x_514_; 
v___x_511_ = lean_unsigned_to_nat(0u);
v___x_512_ = lean_string_utf8_byte_size(v_line_510_);
v_e_513_ = l_Substring_Raw_takeWhileAux___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace_spec__0(v_line_510_, v___x_512_, v___x_511_);
v___x_514_ = lean_string_utf8_extract(v_line_510_, v___x_511_, v_e_513_);
lean_dec(v_e_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace___boxed(lean_object* v_line_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace(v_line_515_);
lean_dec_ref(v_line_515_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg(){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg___closed__0));
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg___boxed(lean_object* v___dummy_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg();
return v_res_522_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0(void){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg();
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7(lean_object* v_s_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___boxed(lean_object* v_s_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7(v_s_526_);
lean_dec_ref(v_s_526_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(lean_object* v_x_528_, lean_object* v_x_529_){
_start:
{
if (lean_obj_tag(v_x_529_) == 0)
{
return v_x_528_;
}
else
{
lean_object* v_key_530_; lean_object* v_value_531_; lean_object* v_tail_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v_key_530_ = lean_ctor_get(v_x_529_, 0);
v_value_531_ = lean_ctor_get(v_x_529_, 1);
v_tail_532_ = lean_ctor_get(v_x_529_, 2);
lean_inc(v_value_531_);
lean_inc(v_key_530_);
v___x_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_533_, 0, v_key_530_);
lean_ctor_set(v___x_533_, 1, v_value_531_);
v___x_534_ = lean_array_push(v_x_528_, v___x_533_);
v_x_528_ = v___x_534_;
v_x_529_ = v_tail_532_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19___boxed(lean_object* v_x_536_, lean_object* v_x_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(v_x_536_, v_x_537_);
lean_dec(v_x_537_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(lean_object* v_as_539_, size_t v_i_540_, size_t v_stop_541_, lean_object* v_b_542_){
_start:
{
uint8_t v___x_543_; 
v___x_543_ = lean_usize_dec_eq(v_i_540_, v_stop_541_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; lean_object* v___x_545_; size_t v___x_546_; size_t v___x_547_; 
v___x_544_ = lean_array_uget_borrowed(v_as_539_, v_i_540_);
v___x_545_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(v_b_542_, v___x_544_);
v___x_546_ = ((size_t)1ULL);
v___x_547_ = lean_usize_add(v_i_540_, v___x_546_);
v_i_540_ = v___x_547_;
v_b_542_ = v___x_545_;
goto _start;
}
else
{
return v_b_542_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___boxed(lean_object* v_as_549_, lean_object* v_i_550_, lean_object* v_stop_551_, lean_object* v_b_552_){
_start:
{
size_t v_i_boxed_553_; size_t v_stop_boxed_554_; lean_object* v_res_555_; 
v_i_boxed_553_ = lean_unbox_usize(v_i_550_);
lean_dec(v_i_550_);
v_stop_boxed_554_ = lean_unbox_usize(v_stop_551_);
lean_dec(v_stop_551_);
v_res_555_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(v_as_549_, v_i_boxed_553_, v_stop_boxed_554_, v_b_552_);
lean_dec_ref(v_as_549_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(lean_object* v_s_556_){
_start:
{
lean_object* v___x_558_; lean_object* v_putStr_559_; lean_object* v___x_560_; 
v___x_558_ = lean_get_stderr();
v_putStr_559_ = lean_ctor_get(v___x_558_, 4);
lean_inc_ref(v_putStr_559_);
lean_dec_ref(v___x_558_);
v___x_560_ = lean_apply_2(v_putStr_559_, v_s_556_, lean_box(0));
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29___boxed(lean_object* v_s_561_, lean_object* v_a_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(v_s_561_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(lean_object* v_s_564_){
_start:
{
uint32_t v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_566_ = 10;
v___x_567_ = lean_string_push(v_s_564_, v___x_566_);
v___x_568_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(v___x_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17___boxed(lean_object* v_s_569_, lean_object* v_a_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v_s_569_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15(lean_object* v_x_572_, lean_object* v_x_573_){
_start:
{
if (lean_obj_tag(v_x_573_) == 0)
{
return v_x_572_;
}
else
{
lean_object* v_key_574_; lean_object* v_value_575_; lean_object* v_tail_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v_key_574_ = lean_ctor_get(v_x_573_, 0);
v_value_575_ = lean_ctor_get(v_x_573_, 1);
v_tail_576_ = lean_ctor_get(v_x_573_, 2);
lean_inc(v_value_575_);
lean_inc(v_key_574_);
v___x_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_577_, 0, v_key_574_);
lean_ctor_set(v___x_577_, 1, v_value_575_);
v___x_578_ = lean_array_push(v_x_572_, v___x_577_);
v_x_572_ = v___x_578_;
v_x_573_ = v_tail_576_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15___boxed(lean_object* v_x_580_, lean_object* v_x_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15(v_x_580_, v_x_581_);
lean_dec(v_x_581_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(lean_object* v_as_583_, size_t v_i_584_, size_t v_stop_585_, lean_object* v_b_586_){
_start:
{
uint8_t v___x_587_; 
v___x_587_ = lean_usize_dec_eq(v_i_584_, v_stop_585_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; lean_object* v___x_589_; size_t v___x_590_; size_t v___x_591_; 
v___x_588_ = lean_array_uget_borrowed(v_as_583_, v_i_584_);
v___x_589_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15(v_b_586_, v___x_588_);
v___x_590_ = ((size_t)1ULL);
v___x_591_ = lean_usize_add(v_i_584_, v___x_590_);
v_i_584_ = v___x_591_;
v_b_586_ = v___x_589_;
goto _start;
}
else
{
return v_b_586_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16___boxed(lean_object* v_as_593_, lean_object* v_i_594_, lean_object* v_stop_595_, lean_object* v_b_596_){
_start:
{
size_t v_i_boxed_597_; size_t v_stop_boxed_598_; lean_object* v_res_599_; 
v_i_boxed_597_ = lean_unbox_usize(v_i_594_);
lean_dec(v_i_594_);
v_stop_boxed_598_ = lean_unbox_usize(v_stop_595_);
lean_dec(v_stop_595_);
v_res_599_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(v_as_593_, v_i_boxed_597_, v_stop_boxed_598_, v_b_596_);
lean_dec_ref(v_as_593_);
return v_res_599_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(lean_object* v_a_600_, lean_object* v_b_601_){
_start:
{
lean_object* v_fst_602_; lean_object* v_fst_603_; uint8_t v___x_604_; 
v_fst_602_ = lean_ctor_get(v_b_601_, 0);
v_fst_603_ = lean_ctor_get(v_a_600_, 0);
v___x_604_ = lean_nat_dec_lt(v_fst_602_, v_fst_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0___boxed(lean_object* v_a_605_, lean_object* v_b_606_){
_start:
{
uint8_t v_res_607_; lean_object* v_r_608_; 
v_res_607_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v_a_605_, v_b_606_);
lean_dec_ref(v_b_606_);
lean_dec_ref(v_a_605_);
v_r_608_ = lean_box(v_res_607_);
return v_r_608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(lean_object* v_hi_609_, lean_object* v_pivot_610_, lean_object* v_as_611_, lean_object* v_i_612_, lean_object* v_k_613_){
_start:
{
uint8_t v___x_614_; 
v___x_614_ = lean_nat_dec_lt(v_k_613_, v_hi_609_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; lean_object* v___x_616_; 
lean_dec(v_k_613_);
v___x_615_ = lean_array_fswap(v_as_611_, v_i_612_, v_hi_609_);
v___x_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_616_, 0, v_i_612_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
return v___x_616_;
}
else
{
lean_object* v_fst_617_; lean_object* v___x_618_; lean_object* v_fst_619_; uint8_t v___x_620_; 
v_fst_617_ = lean_ctor_get(v_pivot_610_, 0);
v___x_618_ = lean_array_fget_borrowed(v_as_611_, v_k_613_);
v_fst_619_ = lean_ctor_get(v___x_618_, 0);
v___x_620_ = lean_nat_dec_lt(v_fst_617_, v_fst_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = lean_unsigned_to_nat(1u);
v___x_622_ = lean_nat_add(v_k_613_, v___x_621_);
lean_dec(v_k_613_);
v_k_613_ = v___x_622_;
goto _start;
}
else
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_624_ = lean_array_fswap(v_as_611_, v_i_612_, v_k_613_);
v___x_625_ = lean_unsigned_to_nat(1u);
v___x_626_ = lean_nat_add(v_i_612_, v___x_625_);
lean_dec(v_i_612_);
v___x_627_ = lean_nat_add(v_k_613_, v___x_625_);
lean_dec(v_k_613_);
v_as_611_ = v___x_624_;
v_i_612_ = v___x_626_;
v_k_613_ = v___x_627_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg___boxed(lean_object* v_hi_629_, lean_object* v_pivot_630_, lean_object* v_as_631_, lean_object* v_i_632_, lean_object* v_k_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(v_hi_629_, v_pivot_630_, v_as_631_, v_i_632_, v_k_633_);
lean_dec_ref(v_pivot_630_);
lean_dec(v_hi_629_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(lean_object* v_n_635_, lean_object* v_as_636_, lean_object* v_lo_637_, lean_object* v_hi_638_){
_start:
{
lean_object* v___y_640_; uint8_t v___x_650_; 
v___x_650_ = lean_nat_dec_lt(v_lo_637_, v_hi_638_);
if (v___x_650_ == 0)
{
lean_dec(v_lo_637_);
return v_as_636_;
}
else
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v_mid_653_; lean_object* v___y_655_; lean_object* v___y_661_; lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_651_ = lean_nat_add(v_lo_637_, v_hi_638_);
v___x_652_ = lean_unsigned_to_nat(1u);
v_mid_653_ = lean_nat_shiftr(v___x_651_, v___x_652_);
lean_dec(v___x_651_);
v___x_666_ = lean_array_fget_borrowed(v_as_636_, v_mid_653_);
v___x_667_ = lean_array_fget_borrowed(v_as_636_, v_lo_637_);
v___x_668_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v___x_666_, v___x_667_);
if (v___x_668_ == 0)
{
v___y_661_ = v_as_636_;
goto v___jp_660_;
}
else
{
lean_object* v___x_669_; 
v___x_669_ = lean_array_fswap(v_as_636_, v_lo_637_, v_mid_653_);
v___y_661_ = v___x_669_;
goto v___jp_660_;
}
v___jp_654_:
{
lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_656_ = lean_array_fget_borrowed(v___y_655_, v_mid_653_);
v___x_657_ = lean_array_fget_borrowed(v___y_655_, v_hi_638_);
v___x_658_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v___x_656_, v___x_657_);
if (v___x_658_ == 0)
{
lean_dec(v_mid_653_);
v___y_640_ = v___y_655_;
goto v___jp_639_;
}
else
{
lean_object* v___x_659_; 
v___x_659_ = lean_array_fswap(v___y_655_, v_mid_653_, v_hi_638_);
lean_dec(v_mid_653_);
v___y_640_ = v___x_659_;
goto v___jp_639_;
}
}
v___jp_660_:
{
lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_662_ = lean_array_fget_borrowed(v___y_661_, v_hi_638_);
v___x_663_ = lean_array_fget_borrowed(v___y_661_, v_lo_637_);
v___x_664_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v___x_662_, v___x_663_);
if (v___x_664_ == 0)
{
v___y_655_ = v___y_661_;
goto v___jp_654_;
}
else
{
lean_object* v___x_665_; 
v___x_665_ = lean_array_fswap(v___y_661_, v_lo_637_, v_hi_638_);
v___y_655_ = v___x_665_;
goto v___jp_654_;
}
}
}
v___jp_639_:
{
lean_object* v_pivot_641_; lean_object* v___x_642_; lean_object* v_fst_643_; lean_object* v_snd_644_; uint8_t v___x_645_; 
v_pivot_641_ = lean_array_fget(v___y_640_, v_hi_638_);
lean_inc_n(v_lo_637_, 2);
v___x_642_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(v_hi_638_, v_pivot_641_, v___y_640_, v_lo_637_, v_lo_637_);
lean_dec(v_pivot_641_);
v_fst_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_fst_643_);
v_snd_644_ = lean_ctor_get(v___x_642_, 1);
lean_inc(v_snd_644_);
lean_dec_ref(v___x_642_);
v___x_645_ = lean_nat_dec_le(v_hi_638_, v_fst_643_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_646_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v_n_635_, v_snd_644_, v_lo_637_, v_fst_643_);
v___x_647_ = lean_unsigned_to_nat(1u);
v___x_648_ = lean_nat_add(v_fst_643_, v___x_647_);
lean_dec(v_fst_643_);
v_as_636_ = v___x_646_;
v_lo_637_ = v___x_648_;
goto _start;
}
else
{
lean_dec(v_fst_643_);
lean_dec(v_lo_637_);
return v_snd_644_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___boxed(lean_object* v_n_670_, lean_object* v_as_671_, lean_object* v_lo_672_, lean_object* v_hi_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v_n_670_, v_as_671_, v_lo_672_, v_hi_673_);
lean_dec(v_hi_673_);
lean_dec(v_n_670_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(lean_object* v_a_675_, lean_object* v___x_676_, lean_object* v___x_677_, lean_object* v_a_678_, lean_object* v_b_679_){
_start:
{
lean_object* v_it_681_; lean_object* v_startInclusive_682_; lean_object* v_endExclusive_683_; 
if (lean_obj_tag(v_a_678_) == 0)
{
lean_object* v_currPos_687_; lean_object* v_searcher_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_711_; 
v_currPos_687_ = lean_ctor_get(v_a_678_, 0);
v_searcher_688_ = lean_ctor_get(v_a_678_, 1);
v_isSharedCheck_711_ = !lean_is_exclusive(v_a_678_);
if (v_isSharedCheck_711_ == 0)
{
v___x_690_ = v_a_678_;
v_isShared_691_ = v_isSharedCheck_711_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_searcher_688_);
lean_inc(v_currPos_687_);
lean_dec(v_a_678_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_711_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
uint8_t v_decide_692_; 
v_decide_692_ = lean_nat_dec_eq(v_searcher_688_, v___x_677_);
if (v_decide_692_ == 0)
{
uint32_t v___x_693_; uint32_t v___x_694_; uint8_t v___x_695_; 
v___x_693_ = 10;
v___x_694_ = lean_string_utf8_get_fast(v_a_675_, v_searcher_688_);
v___x_695_ = lean_uint32_dec_eq(v___x_694_, v___x_693_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; lean_object* v___x_698_; 
v___x_696_ = lean_string_utf8_next_fast(v_a_675_, v_searcher_688_);
lean_dec(v_searcher_688_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 1, v___x_696_);
v___x_698_ = v___x_690_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_currPos_687_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v___x_696_);
v___x_698_ = v_reuseFailAlloc_700_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
v_a_678_ = v___x_698_;
goto _start;
}
}
else
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v_slice_704_; lean_object* v_nextIt_706_; 
v___x_701_ = lean_string_utf8_next_fast(v_a_675_, v_searcher_688_);
v___x_702_ = lean_nat_sub(v___x_701_, v_searcher_688_);
v___x_703_ = lean_nat_add(v_searcher_688_, v___x_702_);
lean_dec(v___x_702_);
v_slice_704_ = l_String_Slice_subslice_x21(v___x_676_, v_currPos_687_, v_searcher_688_);
lean_inc(v___x_703_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 1, v___x_703_);
lean_ctor_set(v___x_690_, 0, v___x_703_);
v_nextIt_706_ = v___x_690_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_703_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v___x_703_);
v_nextIt_706_ = v_reuseFailAlloc_709_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v_startInclusive_707_; lean_object* v_endExclusive_708_; 
v_startInclusive_707_ = lean_ctor_get(v_slice_704_, 0);
lean_inc(v_startInclusive_707_);
v_endExclusive_708_ = lean_ctor_get(v_slice_704_, 1);
lean_inc(v_endExclusive_708_);
lean_dec_ref(v_slice_704_);
v_it_681_ = v_nextIt_706_;
v_startInclusive_682_ = v_startInclusive_707_;
v_endExclusive_683_ = v_endExclusive_708_;
goto v___jp_680_;
}
}
}
else
{
lean_object* v___x_710_; 
lean_del_object(v___x_690_);
lean_dec(v_searcher_688_);
v___x_710_ = lean_box(1);
lean_inc(v___x_677_);
v_it_681_ = v___x_710_;
v_startInclusive_682_ = v_currPos_687_;
v_endExclusive_683_ = v___x_677_;
goto v___jp_680_;
}
}
}
else
{
lean_dec(v___x_677_);
lean_dec_ref(v_a_675_);
return v_b_679_;
}
v___jp_680_:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
lean_inc_ref(v_a_675_);
v___x_684_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_684_, 0, v_a_675_);
lean_ctor_set(v___x_684_, 1, v_startInclusive_682_);
lean_ctor_set(v___x_684_, 2, v_endExclusive_683_);
v___x_685_ = lean_array_push(v_b_679_, v___x_684_);
v_a_678_ = v_it_681_;
v_b_679_ = v___x_685_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg___boxed(lean_object* v_a_712_, lean_object* v___x_713_, lean_object* v___x_714_, lean_object* v_a_715_, lean_object* v_b_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(v_a_712_, v___x_713_, v___x_714_, v_a_715_, v_b_716_);
lean_dec_ref(v___x_713_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9(size_t v_sz_718_, size_t v_i_719_, lean_object* v_bs_720_){
_start:
{
uint8_t v___x_721_; 
v___x_721_ = lean_usize_dec_lt(v_i_719_, v_sz_718_);
if (v___x_721_ == 0)
{
return v_bs_720_;
}
else
{
lean_object* v_v_722_; lean_object* v___x_723_; lean_object* v_bs_x27_724_; lean_object* v___x_725_; size_t v___x_726_; size_t v___x_727_; lean_object* v___x_728_; 
v_v_722_ = lean_array_uget(v_bs_720_, v_i_719_);
v___x_723_ = lean_unsigned_to_nat(0u);
v_bs_x27_724_ = lean_array_uset(v_bs_720_, v_i_719_, v___x_723_);
v___x_725_ = l_String_Slice_toString(v_v_722_);
lean_dec(v_v_722_);
v___x_726_ = ((size_t)1ULL);
v___x_727_ = lean_usize_add(v_i_719_, v___x_726_);
v___x_728_ = lean_array_uset(v_bs_x27_724_, v_i_719_, v___x_725_);
v_i_719_ = v___x_727_;
v_bs_720_ = v___x_728_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9___boxed(lean_object* v_sz_730_, lean_object* v_i_731_, lean_object* v_bs_732_){
_start:
{
size_t v_sz_boxed_733_; size_t v_i_boxed_734_; lean_object* v_res_735_; 
v_sz_boxed_733_ = lean_unbox_usize(v_sz_730_);
lean_dec(v_sz_730_);
v_i_boxed_734_ = lean_unbox_usize(v_i_731_);
lean_dec(v_i_731_);
v_res_735_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9(v_sz_boxed_733_, v_i_boxed_734_, v_bs_732_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33___redArg(lean_object* v_x_736_, lean_object* v_x_737_){
_start:
{
if (lean_obj_tag(v_x_737_) == 0)
{
return v_x_736_;
}
else
{
lean_object* v_key_738_; lean_object* v_value_739_; lean_object* v_tail_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_763_; 
v_key_738_ = lean_ctor_get(v_x_737_, 0);
v_value_739_ = lean_ctor_get(v_x_737_, 1);
v_tail_740_ = lean_ctor_get(v_x_737_, 2);
v_isSharedCheck_763_ = !lean_is_exclusive(v_x_737_);
if (v_isSharedCheck_763_ == 0)
{
v___x_742_ = v_x_737_;
v_isShared_743_ = v_isSharedCheck_763_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_tail_740_);
lean_inc(v_value_739_);
lean_inc(v_key_738_);
lean_dec(v_x_737_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_763_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_744_; uint64_t v___x_745_; uint64_t v___x_746_; uint64_t v___x_747_; uint64_t v_fold_748_; uint64_t v___x_749_; uint64_t v___x_750_; uint64_t v___x_751_; size_t v___x_752_; size_t v___x_753_; size_t v___x_754_; size_t v___x_755_; size_t v___x_756_; lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_744_ = lean_array_get_size(v_x_736_);
v___x_745_ = lean_uint64_of_nat(v_key_738_);
v___x_746_ = 32ULL;
v___x_747_ = lean_uint64_shift_right(v___x_745_, v___x_746_);
v_fold_748_ = lean_uint64_xor(v___x_745_, v___x_747_);
v___x_749_ = 16ULL;
v___x_750_ = lean_uint64_shift_right(v_fold_748_, v___x_749_);
v___x_751_ = lean_uint64_xor(v_fold_748_, v___x_750_);
v___x_752_ = lean_uint64_to_usize(v___x_751_);
v___x_753_ = lean_usize_of_nat(v___x_744_);
v___x_754_ = ((size_t)1ULL);
v___x_755_ = lean_usize_sub(v___x_753_, v___x_754_);
v___x_756_ = lean_usize_land(v___x_752_, v___x_755_);
v___x_757_ = lean_array_uget_borrowed(v_x_736_, v___x_756_);
lean_inc(v___x_757_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 2, v___x_757_);
v___x_759_ = v___x_742_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_key_738_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_value_739_);
lean_ctor_set(v_reuseFailAlloc_762_, 2, v___x_757_);
v___x_759_ = v_reuseFailAlloc_762_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_760_; 
v___x_760_ = lean_array_uset(v_x_736_, v___x_756_, v___x_759_);
v_x_736_ = v___x_760_;
v_x_737_ = v_tail_740_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15___redArg(lean_object* v_i_764_, lean_object* v_source_765_, lean_object* v_target_766_){
_start:
{
lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_767_ = lean_array_get_size(v_source_765_);
v___x_768_ = lean_nat_dec_lt(v_i_764_, v___x_767_);
if (v___x_768_ == 0)
{
lean_dec_ref(v_source_765_);
lean_dec(v_i_764_);
return v_target_766_;
}
else
{
lean_object* v_es_769_; lean_object* v___x_770_; lean_object* v_source_771_; lean_object* v_target_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v_es_769_ = lean_array_fget(v_source_765_, v_i_764_);
v___x_770_ = lean_box(0);
v_source_771_ = lean_array_fset(v_source_765_, v_i_764_, v___x_770_);
v_target_772_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33___redArg(v_target_766_, v_es_769_);
v___x_773_ = lean_unsigned_to_nat(1u);
v___x_774_ = lean_nat_add(v_i_764_, v___x_773_);
lean_dec(v_i_764_);
v_i_764_ = v___x_774_;
v_source_765_ = v_source_771_;
v_target_766_ = v_target_772_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12___redArg(lean_object* v_data_776_){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v_nbuckets_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_777_ = lean_array_get_size(v_data_776_);
v___x_778_ = lean_unsigned_to_nat(2u);
v_nbuckets_779_ = lean_nat_mul(v___x_777_, v___x_778_);
v___x_780_ = lean_unsigned_to_nat(0u);
v___x_781_ = lean_box(0);
v___x_782_ = lean_mk_array(v_nbuckets_779_, v___x_781_);
v___x_783_ = lean_array_propagate_mark(v_data_776_, v___x_782_);
v___x_784_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15___redArg(v___x_780_, v_data_776_, v___x_783_);
return v___x_784_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(lean_object* v_a_785_, lean_object* v_x_786_){
_start:
{
if (lean_obj_tag(v_x_786_) == 0)
{
uint8_t v___x_787_; 
v___x_787_ = 0;
return v___x_787_;
}
else
{
lean_object* v_key_788_; lean_object* v_tail_789_; uint8_t v___x_790_; 
v_key_788_ = lean_ctor_get(v_x_786_, 0);
v_tail_789_ = lean_ctor_get(v_x_786_, 2);
v___x_790_ = lean_nat_dec_eq(v_key_788_, v_a_785_);
if (v___x_790_ == 0)
{
v_x_786_ = v_tail_789_;
goto _start;
}
else
{
return v___x_790_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg___boxed(lean_object* v_a_792_, lean_object* v_x_793_){
_start:
{
uint8_t v_res_794_; lean_object* v_r_795_; 
v_res_794_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(v_a_792_, v_x_793_);
lean_dec(v_x_793_);
lean_dec(v_a_792_);
v_r_795_ = lean_box(v_res_794_);
return v_r_795_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(lean_object* v_a_796_, lean_object* v_b_797_, lean_object* v_x_798_){
_start:
{
if (lean_obj_tag(v_x_798_) == 0)
{
lean_dec(v_b_797_);
lean_dec(v_a_796_);
return v_x_798_;
}
else
{
lean_object* v_key_799_; lean_object* v_value_800_; lean_object* v_tail_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_813_; 
v_key_799_ = lean_ctor_get(v_x_798_, 0);
v_value_800_ = lean_ctor_get(v_x_798_, 1);
v_tail_801_ = lean_ctor_get(v_x_798_, 2);
v_isSharedCheck_813_ = !lean_is_exclusive(v_x_798_);
if (v_isSharedCheck_813_ == 0)
{
v___x_803_ = v_x_798_;
v_isShared_804_ = v_isSharedCheck_813_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_tail_801_);
lean_inc(v_value_800_);
lean_inc(v_key_799_);
lean_dec(v_x_798_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_813_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
uint8_t v___x_805_; 
v___x_805_ = lean_nat_dec_eq(v_key_799_, v_a_796_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; lean_object* v___x_808_; 
v___x_806_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(v_a_796_, v_b_797_, v_tail_801_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 2, v___x_806_);
v___x_808_ = v___x_803_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_key_799_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v_value_800_);
lean_ctor_set(v_reuseFailAlloc_809_, 2, v___x_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
else
{
lean_object* v___x_811_; 
lean_dec(v_value_800_);
lean_dec(v_key_799_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 1, v_b_797_);
lean_ctor_set(v___x_803_, 0, v_a_796_);
v___x_811_ = v___x_803_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_796_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_b_797_);
lean_ctor_set(v_reuseFailAlloc_812_, 2, v_tail_801_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(lean_object* v_m_814_, lean_object* v_a_815_, lean_object* v_b_816_){
_start:
{
lean_object* v_size_817_; lean_object* v_buckets_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_861_; 
v_size_817_ = lean_ctor_get(v_m_814_, 0);
v_buckets_818_ = lean_ctor_get(v_m_814_, 1);
v_isSharedCheck_861_ = !lean_is_exclusive(v_m_814_);
if (v_isSharedCheck_861_ == 0)
{
v___x_820_ = v_m_814_;
v_isShared_821_ = v_isSharedCheck_861_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_buckets_818_);
lean_inc(v_size_817_);
lean_dec(v_m_814_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_861_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_822_; uint64_t v___x_823_; uint64_t v___x_824_; uint64_t v___x_825_; uint64_t v_fold_826_; uint64_t v___x_827_; uint64_t v___x_828_; uint64_t v___x_829_; size_t v___x_830_; size_t v___x_831_; size_t v___x_832_; size_t v___x_833_; size_t v___x_834_; lean_object* v_bkt_835_; uint8_t v___x_836_; 
v___x_822_ = lean_array_get_size(v_buckets_818_);
v___x_823_ = lean_uint64_of_nat(v_a_815_);
v___x_824_ = 32ULL;
v___x_825_ = lean_uint64_shift_right(v___x_823_, v___x_824_);
v_fold_826_ = lean_uint64_xor(v___x_823_, v___x_825_);
v___x_827_ = 16ULL;
v___x_828_ = lean_uint64_shift_right(v_fold_826_, v___x_827_);
v___x_829_ = lean_uint64_xor(v_fold_826_, v___x_828_);
v___x_830_ = lean_uint64_to_usize(v___x_829_);
v___x_831_ = lean_usize_of_nat(v___x_822_);
v___x_832_ = ((size_t)1ULL);
v___x_833_ = lean_usize_sub(v___x_831_, v___x_832_);
v___x_834_ = lean_usize_land(v___x_830_, v___x_833_);
v_bkt_835_ = lean_array_uget_borrowed(v_buckets_818_, v___x_834_);
v___x_836_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(v_a_815_, v_bkt_835_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; lean_object* v_size_x27_838_; lean_object* v___x_839_; lean_object* v_buckets_x27_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_837_ = lean_unsigned_to_nat(1u);
v_size_x27_838_ = lean_nat_add(v_size_817_, v___x_837_);
lean_dec(v_size_817_);
lean_inc(v_bkt_835_);
v___x_839_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_839_, 0, v_a_815_);
lean_ctor_set(v___x_839_, 1, v_b_816_);
lean_ctor_set(v___x_839_, 2, v_bkt_835_);
v_buckets_x27_840_ = lean_array_uset(v_buckets_818_, v___x_834_, v___x_839_);
v___x_841_ = lean_unsigned_to_nat(4u);
v___x_842_ = lean_nat_mul(v_size_x27_838_, v___x_841_);
v___x_843_ = lean_unsigned_to_nat(3u);
v___x_844_ = lean_nat_div(v___x_842_, v___x_843_);
lean_dec(v___x_842_);
v___x_845_ = lean_array_get_size(v_buckets_x27_840_);
v___x_846_ = lean_nat_dec_le(v___x_844_, v___x_845_);
lean_dec(v___x_844_);
if (v___x_846_ == 0)
{
lean_object* v_val_847_; lean_object* v___x_849_; 
v_val_847_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12___redArg(v_buckets_x27_840_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 1, v_val_847_);
lean_ctor_set(v___x_820_, 0, v_size_x27_838_);
v___x_849_ = v___x_820_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_size_x27_838_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_val_847_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
else
{
lean_object* v___x_852_; 
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 1, v_buckets_x27_840_);
lean_ctor_set(v___x_820_, 0, v_size_x27_838_);
v___x_852_ = v___x_820_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_size_x27_838_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v_buckets_x27_840_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
else
{
lean_object* v___x_854_; lean_object* v_buckets_x27_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_859_; 
lean_inc(v_bkt_835_);
v___x_854_ = lean_box(0);
v_buckets_x27_855_ = lean_array_uset(v_buckets_818_, v___x_834_, v___x_854_);
v___x_856_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(v_a_815_, v_b_816_, v_bkt_835_);
v___x_857_ = lean_array_uset(v_buckets_x27_855_, v___x_834_, v___x_856_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 1, v___x_857_);
v___x_859_ = v___x_820_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_size_817_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v___x_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9(lean_object* v_a_862_, lean_object* v_as_863_, size_t v_i_864_, size_t v_stop_865_){
_start:
{
uint8_t v___x_866_; 
v___x_866_ = lean_usize_dec_eq(v_i_864_, v_stop_865_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; uint8_t v___x_868_; 
v___x_867_ = lean_array_uget_borrowed(v_as_863_, v_i_864_);
v___x_868_ = lean_name_eq(v_a_862_, v___x_867_);
if (v___x_868_ == 0)
{
size_t v___x_869_; size_t v___x_870_; 
v___x_869_ = ((size_t)1ULL);
v___x_870_ = lean_usize_add(v_i_864_, v___x_869_);
v_i_864_ = v___x_870_;
goto _start;
}
else
{
return v___x_868_;
}
}
else
{
uint8_t v___x_872_; 
v___x_872_ = 0;
return v___x_872_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9___boxed(lean_object* v_a_873_, lean_object* v_as_874_, lean_object* v_i_875_, lean_object* v_stop_876_){
_start:
{
size_t v_i_boxed_877_; size_t v_stop_boxed_878_; uint8_t v_res_879_; lean_object* v_r_880_; 
v_i_boxed_877_ = lean_unbox_usize(v_i_875_);
lean_dec(v_i_875_);
v_stop_boxed_878_ = lean_unbox_usize(v_stop_876_);
lean_dec(v_stop_876_);
v_res_879_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9(v_a_873_, v_as_874_, v_i_boxed_877_, v_stop_boxed_878_);
lean_dec_ref(v_as_874_);
lean_dec(v_a_873_);
v_r_880_ = lean_box(v_res_879_);
return v_r_880_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(lean_object* v_as_881_, lean_object* v_a_882_){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; uint8_t v___x_885_; 
v___x_883_ = lean_unsigned_to_nat(0u);
v___x_884_ = lean_array_get_size(v_as_881_);
v___x_885_ = lean_nat_dec_lt(v___x_883_, v___x_884_);
if (v___x_885_ == 0)
{
return v___x_885_;
}
else
{
if (v___x_885_ == 0)
{
return v___x_885_;
}
else
{
size_t v___x_886_; size_t v___x_887_; uint8_t v___x_888_; 
v___x_886_ = ((size_t)0ULL);
v___x_887_ = lean_usize_of_nat(v___x_884_);
v___x_888_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9(v_a_882_, v_as_881_, v___x_886_, v___x_887_);
return v___x_888_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4___boxed(lean_object* v_as_889_, lean_object* v_a_890_){
_start:
{
uint8_t v_res_891_; lean_object* v_r_892_; 
v_res_891_ = l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(v_as_889_, v_a_890_);
lean_dec(v_a_890_);
lean_dec_ref(v_as_889_);
v_r_892_ = lean_box(v_res_891_);
return v_r_892_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(lean_object* v_a_893_, lean_object* v_fallback_894_, lean_object* v_x_895_){
_start:
{
if (lean_obj_tag(v_x_895_) == 0)
{
lean_inc(v_fallback_894_);
return v_fallback_894_;
}
else
{
lean_object* v_key_896_; lean_object* v_value_897_; lean_object* v_tail_898_; uint8_t v___x_899_; 
v_key_896_ = lean_ctor_get(v_x_895_, 0);
v_value_897_ = lean_ctor_get(v_x_895_, 1);
v_tail_898_ = lean_ctor_get(v_x_895_, 2);
v___x_899_ = lean_nat_dec_eq(v_key_896_, v_a_893_);
if (v___x_899_ == 0)
{
v_x_895_ = v_tail_898_;
goto _start;
}
else
{
lean_inc(v_value_897_);
return v_value_897_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg___boxed(lean_object* v_a_901_, lean_object* v_fallback_902_, lean_object* v_x_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(v_a_901_, v_fallback_902_, v_x_903_);
lean_dec(v_x_903_);
lean_dec(v_fallback_902_);
lean_dec(v_a_901_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(lean_object* v_m_905_, lean_object* v_a_906_, lean_object* v_fallback_907_){
_start:
{
lean_object* v_buckets_908_; lean_object* v___x_909_; uint64_t v___x_910_; uint64_t v___x_911_; uint64_t v___x_912_; uint64_t v_fold_913_; uint64_t v___x_914_; uint64_t v___x_915_; uint64_t v___x_916_; size_t v___x_917_; size_t v___x_918_; size_t v___x_919_; size_t v___x_920_; size_t v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v_buckets_908_ = lean_ctor_get(v_m_905_, 1);
v___x_909_ = lean_array_get_size(v_buckets_908_);
v___x_910_ = lean_uint64_of_nat(v_a_906_);
v___x_911_ = 32ULL;
v___x_912_ = lean_uint64_shift_right(v___x_910_, v___x_911_);
v_fold_913_ = lean_uint64_xor(v___x_910_, v___x_912_);
v___x_914_ = 16ULL;
v___x_915_ = lean_uint64_shift_right(v_fold_913_, v___x_914_);
v___x_916_ = lean_uint64_xor(v_fold_913_, v___x_915_);
v___x_917_ = lean_uint64_to_usize(v___x_916_);
v___x_918_ = lean_usize_of_nat(v___x_909_);
v___x_919_ = ((size_t)1ULL);
v___x_920_ = lean_usize_sub(v___x_918_, v___x_919_);
v___x_921_ = lean_usize_land(v___x_917_, v___x_920_);
v___x_922_ = lean_array_uget_borrowed(v_buckets_908_, v___x_921_);
v___x_923_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(v_a_906_, v_fallback_907_, v___x_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg___boxed(lean_object* v_m_924_, lean_object* v_a_925_, lean_object* v_fallback_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(v_m_924_, v_a_925_, v_fallback_926_);
lean_dec(v_fallback_926_);
lean_dec(v_a_925_);
lean_dec_ref(v_m_924_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(lean_object* v_as_930_, size_t v_sz_931_, size_t v_i_932_, lean_object* v_b_933_){
_start:
{
lean_object* v_a_936_; uint8_t v___x_940_; 
v___x_940_ = lean_usize_dec_lt(v_i_932_, v_sz_931_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; 
v___x_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_941_, 0, v_b_933_);
return v___x_941_;
}
else
{
lean_object* v_a_942_; lean_object* v_fst_943_; lean_object* v_snd_944_; lean_object* v___x_945_; lean_object* v___x_946_; uint8_t v___x_947_; 
v_a_942_ = lean_array_uget_borrowed(v_as_930_, v_i_932_);
v_fst_943_ = lean_ctor_get(v_a_942_, 0);
v_snd_944_ = lean_ctor_get(v_a_942_, 1);
v___x_945_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___closed__0));
v___x_946_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(v_b_933_, v_fst_943_, v___x_945_);
v___x_947_ = l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(v___x_946_, v_snd_944_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; lean_object* v___x_949_; 
lean_inc(v_snd_944_);
v___x_948_ = lean_array_push(v___x_946_, v_snd_944_);
lean_inc(v_fst_943_);
v___x_949_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(v_b_933_, v_fst_943_, v___x_948_);
v_a_936_ = v___x_949_;
goto v___jp_935_;
}
else
{
lean_dec(v___x_946_);
v_a_936_ = v_b_933_;
goto v___jp_935_;
}
}
v___jp_935_:
{
size_t v___x_937_; size_t v___x_938_; 
v___x_937_ = ((size_t)1ULL);
v___x_938_ = lean_usize_add(v_i_932_, v___x_937_);
v_i_932_ = v___x_938_;
v_b_933_ = v_a_936_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___boxed(lean_object* v_as_950_, lean_object* v_sz_951_, lean_object* v_i_952_, lean_object* v_b_953_, lean_object* v___y_954_){
_start:
{
size_t v_sz_boxed_955_; size_t v_i_boxed_956_; lean_object* v_res_957_; 
v_sz_boxed_955_ = lean_unbox_usize(v_sz_951_);
lean_dec(v_sz_951_);
v_i_boxed_956_ = lean_unbox_usize(v_i_952_);
lean_dec(v_i_952_);
v_res_957_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(v_as_950_, v_sz_boxed_955_, v_i_boxed_956_, v_b_953_);
lean_dec_ref(v_as_950_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(lean_object* v_s_958_){
_start:
{
lean_object* v___x_960_; lean_object* v_putStr_961_; lean_object* v___x_962_; 
v___x_960_ = lean_get_stdout();
v_putStr_961_ = lean_ctor_get(v___x_960_, 4);
lean_inc_ref(v_putStr_961_);
lean_dec_ref(v___x_960_);
v___x_962_ = lean_apply_2(v_putStr_961_, v_s_958_, lean_box(0));
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23___boxed(lean_object* v_s_963_, lean_object* v_a_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v_s_963_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(lean_object* v_s_966_){
_start:
{
uint32_t v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_968_ = 10;
v___x_969_ = lean_string_push(v_s_966_, v___x_968_);
v___x_970_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13___boxed(lean_object* v_s_971_, lean_object* v_a_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v_s_971_);
return v_res_973_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(uint8_t v___x_974_, lean_object* v_a_975_, lean_object* v_b_976_){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; uint8_t v___x_979_; 
v___x_977_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_975_, v___x_974_);
v___x_978_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_b_976_, v___x_974_);
v___x_979_ = lean_string_dec_lt(v___x_977_, v___x_978_);
lean_dec_ref(v___x_978_);
lean_dec_ref(v___x_977_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0___boxed(lean_object* v___x_980_, lean_object* v_a_981_, lean_object* v_b_982_){
_start:
{
uint8_t v___x_11544__boxed_983_; uint8_t v_res_984_; lean_object* v_r_985_; 
v___x_11544__boxed_983_ = lean_unbox(v___x_980_);
v_res_984_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_11544__boxed_983_, v_a_981_, v_b_982_);
v_r_985_ = lean_box(v_res_984_);
return v_r_985_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(lean_object* v___x_986_, lean_object* v___x_987_, lean_object* v_hi_988_, lean_object* v_pivot_989_, lean_object* v_as_990_, lean_object* v_i_991_, lean_object* v_k_992_){
_start:
{
uint8_t v___x_993_; 
v___x_993_ = lean_nat_dec_lt(v_k_992_, v_hi_988_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; lean_object* v___x_995_; 
lean_dec(v_k_992_);
lean_dec(v_pivot_989_);
v___x_994_ = lean_array_fswap(v_as_990_, v_i_991_, v_hi_988_);
v___x_995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_995_, 0, v_i_991_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
return v___x_995_;
}
else
{
uint8_t v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; uint8_t v___x_1000_; 
v___x_996_ = lean_nat_dec_lt(v___x_986_, v___x_987_);
v___x_997_ = lean_array_fget_borrowed(v_as_990_, v_k_992_);
lean_inc(v___x_997_);
v___x_998_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_997_, v___x_996_);
lean_inc(v_pivot_989_);
v___x_999_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pivot_989_, v___x_996_);
v___x_1000_ = lean_string_dec_lt(v___x_998_, v___x_999_);
lean_dec_ref(v___x_999_);
lean_dec_ref(v___x_998_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = lean_unsigned_to_nat(1u);
v___x_1002_ = lean_nat_add(v_k_992_, v___x_1001_);
lean_dec(v_k_992_);
v_k_992_ = v___x_1002_;
goto _start;
}
else
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1004_ = lean_array_fswap(v_as_990_, v_i_991_, v_k_992_);
v___x_1005_ = lean_unsigned_to_nat(1u);
v___x_1006_ = lean_nat_add(v_i_991_, v___x_1005_);
lean_dec(v_i_991_);
v___x_1007_ = lean_nat_add(v_k_992_, v___x_1005_);
lean_dec(v_k_992_);
v_as_990_ = v___x_1004_;
v_i_991_ = v___x_1006_;
v_k_992_ = v___x_1007_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg___boxed(lean_object* v___x_1009_, lean_object* v___x_1010_, lean_object* v_hi_1011_, lean_object* v_pivot_1012_, lean_object* v_as_1013_, lean_object* v_i_1014_, lean_object* v_k_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(v___x_1009_, v___x_1010_, v_hi_1011_, v_pivot_1012_, v_as_1013_, v_i_1014_, v_k_1015_);
lean_dec(v_hi_1011_);
lean_dec(v___x_1010_);
lean_dec(v___x_1009_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(lean_object* v___x_1017_, lean_object* v___x_1018_, lean_object* v_n_1019_, lean_object* v_as_1020_, lean_object* v_lo_1021_, lean_object* v_hi_1022_){
_start:
{
lean_object* v___y_1024_; uint8_t v___x_1034_; 
v___x_1034_ = lean_nat_dec_lt(v_lo_1021_, v_hi_1022_);
if (v___x_1034_ == 0)
{
lean_dec(v_lo_1021_);
return v_as_1020_;
}
else
{
uint8_t v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v_mid_1038_; lean_object* v___y_1040_; lean_object* v___y_1046_; lean_object* v___x_1051_; lean_object* v___x_1052_; uint8_t v___x_1053_; 
v___x_1035_ = lean_nat_dec_lt(v___x_1017_, v___x_1018_);
v___x_1036_ = lean_nat_add(v_lo_1021_, v_hi_1022_);
v___x_1037_ = lean_unsigned_to_nat(1u);
v_mid_1038_ = lean_nat_shiftr(v___x_1036_, v___x_1037_);
lean_dec(v___x_1036_);
v___x_1051_ = lean_array_fget_borrowed(v_as_1020_, v_mid_1038_);
v___x_1052_ = lean_array_fget_borrowed(v_as_1020_, v_lo_1021_);
lean_inc(v___x_1052_);
lean_inc(v___x_1051_);
v___x_1053_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_1035_, v___x_1051_, v___x_1052_);
if (v___x_1053_ == 0)
{
v___y_1046_ = v_as_1020_;
goto v___jp_1045_;
}
else
{
lean_object* v___x_1054_; 
v___x_1054_ = lean_array_fswap(v_as_1020_, v_lo_1021_, v_mid_1038_);
v___y_1046_ = v___x_1054_;
goto v___jp_1045_;
}
v___jp_1039_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; uint8_t v___x_1043_; 
v___x_1041_ = lean_array_fget_borrowed(v___y_1040_, v_mid_1038_);
v___x_1042_ = lean_array_fget_borrowed(v___y_1040_, v_hi_1022_);
lean_inc(v___x_1042_);
lean_inc(v___x_1041_);
v___x_1043_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_1035_, v___x_1041_, v___x_1042_);
if (v___x_1043_ == 0)
{
lean_dec(v_mid_1038_);
v___y_1024_ = v___y_1040_;
goto v___jp_1023_;
}
else
{
lean_object* v___x_1044_; 
v___x_1044_ = lean_array_fswap(v___y_1040_, v_mid_1038_, v_hi_1022_);
lean_dec(v_mid_1038_);
v___y_1024_ = v___x_1044_;
goto v___jp_1023_;
}
}
v___jp_1045_:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
v___x_1047_ = lean_array_fget_borrowed(v___y_1046_, v_hi_1022_);
v___x_1048_ = lean_array_fget_borrowed(v___y_1046_, v_lo_1021_);
lean_inc(v___x_1048_);
lean_inc(v___x_1047_);
v___x_1049_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_1035_, v___x_1047_, v___x_1048_);
if (v___x_1049_ == 0)
{
v___y_1040_ = v___y_1046_;
goto v___jp_1039_;
}
else
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_array_fswap(v___y_1046_, v_lo_1021_, v_hi_1022_);
v___y_1040_ = v___x_1050_;
goto v___jp_1039_;
}
}
}
v___jp_1023_:
{
lean_object* v_pivot_1025_; lean_object* v___x_1026_; lean_object* v_fst_1027_; lean_object* v_snd_1028_; uint8_t v___x_1029_; 
v_pivot_1025_ = lean_array_fget(v___y_1024_, v_hi_1022_);
lean_inc_n(v_lo_1021_, 2);
v___x_1026_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(v___x_1017_, v___x_1018_, v_hi_1022_, v_pivot_1025_, v___y_1024_, v_lo_1021_, v_lo_1021_);
v_fst_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_fst_1027_);
v_snd_1028_ = lean_ctor_get(v___x_1026_, 1);
lean_inc(v_snd_1028_);
lean_dec_ref(v___x_1026_);
v___x_1029_ = lean_nat_dec_le(v_hi_1022_, v_fst_1027_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1030_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v___x_1017_, v___x_1018_, v_n_1019_, v_snd_1028_, v_lo_1021_, v_fst_1027_);
v___x_1031_ = lean_unsigned_to_nat(1u);
v___x_1032_ = lean_nat_add(v_fst_1027_, v___x_1031_);
lean_dec(v_fst_1027_);
v_as_1020_ = v___x_1030_;
v_lo_1021_ = v___x_1032_;
goto _start;
}
else
{
lean_dec(v_fst_1027_);
lean_dec(v_lo_1021_);
return v_snd_1028_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___boxed(lean_object* v___x_1055_, lean_object* v___x_1056_, lean_object* v_n_1057_, lean_object* v_as_1058_, lean_object* v_lo_1059_, lean_object* v_hi_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v___x_1055_, v___x_1056_, v_n_1057_, v_as_1058_, v_lo_1059_, v_hi_1060_);
lean_dec(v_hi_1060_);
lean_dec(v_n_1057_);
lean_dec(v___x_1056_);
lean_dec(v___x_1055_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(lean_object* v___x_1064_, lean_object* v___x_1065_, lean_object* v___x_1066_, size_t v_sz_1067_, size_t v_i_1068_, lean_object* v_bs_1069_){
_start:
{
uint8_t v___x_1070_; 
v___x_1070_ = lean_usize_dec_lt(v_i_1068_, v_sz_1067_);
if (v___x_1070_ == 0)
{
lean_dec_ref(v___x_1064_);
return v_bs_1069_;
}
else
{
uint8_t v___x_1071_; lean_object* v_v_1072_; lean_object* v___x_1073_; lean_object* v_bs_x27_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; size_t v___x_1083_; size_t v___x_1084_; lean_object* v___x_1085_; 
v___x_1071_ = lean_nat_dec_lt(v___x_1065_, v___x_1066_);
v_v_1072_ = lean_array_uget(v_bs_1069_, v_i_1068_);
v___x_1073_ = lean_unsigned_to_nat(0u);
v_bs_x27_1074_ = lean_array_uset(v_bs_1069_, v_i_1068_, v___x_1073_);
v___x_1075_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__0));
lean_inc_ref(v___x_1064_);
v___x_1076_ = lean_string_append(v___x_1064_, v___x_1075_);
v___x_1077_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_1072_, v___x_1071_);
v___x_1078_ = lean_string_append(v___x_1076_, v___x_1077_);
lean_dec_ref(v___x_1077_);
v___x_1079_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__1));
v___x_1080_ = lean_string_append(v___x_1078_, v___x_1079_);
v___x_1081_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordedMarker___closed__0));
v___x_1082_ = lean_string_append(v___x_1080_, v___x_1081_);
v___x_1083_ = ((size_t)1ULL);
v___x_1084_ = lean_usize_add(v_i_1068_, v___x_1083_);
v___x_1085_ = lean_array_uset(v_bs_x27_1074_, v_i_1068_, v___x_1082_);
v_i_1068_ = v___x_1084_;
v_bs_1069_ = v___x_1085_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___boxed(lean_object* v___x_1087_, lean_object* v___x_1088_, lean_object* v___x_1089_, lean_object* v_sz_1090_, lean_object* v_i_1091_, lean_object* v_bs_1092_){
_start:
{
size_t v_sz_boxed_1093_; size_t v_i_boxed_1094_; lean_object* v_res_1095_; 
v_sz_boxed_1093_ = lean_unbox_usize(v_sz_1090_);
lean_dec(v_sz_1090_);
v_i_boxed_1094_ = lean_unbox_usize(v_i_1091_);
lean_dec(v_i_1091_);
v_res_1095_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(v___x_1087_, v___x_1088_, v___x_1089_, v_sz_boxed_1093_, v_i_boxed_1094_, v_bs_1092_);
lean_dec(v___x_1089_);
lean_dec(v___x_1088_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(lean_object* v_as_1096_, size_t v_sz_1097_, size_t v_i_1098_, lean_object* v_b_1099_){
_start:
{
lean_object* v_a_1102_; uint8_t v___x_1106_; 
v___x_1106_ = lean_usize_dec_lt(v_i_1098_, v_sz_1097_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; 
v___x_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1107_, 0, v_b_1099_);
return v___x_1107_;
}
else
{
lean_object* v_a_1108_; lean_object* v_fst_1109_; lean_object* v_snd_1110_; lean_object* v_fst_1111_; lean_object* v_snd_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1151_; 
v_a_1108_ = lean_array_uget_borrowed(v_as_1096_, v_i_1098_);
v_fst_1109_ = lean_ctor_get(v_a_1108_, 0);
v_snd_1110_ = lean_ctor_get(v_a_1108_, 1);
v_fst_1111_ = lean_ctor_get(v_b_1099_, 0);
v_snd_1112_ = lean_ctor_get(v_b_1099_, 1);
v_isSharedCheck_1151_ = !lean_is_exclusive(v_b_1099_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1114_ = v_b_1099_;
v_isShared_1115_ = v_isSharedCheck_1151_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_snd_1112_);
lean_inc(v_fst_1111_);
lean_dec(v_b_1099_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1151_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; 
v___x_1116_ = lean_unsigned_to_nat(1u);
v___x_1117_ = lean_nat_sub(v_fst_1109_, v___x_1116_);
v___x_1118_ = lean_array_get_size(v_fst_1111_);
v___x_1119_ = lean_nat_dec_lt(v___x_1117_, v___x_1118_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1121_; 
lean_dec(v___x_1117_);
if (v_isShared_1115_ == 0)
{
v___x_1121_ = v___x_1114_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_fst_1111_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_snd_1112_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
v_a_1102_ = v___x_1121_;
goto v___jp_1101_;
}
}
else
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___y_1127_; lean_object* v___x_1140_; lean_object* v___y_1142_; lean_object* v___y_1143_; uint8_t v___x_1145_; 
v___x_1123_ = lean_unsigned_to_nat(0u);
v___x_1124_ = lean_array_fget_borrowed(v_fst_1111_, v___x_1117_);
v___x_1125_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace(v___x_1124_);
v___x_1140_ = lean_array_get_size(v_snd_1110_);
v___x_1145_ = lean_nat_dec_eq(v___x_1140_, v___x_1123_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; lean_object* v___y_1148_; uint8_t v___x_1150_; 
v___x_1146_ = lean_nat_sub(v___x_1140_, v___x_1116_);
v___x_1150_ = lean_nat_dec_le(v___x_1123_, v___x_1146_);
if (v___x_1150_ == 0)
{
lean_inc(v___x_1146_);
v___y_1148_ = v___x_1146_;
goto v___jp_1147_;
}
else
{
v___y_1148_ = v___x_1123_;
goto v___jp_1147_;
}
v___jp_1147_:
{
uint8_t v___x_1149_; 
v___x_1149_ = lean_nat_dec_le(v___y_1148_, v___x_1146_);
if (v___x_1149_ == 0)
{
lean_dec(v___x_1146_);
lean_inc(v___y_1148_);
v___y_1142_ = v___y_1148_;
v___y_1143_ = v___y_1148_;
goto v___jp_1141_;
}
else
{
v___y_1142_ = v___y_1148_;
v___y_1143_ = v___x_1146_;
goto v___jp_1141_;
}
}
}
else
{
lean_inc(v_snd_1110_);
v___y_1127_ = v_snd_1110_;
goto v___jp_1126_;
}
v___jp_1126_:
{
size_t v_sz_1128_; size_t v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1138_; 
v_sz_1128_ = lean_array_size(v___y_1127_);
v___x_1129_ = ((size_t)0ULL);
v___x_1130_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(v___x_1125_, v___x_1117_, v___x_1118_, v_sz_1128_, v___x_1129_, v___y_1127_);
lean_inc(v___x_1117_);
v___x_1131_ = l_Array_extract___redArg(v_fst_1111_, v___x_1123_, v___x_1117_);
v___x_1132_ = l_Array_append___redArg(v___x_1131_, v___x_1130_);
v___x_1133_ = l_Array_extract___redArg(v_fst_1111_, v___x_1117_, v___x_1118_);
lean_dec(v_fst_1111_);
v___x_1134_ = l_Array_append___redArg(v___x_1132_, v___x_1133_);
lean_dec_ref(v___x_1133_);
v___x_1135_ = lean_array_get_size(v___x_1130_);
lean_dec_ref(v___x_1130_);
v___x_1136_ = lean_nat_add(v_snd_1112_, v___x_1135_);
lean_dec(v_snd_1112_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 1, v___x_1136_);
lean_ctor_set(v___x_1114_, 0, v___x_1134_);
v___x_1138_ = v___x_1114_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1134_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v___x_1136_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
v_a_1102_ = v___x_1138_;
goto v___jp_1101_;
}
}
v___jp_1141_:
{
lean_object* v___x_1144_; 
lean_inc(v_snd_1110_);
v___x_1144_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v___x_1117_, v___x_1118_, v___x_1140_, v_snd_1110_, v___y_1142_, v___y_1143_);
lean_dec(v___y_1143_);
v___y_1127_ = v___x_1144_;
goto v___jp_1126_;
}
}
}
}
v___jp_1101_:
{
size_t v___x_1103_; size_t v___x_1104_; 
v___x_1103_ = ((size_t)1ULL);
v___x_1104_ = lean_usize_add(v_i_1098_, v___x_1103_);
v_i_1098_ = v___x_1104_;
v_b_1099_ = v_a_1102_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12___boxed(lean_object* v_as_1152_, lean_object* v_sz_1153_, lean_object* v_i_1154_, lean_object* v_b_1155_, lean_object* v___y_1156_){
_start:
{
size_t v_sz_boxed_1157_; size_t v_i_boxed_1158_; lean_object* v_res_1159_; 
v_sz_boxed_1157_ = lean_unbox_usize(v_sz_1153_);
lean_dec(v_sz_1153_);
v_i_boxed_1158_ = lean_unbox_usize(v_i_1154_);
lean_dec(v_i_1154_);
v_res_1159_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(v_as_1152_, v_sz_boxed_1157_, v_i_boxed_1158_, v_b_1155_);
lean_dec_ref(v_as_1152_);
return v_res_1159_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__2(void){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1162_ = lean_box(0);
v___x_1163_ = lean_unsigned_to_nat(16u);
v___x_1164_ = lean_mk_array(v___x_1163_, v___x_1162_);
return v___x_1164_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__3(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1165_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__2);
v___x_1166_ = lean_unsigned_to_nat(0u);
v___x_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1166_);
lean_ctor_set(v___x_1167_, 1, v___x_1165_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(lean_object* v_as_1176_, size_t v_sz_1177_, size_t v_i_1178_, lean_object* v_b_1179_){
_start:
{
lean_object* v_a_1182_; uint8_t v___x_1186_; 
v___x_1186_ = lean_usize_dec_lt(v_i_1178_, v_sz_1177_);
if (v___x_1186_ == 0)
{
lean_object* v___x_1187_; 
v___x_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1187_, 0, v_b_1179_);
return v___x_1187_;
}
else
{
lean_object* v_a_1188_; lean_object* v_snd_1189_; lean_object* v_fst_1190_; lean_object* v_snd_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1298_; 
v_a_1188_ = lean_array_uget_borrowed(v_as_1176_, v_i_1178_);
v_snd_1189_ = lean_ctor_get(v_a_1188_, 1);
lean_inc(v_snd_1189_);
v_fst_1190_ = lean_ctor_get(v_snd_1189_, 0);
v_snd_1191_ = lean_ctor_get(v_snd_1189_, 1);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_snd_1189_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1193_ = v_snd_1189_;
v_isShared_1194_ = v_isSharedCheck_1298_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_snd_1191_);
lean_inc(v_fst_1190_);
lean_dec(v_snd_1189_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1298_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1195_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; lean_object* v___x_1209_; lean_object* v___x_1210_; size_t v_sz_1211_; size_t v___x_1212_; lean_object* v___x_1213_; 
v___x_1195_ = lean_box(0);
v___x_1209_ = lean_unsigned_to_nat(0u);
v___x_1210_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__3);
v_sz_1211_ = lean_array_size(v_snd_1191_);
v___x_1212_ = ((size_t)0ULL);
v___x_1213_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(v_snd_1191_, v_sz_1211_, v___x_1212_, v___x_1210_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_a_1214_; lean_object* v___x_1215_; 
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_a_1214_);
lean_dec_ref_known(v___x_1213_, 1);
v___x_1215_ = l_IO_FS_readFile(v_fst_1190_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v_size_1219_; lean_object* v_buckets_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; size_t v_sz_1224_; lean_object* v___x_1225_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1265_; lean_object* v___y_1266_; lean_object* v___y_1269_; lean_object* v___x_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; 
lean_dec(v_snd_1191_);
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc_n(v_a_1216_, 2);
lean_dec_ref_known(v___x_1215_, 1);
v___x_1217_ = lean_string_utf8_byte_size(v_a_1216_);
v___x_1218_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1218_, 0, v_a_1216_);
lean_ctor_set(v___x_1218_, 1, v___x_1209_);
lean_ctor_set(v___x_1218_, 2, v___x_1217_);
v_size_1219_ = lean_ctor_get(v_a_1214_, 0);
lean_inc(v_size_1219_);
v_buckets_1220_ = lean_ctor_get(v_a_1214_, 1);
lean_inc_ref(v_buckets_1220_);
lean_dec(v_a_1214_);
v___x_1221_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0);
v___x_1222_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__4));
v___x_1223_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(v_a_1216_, v___x_1218_, v___x_1217_, v___x_1221_, v___x_1222_);
lean_dec_ref_known(v___x_1218_, 3);
v_sz_1224_ = lean_array_size(v___x_1223_);
v___x_1225_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9(v_sz_1224_, v___x_1212_, v___x_1223_);
v___x_1275_ = lean_mk_empty_array_with_capacity(v_size_1219_);
lean_dec(v_size_1219_);
v___x_1276_ = lean_array_get_size(v_buckets_1220_);
v___x_1277_ = lean_nat_dec_lt(v___x_1209_, v___x_1276_);
if (v___x_1277_ == 0)
{
lean_dec_ref(v_buckets_1220_);
v___y_1269_ = v___x_1275_;
goto v___jp_1268_;
}
else
{
size_t v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = lean_usize_of_nat(v___x_1276_);
v___x_1279_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(v_buckets_1220_, v___x_1212_, v___x_1278_, v___x_1275_);
lean_dec_ref(v_buckets_1220_);
v___y_1269_ = v___x_1279_;
goto v___jp_1268_;
}
v___jp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 1, v___x_1209_);
lean_ctor_set(v___x_1193_, 0, v___x_1225_);
v___x_1230_ = v___x_1193_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1225_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v___x_1209_);
v___x_1230_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
size_t v_sz_1231_; lean_object* v___x_1232_; 
v_sz_1231_ = lean_array_size(v___y_1228_);
v___x_1232_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(v___y_1228_, v_sz_1231_, v___x_1212_, v___x_1230_);
lean_dec_ref(v___y_1228_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; lean_object* v_fst_1234_; lean_object* v_snd_1235_; uint8_t v___x_1236_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1233_);
lean_dec_ref_known(v___x_1232_, 1);
v_fst_1234_ = lean_ctor_get(v_a_1233_, 0);
lean_inc(v_fst_1234_);
v_snd_1235_ = lean_ctor_get(v_a_1233_, 1);
lean_inc(v_snd_1235_);
lean_dec(v_a_1233_);
v___x_1236_ = lean_nat_dec_lt(v___x_1209_, v_snd_1235_);
if (v___x_1236_ == 0)
{
lean_dec(v_snd_1235_);
lean_dec(v_fst_1234_);
lean_dec(v_fst_1190_);
v_a_1182_ = v___x_1195_;
goto v___jp_1181_;
}
else
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; uint8_t v___x_1242_; 
v___x_1237_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__5));
lean_inc(v_snd_1235_);
v___x_1238_ = l_Nat_reprFast(v_snd_1235_);
v___x_1239_ = lean_string_append(v___x_1237_, v___x_1238_);
lean_dec_ref(v___x_1238_);
v___x_1240_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__6));
v___x_1241_ = lean_string_append(v___x_1239_, v___x_1240_);
v___x_1242_ = lean_nat_dec_eq(v_snd_1235_, v___y_1227_);
lean_dec(v_snd_1235_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; 
v___x_1243_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__7));
v___y_1197_ = v_fst_1234_;
v___y_1198_ = v___x_1241_;
v___y_1199_ = v___x_1243_;
goto v___jp_1196_;
}
else
{
lean_object* v___x_1244_; 
v___x_1244_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___y_1197_ = v_fst_1234_;
v___y_1198_ = v___x_1241_;
v___y_1199_ = v___x_1244_;
goto v___jp_1196_;
}
}
}
else
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
lean_dec(v_fst_1190_);
v_a_1245_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1232_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1232_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
}
v___jp_1254_:
{
lean_object* v___x_1260_; 
v___x_1260_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v___y_1257_, v___y_1256_, v___y_1255_, v___y_1259_);
lean_dec(v___y_1259_);
lean_dec(v___y_1257_);
v___y_1227_ = v___y_1258_;
v___y_1228_ = v___x_1260_;
goto v___jp_1226_;
}
v___jp_1261_:
{
uint8_t v___x_1267_; 
v___x_1267_ = lean_nat_dec_le(v___y_1266_, v___y_1264_);
if (v___x_1267_ == 0)
{
lean_dec(v___y_1264_);
lean_inc(v___y_1266_);
v___y_1255_ = v___y_1266_;
v___y_1256_ = v___y_1263_;
v___y_1257_ = v___y_1262_;
v___y_1258_ = v___y_1265_;
v___y_1259_ = v___y_1266_;
goto v___jp_1254_;
}
else
{
v___y_1255_ = v___y_1266_;
v___y_1256_ = v___y_1263_;
v___y_1257_ = v___y_1262_;
v___y_1258_ = v___y_1265_;
v___y_1259_ = v___y_1264_;
goto v___jp_1254_;
}
}
v___jp_1268_:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; 
v___x_1270_ = lean_unsigned_to_nat(1u);
v___x_1271_ = lean_array_get_size(v___y_1269_);
v___x_1272_ = lean_nat_dec_eq(v___x_1271_, v___x_1209_);
if (v___x_1272_ == 0)
{
lean_object* v___x_1273_; uint8_t v___x_1274_; 
v___x_1273_ = lean_nat_sub(v___x_1271_, v___x_1270_);
v___x_1274_ = lean_nat_dec_le(v___x_1209_, v___x_1273_);
if (v___x_1274_ == 0)
{
lean_inc(v___x_1273_);
v___y_1262_ = v___x_1271_;
v___y_1263_ = v___y_1269_;
v___y_1264_ = v___x_1273_;
v___y_1265_ = v___x_1270_;
v___y_1266_ = v___x_1273_;
goto v___jp_1261_;
}
else
{
v___y_1262_ = v___x_1271_;
v___y_1263_ = v___y_1269_;
v___y_1264_ = v___x_1273_;
v___y_1265_ = v___x_1270_;
v___y_1266_ = v___x_1209_;
goto v___jp_1261_;
}
}
else
{
v___y_1227_ = v___x_1270_;
v___y_1228_ = v___y_1269_;
goto v___jp_1226_;
}
}
}
else
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
lean_dec_ref_known(v___x_1215_, 1);
lean_dec(v_a_1214_);
lean_del_object(v___x_1193_);
v___x_1280_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__8));
v___x_1281_ = lean_string_append(v___x_1280_, v_fst_1190_);
lean_dec(v_fst_1190_);
v___x_1282_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__9));
v___x_1283_ = lean_string_append(v___x_1281_, v___x_1282_);
v___x_1284_ = lean_array_get_size(v_snd_1191_);
lean_dec(v_snd_1191_);
v___x_1285_ = l_Nat_reprFast(v___x_1284_);
v___x_1286_ = lean_string_append(v___x_1283_, v___x_1285_);
lean_dec_ref(v___x_1285_);
v___x_1287_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__10));
v___x_1288_ = lean_string_append(v___x_1286_, v___x_1287_);
v___x_1289_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_1288_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_dec_ref_known(v___x_1289_, 1);
v_a_1182_ = v___x_1195_;
goto v___jp_1181_;
}
else
{
return v___x_1289_;
}
}
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_del_object(v___x_1193_);
lean_dec(v_snd_1191_);
lean_dec(v_fst_1190_);
v_a_1290_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1213_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1213_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
v___jp_1196_:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1200_ = lean_string_append(v___y_1198_, v___y_1199_);
v___x_1201_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__0));
v___x_1202_ = lean_string_append(v___x_1200_, v___x_1201_);
v___x_1203_ = lean_string_append(v___x_1202_, v_fst_1190_);
v___x_1204_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_1203_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
lean_dec_ref_known(v___x_1204_, 1);
v___x_1205_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__1));
v___x_1206_ = lean_array_to_list(v___y_1197_);
v___x_1207_ = l_String_intercalate(v___x_1205_, v___x_1206_);
v___x_1208_ = l_IO_FS_writeFile(v_fst_1190_, v___x_1207_);
lean_dec_ref(v___x_1207_);
lean_dec(v_fst_1190_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_dec_ref_known(v___x_1208_, 1);
v_a_1182_ = v___x_1195_;
goto v___jp_1181_;
}
else
{
return v___x_1208_;
}
}
else
{
lean_dec(v___y_1197_);
lean_dec(v_fst_1190_);
return v___x_1204_;
}
}
}
}
v___jp_1181_:
{
size_t v___x_1183_; size_t v___x_1184_; 
v___x_1183_ = ((size_t)1ULL);
v___x_1184_ = lean_usize_add(v_i_1178_, v___x_1183_);
v_i_1178_ = v___x_1184_;
v_b_1179_ = v_a_1182_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___boxed(lean_object* v_as_1299_, lean_object* v_sz_1300_, lean_object* v_i_1301_, lean_object* v_b_1302_, lean_object* v___y_1303_){
_start:
{
size_t v_sz_boxed_1304_; size_t v_i_boxed_1305_; lean_object* v_res_1306_; 
v_sz_boxed_1304_ = lean_unbox_usize(v_sz_1300_);
lean_dec(v_sz_1300_);
v_i_boxed_1305_ = lean_unbox_usize(v_i_1301_);
lean_dec(v_i_1301_);
v_res_1306_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(v_as_1299_, v_sz_boxed_1304_, v_i_boxed_1305_, v_b_1302_);
lean_dec_ref(v_as_1299_);
return v_res_1306_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(lean_object* v_a_1307_, lean_object* v_x_1308_){
_start:
{
if (lean_obj_tag(v_x_1308_) == 0)
{
uint8_t v___x_1309_; 
v___x_1309_ = 0;
return v___x_1309_;
}
else
{
lean_object* v_key_1310_; lean_object* v_tail_1311_; uint8_t v___x_1312_; 
v_key_1310_ = lean_ctor_get(v_x_1308_, 0);
v_tail_1311_ = lean_ctor_get(v_x_1308_, 2);
v___x_1312_ = lean_string_dec_eq(v_key_1310_, v_a_1307_);
if (v___x_1312_ == 0)
{
v_x_1308_ = v_tail_1311_;
goto _start;
}
else
{
return v___x_1312_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg___boxed(lean_object* v_a_1314_, lean_object* v_x_1315_){
_start:
{
uint8_t v_res_1316_; lean_object* v_r_1317_; 
v_res_1316_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(v_a_1314_, v_x_1315_);
lean_dec(v_x_1315_);
lean_dec_ref(v_a_1314_);
v_r_1317_ = lean_box(v_res_1316_);
return v_r_1317_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(lean_object* v_a_1318_, lean_object* v_b_1319_, lean_object* v_x_1320_){
_start:
{
if (lean_obj_tag(v_x_1320_) == 0)
{
lean_dec(v_b_1319_);
lean_dec_ref(v_a_1318_);
return v_x_1320_;
}
else
{
lean_object* v_key_1321_; lean_object* v_value_1322_; lean_object* v_tail_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1335_; 
v_key_1321_ = lean_ctor_get(v_x_1320_, 0);
v_value_1322_ = lean_ctor_get(v_x_1320_, 1);
v_tail_1323_ = lean_ctor_get(v_x_1320_, 2);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_x_1320_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1325_ = v_x_1320_;
v_isShared_1326_ = v_isSharedCheck_1335_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_tail_1323_);
lean_inc(v_value_1322_);
lean_inc(v_key_1321_);
lean_dec(v_x_1320_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1335_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
uint8_t v___x_1327_; 
v___x_1327_ = lean_string_dec_eq(v_key_1321_, v_a_1318_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; lean_object* v___x_1330_; 
v___x_1328_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(v_a_1318_, v_b_1319_, v_tail_1323_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 2, v___x_1328_);
v___x_1330_ = v___x_1325_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_key_1321_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v_value_1322_);
lean_ctor_set(v_reuseFailAlloc_1331_, 2, v___x_1328_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
else
{
lean_object* v___x_1333_; 
lean_dec(v_value_1322_);
lean_dec(v_key_1321_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 1, v_b_1319_);
lean_ctor_set(v___x_1325_, 0, v_a_1318_);
v___x_1333_ = v___x_1325_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1318_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v_b_1319_);
lean_ctor_set(v_reuseFailAlloc_1334_, 2, v_tail_1323_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26___redArg(lean_object* v_x_1336_, lean_object* v_x_1337_){
_start:
{
if (lean_obj_tag(v_x_1337_) == 0)
{
return v_x_1336_;
}
else
{
lean_object* v_key_1338_; lean_object* v_value_1339_; lean_object* v_tail_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1363_; 
v_key_1338_ = lean_ctor_get(v_x_1337_, 0);
v_value_1339_ = lean_ctor_get(v_x_1337_, 1);
v_tail_1340_ = lean_ctor_get(v_x_1337_, 2);
v_isSharedCheck_1363_ = !lean_is_exclusive(v_x_1337_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1342_ = v_x_1337_;
v_isShared_1343_ = v_isSharedCheck_1363_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_tail_1340_);
lean_inc(v_value_1339_);
lean_inc(v_key_1338_);
lean_dec(v_x_1337_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1363_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1344_; uint64_t v___x_1345_; uint64_t v___x_1346_; uint64_t v___x_1347_; uint64_t v_fold_1348_; uint64_t v___x_1349_; uint64_t v___x_1350_; uint64_t v___x_1351_; size_t v___x_1352_; size_t v___x_1353_; size_t v___x_1354_; size_t v___x_1355_; size_t v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1344_ = lean_array_get_size(v_x_1336_);
v___x_1345_ = lean_string_hash(v_key_1338_);
v___x_1346_ = 32ULL;
v___x_1347_ = lean_uint64_shift_right(v___x_1345_, v___x_1346_);
v_fold_1348_ = lean_uint64_xor(v___x_1345_, v___x_1347_);
v___x_1349_ = 16ULL;
v___x_1350_ = lean_uint64_shift_right(v_fold_1348_, v___x_1349_);
v___x_1351_ = lean_uint64_xor(v_fold_1348_, v___x_1350_);
v___x_1352_ = lean_uint64_to_usize(v___x_1351_);
v___x_1353_ = lean_usize_of_nat(v___x_1344_);
v___x_1354_ = ((size_t)1ULL);
v___x_1355_ = lean_usize_sub(v___x_1353_, v___x_1354_);
v___x_1356_ = lean_usize_land(v___x_1352_, v___x_1355_);
v___x_1357_ = lean_array_uget_borrowed(v_x_1336_, v___x_1356_);
lean_inc(v___x_1357_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 2, v___x_1357_);
v___x_1359_ = v___x_1342_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_key_1338_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v_value_1339_);
lean_ctor_set(v_reuseFailAlloc_1362_, 2, v___x_1357_);
v___x_1359_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
lean_object* v___x_1360_; 
v___x_1360_ = lean_array_uset(v_x_1336_, v___x_1356_, v___x_1359_);
v_x_1336_ = v___x_1360_;
v_x_1337_ = v_tail_1340_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5___redArg(lean_object* v_i_1364_, lean_object* v_source_1365_, lean_object* v_target_1366_){
_start:
{
lean_object* v___x_1367_; uint8_t v___x_1368_; 
v___x_1367_ = lean_array_get_size(v_source_1365_);
v___x_1368_ = lean_nat_dec_lt(v_i_1364_, v___x_1367_);
if (v___x_1368_ == 0)
{
lean_dec_ref(v_source_1365_);
lean_dec(v_i_1364_);
return v_target_1366_;
}
else
{
lean_object* v_es_1369_; lean_object* v___x_1370_; lean_object* v_source_1371_; lean_object* v_target_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v_es_1369_ = lean_array_fget(v_source_1365_, v_i_1364_);
v___x_1370_ = lean_box(0);
v_source_1371_ = lean_array_fset(v_source_1365_, v_i_1364_, v___x_1370_);
v_target_1372_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26___redArg(v_target_1366_, v_es_1369_);
v___x_1373_ = lean_unsigned_to_nat(1u);
v___x_1374_ = lean_nat_add(v_i_1364_, v___x_1373_);
lean_dec(v_i_1364_);
v_i_1364_ = v___x_1374_;
v_source_1365_ = v_source_1371_;
v_target_1366_ = v_target_1372_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3___redArg(lean_object* v_data_1376_){
_start:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v_nbuckets_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1377_ = lean_array_get_size(v_data_1376_);
v___x_1378_ = lean_unsigned_to_nat(2u);
v_nbuckets_1379_ = lean_nat_mul(v___x_1377_, v___x_1378_);
v___x_1380_ = lean_unsigned_to_nat(0u);
v___x_1381_ = lean_box(0);
v___x_1382_ = lean_mk_array(v_nbuckets_1379_, v___x_1381_);
v___x_1383_ = lean_array_propagate_mark(v_data_1376_, v___x_1382_);
v___x_1384_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5___redArg(v___x_1380_, v_data_1376_, v___x_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(lean_object* v_m_1385_, lean_object* v_a_1386_, lean_object* v_b_1387_){
_start:
{
lean_object* v_size_1388_; lean_object* v_buckets_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1432_; 
v_size_1388_ = lean_ctor_get(v_m_1385_, 0);
v_buckets_1389_ = lean_ctor_get(v_m_1385_, 1);
v_isSharedCheck_1432_ = !lean_is_exclusive(v_m_1385_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1391_ = v_m_1385_;
v_isShared_1392_ = v_isSharedCheck_1432_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_buckets_1389_);
lean_inc(v_size_1388_);
lean_dec(v_m_1385_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1432_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; uint64_t v___x_1394_; uint64_t v___x_1395_; uint64_t v___x_1396_; uint64_t v_fold_1397_; uint64_t v___x_1398_; uint64_t v___x_1399_; uint64_t v___x_1400_; size_t v___x_1401_; size_t v___x_1402_; size_t v___x_1403_; size_t v___x_1404_; size_t v___x_1405_; lean_object* v_bkt_1406_; uint8_t v___x_1407_; 
v___x_1393_ = lean_array_get_size(v_buckets_1389_);
v___x_1394_ = lean_string_hash(v_a_1386_);
v___x_1395_ = 32ULL;
v___x_1396_ = lean_uint64_shift_right(v___x_1394_, v___x_1395_);
v_fold_1397_ = lean_uint64_xor(v___x_1394_, v___x_1396_);
v___x_1398_ = 16ULL;
v___x_1399_ = lean_uint64_shift_right(v_fold_1397_, v___x_1398_);
v___x_1400_ = lean_uint64_xor(v_fold_1397_, v___x_1399_);
v___x_1401_ = lean_uint64_to_usize(v___x_1400_);
v___x_1402_ = lean_usize_of_nat(v___x_1393_);
v___x_1403_ = ((size_t)1ULL);
v___x_1404_ = lean_usize_sub(v___x_1402_, v___x_1403_);
v___x_1405_ = lean_usize_land(v___x_1401_, v___x_1404_);
v_bkt_1406_ = lean_array_uget_borrowed(v_buckets_1389_, v___x_1405_);
v___x_1407_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(v_a_1386_, v_bkt_1406_);
if (v___x_1407_ == 0)
{
lean_object* v___x_1408_; lean_object* v_size_x27_1409_; lean_object* v___x_1410_; lean_object* v_buckets_x27_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; uint8_t v___x_1417_; 
v___x_1408_ = lean_unsigned_to_nat(1u);
v_size_x27_1409_ = lean_nat_add(v_size_1388_, v___x_1408_);
lean_dec(v_size_1388_);
lean_inc(v_bkt_1406_);
v___x_1410_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1410_, 0, v_a_1386_);
lean_ctor_set(v___x_1410_, 1, v_b_1387_);
lean_ctor_set(v___x_1410_, 2, v_bkt_1406_);
v_buckets_x27_1411_ = lean_array_uset(v_buckets_1389_, v___x_1405_, v___x_1410_);
v___x_1412_ = lean_unsigned_to_nat(4u);
v___x_1413_ = lean_nat_mul(v_size_x27_1409_, v___x_1412_);
v___x_1414_ = lean_unsigned_to_nat(3u);
v___x_1415_ = lean_nat_div(v___x_1413_, v___x_1414_);
lean_dec(v___x_1413_);
v___x_1416_ = lean_array_get_size(v_buckets_x27_1411_);
v___x_1417_ = lean_nat_dec_le(v___x_1415_, v___x_1416_);
lean_dec(v___x_1415_);
if (v___x_1417_ == 0)
{
lean_object* v_val_1418_; lean_object* v___x_1420_; 
v_val_1418_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3___redArg(v_buckets_x27_1411_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 1, v_val_1418_);
lean_ctor_set(v___x_1391_, 0, v_size_x27_1409_);
v___x_1420_ = v___x_1391_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_size_x27_1409_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v_val_1418_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
else
{
lean_object* v___x_1423_; 
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 1, v_buckets_x27_1411_);
lean_ctor_set(v___x_1391_, 0, v_size_x27_1409_);
v___x_1423_ = v___x_1391_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_size_x27_1409_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_buckets_x27_1411_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
else
{
lean_object* v___x_1425_; lean_object* v_buckets_x27_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1430_; 
lean_inc(v_bkt_1406_);
v___x_1425_ = lean_box(0);
v_buckets_x27_1426_ = lean_array_uset(v_buckets_1389_, v___x_1405_, v___x_1425_);
v___x_1427_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(v_a_1386_, v_b_1387_, v_bkt_1406_);
v___x_1428_ = lean_array_uset(v_buckets_x27_1426_, v___x_1405_, v___x_1427_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 1, v___x_1428_);
v___x_1430_ = v___x_1391_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_size_1388_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v___x_1428_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(lean_object* v_a_1433_, lean_object* v_fallback_1434_, lean_object* v_x_1435_){
_start:
{
if (lean_obj_tag(v_x_1435_) == 0)
{
lean_inc(v_fallback_1434_);
return v_fallback_1434_;
}
else
{
lean_object* v_key_1436_; lean_object* v_value_1437_; lean_object* v_tail_1438_; uint8_t v___x_1439_; 
v_key_1436_ = lean_ctor_get(v_x_1435_, 0);
v_value_1437_ = lean_ctor_get(v_x_1435_, 1);
v_tail_1438_ = lean_ctor_get(v_x_1435_, 2);
v___x_1439_ = lean_string_dec_eq(v_key_1436_, v_a_1433_);
if (v___x_1439_ == 0)
{
v_x_1435_ = v_tail_1438_;
goto _start;
}
else
{
lean_inc(v_value_1437_);
return v_value_1437_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg___boxed(lean_object* v_a_1441_, lean_object* v_fallback_1442_, lean_object* v_x_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(v_a_1441_, v_fallback_1442_, v_x_1443_);
lean_dec(v_x_1443_);
lean_dec(v_fallback_1442_);
lean_dec_ref(v_a_1441_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(lean_object* v_m_1445_, lean_object* v_a_1446_, lean_object* v_fallback_1447_){
_start:
{
lean_object* v_buckets_1448_; lean_object* v___x_1449_; uint64_t v___x_1450_; uint64_t v___x_1451_; uint64_t v___x_1452_; uint64_t v_fold_1453_; uint64_t v___x_1454_; uint64_t v___x_1455_; uint64_t v___x_1456_; size_t v___x_1457_; size_t v___x_1458_; size_t v___x_1459_; size_t v___x_1460_; size_t v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v_buckets_1448_ = lean_ctor_get(v_m_1445_, 1);
v___x_1449_ = lean_array_get_size(v_buckets_1448_);
v___x_1450_ = lean_string_hash(v_a_1446_);
v___x_1451_ = 32ULL;
v___x_1452_ = lean_uint64_shift_right(v___x_1450_, v___x_1451_);
v_fold_1453_ = lean_uint64_xor(v___x_1450_, v___x_1452_);
v___x_1454_ = 16ULL;
v___x_1455_ = lean_uint64_shift_right(v_fold_1453_, v___x_1454_);
v___x_1456_ = lean_uint64_xor(v_fold_1453_, v___x_1455_);
v___x_1457_ = lean_uint64_to_usize(v___x_1456_);
v___x_1458_ = lean_usize_of_nat(v___x_1449_);
v___x_1459_ = ((size_t)1ULL);
v___x_1460_ = lean_usize_sub(v___x_1458_, v___x_1459_);
v___x_1461_ = lean_usize_land(v___x_1457_, v___x_1460_);
v___x_1462_ = lean_array_uget_borrowed(v_buckets_1448_, v___x_1461_);
v___x_1463_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(v_a_1446_, v_fallback_1447_, v___x_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg___boxed(lean_object* v_m_1464_, lean_object* v_a_1465_, lean_object* v_fallback_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(v_m_1464_, v_a_1465_, v_fallback_1466_);
lean_dec(v_fallback_1466_);
lean_dec_ref(v_a_1465_);
lean_dec_ref(v_m_1464_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(lean_object* v_as_1470_, size_t v_sz_1471_, size_t v_i_1472_, lean_object* v_b_1473_){
_start:
{
uint8_t v___x_1475_; 
v___x_1475_ = lean_usize_dec_lt(v_i_1472_, v_sz_1471_);
if (v___x_1475_ == 0)
{
lean_object* v___x_1476_; 
v___x_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1476_, 0, v_b_1473_);
return v___x_1476_;
}
else
{
lean_object* v_a_1477_; lean_object* v_file_1478_; lean_object* v_pos_1479_; lean_object* v_option_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v_fst_1484_; lean_object* v_snd_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1506_; 
v_a_1477_ = lean_array_uget_borrowed(v_as_1470_, v_i_1472_);
v_file_1478_ = lean_ctor_get(v_a_1477_, 0);
v_pos_1479_ = lean_ctor_get(v_a_1477_, 1);
lean_inc_ref(v_pos_1479_);
v_option_1480_ = lean_ctor_get(v_a_1477_, 2);
v___x_1481_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___closed__0));
lean_inc_ref(v_file_1478_);
v___x_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1482_, 0, v_file_1478_);
lean_ctor_set(v___x_1482_, 1, v___x_1481_);
v___x_1483_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(v_b_1473_, v_file_1478_, v___x_1482_);
lean_dec_ref_known(v___x_1482_, 2);
v_fst_1484_ = lean_ctor_get(v___x_1483_, 0);
v_snd_1485_ = lean_ctor_get(v___x_1483_, 1);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1487_ = v___x_1483_;
v_isShared_1488_ = v_isSharedCheck_1506_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_snd_1485_);
lean_inc(v_fst_1484_);
lean_dec(v___x_1483_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1506_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v_line_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1504_; 
v_line_1489_ = lean_ctor_get(v_pos_1479_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v_pos_1479_);
if (v_isSharedCheck_1504_ == 0)
{
lean_object* v_unused_1505_; 
v_unused_1505_ = lean_ctor_get(v_pos_1479_, 1);
lean_dec(v_unused_1505_);
v___x_1491_ = v_pos_1479_;
v_isShared_1492_ = v_isSharedCheck_1504_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_line_1489_);
lean_dec(v_pos_1479_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1504_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
lean_inc(v_option_1480_);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 1, v_option_1480_);
lean_ctor_set(v___x_1487_, 0, v_line_1489_);
v___x_1494_ = v___x_1487_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_line_1489_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v_option_1480_);
v___x_1494_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
lean_object* v___x_1495_; lean_object* v___x_1497_; 
v___x_1495_ = lean_array_push(v_snd_1485_, v___x_1494_);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 1, v___x_1495_);
lean_ctor_set(v___x_1491_, 0, v_fst_1484_);
v___x_1497_ = v___x_1491_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_fst_1484_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v___x_1495_);
v___x_1497_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
lean_object* v___x_1498_; size_t v___x_1499_; size_t v___x_1500_; 
lean_inc_ref(v_file_1478_);
v___x_1498_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(v_b_1473_, v_file_1478_, v___x_1497_);
v___x_1499_ = ((size_t)1ULL);
v___x_1500_ = lean_usize_add(v_i_1472_, v___x_1499_);
v_i_1472_ = v___x_1500_;
v_b_1473_ = v___x_1498_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___boxed(lean_object* v_as_1507_, lean_object* v_sz_1508_, lean_object* v_i_1509_, lean_object* v_b_1510_, lean_object* v___y_1511_){
_start:
{
size_t v_sz_boxed_1512_; size_t v_i_boxed_1513_; lean_object* v_res_1514_; 
v_sz_boxed_1512_ = lean_unbox_usize(v_sz_1508_);
lean_dec(v_sz_1508_);
v_i_boxed_1513_ = lean_unbox_usize(v_i_1509_);
lean_dec(v_i_1509_);
v_res_1514_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(v_as_1507_, v_sz_boxed_1512_, v_i_boxed_1513_, v_b_1510_);
lean_dec_ref(v_as_1507_);
return v_res_1514_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0(void){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1515_ = lean_box(0);
v___x_1516_ = lean_unsigned_to_nat(16u);
v___x_1517_ = lean_mk_array(v___x_1516_, v___x_1515_);
return v___x_1517_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1(void){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v_byFile_1520_; 
v___x_1518_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0);
v___x_1519_ = lean_unsigned_to_nat(0u);
v_byFile_1520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byFile_1520_, 0, v___x_1519_);
lean_ctor_set(v_byFile_1520_, 1, v___x_1518_);
return v_byFile_1520_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(lean_object* v_records_1521_){
_start:
{
lean_object* v___x_1523_; lean_object* v_byFile_1524_; size_t v_sz_1525_; size_t v___x_1526_; lean_object* v___x_1527_; 
v___x_1523_ = lean_unsigned_to_nat(0u);
v_byFile_1524_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1);
v_sz_1525_ = lean_array_size(v_records_1521_);
v___x_1526_ = ((size_t)0ULL);
v___x_1527_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(v_records_1521_, v_sz_1525_, v___x_1526_, v_byFile_1524_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v_a_1528_; lean_object* v___y_1530_; lean_object* v_size_1542_; lean_object* v_buckets_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; uint8_t v___x_1546_; 
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_a_1528_);
lean_dec_ref_known(v___x_1527_, 1);
v_size_1542_ = lean_ctor_get(v_a_1528_, 0);
lean_inc(v_size_1542_);
v_buckets_1543_ = lean_ctor_get(v_a_1528_, 1);
lean_inc_ref(v_buckets_1543_);
lean_dec(v_a_1528_);
v___x_1544_ = lean_mk_empty_array_with_capacity(v_size_1542_);
lean_dec(v_size_1542_);
v___x_1545_ = lean_array_get_size(v_buckets_1543_);
v___x_1546_ = lean_nat_dec_lt(v___x_1523_, v___x_1545_);
if (v___x_1546_ == 0)
{
lean_dec_ref(v_buckets_1543_);
v___y_1530_ = v___x_1544_;
goto v___jp_1529_;
}
else
{
size_t v___x_1547_; lean_object* v___x_1548_; 
v___x_1547_ = lean_usize_of_nat(v___x_1545_);
v___x_1548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(v_buckets_1543_, v___x_1526_, v___x_1547_, v___x_1544_);
lean_dec_ref(v_buckets_1543_);
v___y_1530_ = v___x_1548_;
goto v___jp_1529_;
}
v___jp_1529_:
{
lean_object* v___x_1531_; size_t v_sz_1532_; lean_object* v___x_1533_; 
v___x_1531_ = lean_box(0);
v_sz_1532_ = lean_array_size(v___y_1530_);
v___x_1533_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(v___y_1530_, v_sz_1532_, v___x_1526_, v___x_1531_);
lean_dec_ref(v___y_1530_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1540_; 
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1540_ == 0)
{
lean_object* v_unused_1541_; 
v_unused_1541_ = lean_ctor_get(v___x_1533_, 0);
lean_dec(v_unused_1541_);
v___x_1535_ = v___x_1533_;
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
else
{
lean_dec(v___x_1533_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1538_; 
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 0, v___x_1531_);
v___x_1538_ = v___x_1535_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1531_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
else
{
return v___x_1533_;
}
}
}
else
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
v_a_1549_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1551_ = v___x_1527_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1527_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1554_; 
if (v_isShared_1552_ == 0)
{
v___x_1554_ = v___x_1551_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1549_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___boxed(lean_object* v_records_1557_, lean_object* v_a_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(v_records_1557_);
lean_dec_ref(v_records_1557_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0(lean_object* v_00_u03b2_1560_, lean_object* v_m_1561_, lean_object* v_a_1562_, lean_object* v_fallback_1563_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(v_m_1561_, v_a_1562_, v_fallback_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___boxed(lean_object* v_00_u03b2_1565_, lean_object* v_m_1566_, lean_object* v_a_1567_, lean_object* v_fallback_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0(v_00_u03b2_1565_, v_m_1566_, v_a_1567_, v_fallback_1568_);
lean_dec(v_fallback_1568_);
lean_dec_ref(v_a_1567_);
lean_dec_ref(v_m_1566_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1(lean_object* v_00_u03b2_1570_, lean_object* v_m_1571_, lean_object* v_a_1572_, lean_object* v_b_1573_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(v_m_1571_, v_a_1572_, v_b_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3(lean_object* v_00_u03b2_1575_, lean_object* v_m_1576_, lean_object* v_a_1577_, lean_object* v_fallback_1578_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(v_m_1576_, v_a_1577_, v_fallback_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___boxed(lean_object* v_00_u03b2_1580_, lean_object* v_m_1581_, lean_object* v_a_1582_, lean_object* v_fallback_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3(v_00_u03b2_1580_, v_m_1581_, v_a_1582_, v_fallback_1583_);
lean_dec(v_fallback_1583_);
lean_dec(v_a_1582_);
lean_dec_ref(v_m_1581_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5(lean_object* v_00_u03b2_1585_, lean_object* v_m_1586_, lean_object* v_a_1587_, lean_object* v_b_1588_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(v_m_1586_, v_a_1587_, v_b_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8(lean_object* v_a_1590_, lean_object* v___x_1591_, lean_object* v___x_1592_, lean_object* v_inst_1593_, lean_object* v_R_1594_, lean_object* v_a_1595_, lean_object* v_b_1596_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(v_a_1590_, v___x_1591_, v___x_1592_, v_a_1595_, v_b_1596_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___boxed(lean_object* v_a_1598_, lean_object* v___x_1599_, lean_object* v___x_1600_, lean_object* v_inst_1601_, lean_object* v_R_1602_, lean_object* v_a_1603_, lean_object* v_b_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8(v_a_1598_, v___x_1599_, v___x_1600_, v_inst_1601_, v_R_1602_, v_a_1603_, v_b_1604_);
lean_dec_ref(v___x_1599_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11(lean_object* v___x_1606_, lean_object* v___x_1607_, lean_object* v_n_1608_, lean_object* v_as_1609_, lean_object* v_lo_1610_, lean_object* v_hi_1611_, lean_object* v_w_1612_, lean_object* v_hlo_1613_, lean_object* v_hhi_1614_){
_start:
{
lean_object* v___x_1615_; 
v___x_1615_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v___x_1606_, v___x_1607_, v_n_1608_, v_as_1609_, v_lo_1610_, v_hi_1611_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___boxed(lean_object* v___x_1616_, lean_object* v___x_1617_, lean_object* v_n_1618_, lean_object* v_as_1619_, lean_object* v_lo_1620_, lean_object* v_hi_1621_, lean_object* v_w_1622_, lean_object* v_hlo_1623_, lean_object* v_hhi_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11(v___x_1616_, v___x_1617_, v_n_1618_, v_as_1619_, v_lo_1620_, v_hi_1621_, v_w_1622_, v_hlo_1623_, v_hhi_1624_);
lean_dec(v_hi_1621_);
lean_dec(v_n_1618_);
lean_dec(v___x_1617_);
lean_dec(v___x_1616_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14(lean_object* v_n_1626_, lean_object* v_as_1627_, lean_object* v_lo_1628_, lean_object* v_hi_1629_, lean_object* v_w_1630_, lean_object* v_hlo_1631_, lean_object* v_hhi_1632_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v_n_1626_, v_as_1627_, v_lo_1628_, v_hi_1629_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___boxed(lean_object* v_n_1634_, lean_object* v_as_1635_, lean_object* v_lo_1636_, lean_object* v_hi_1637_, lean_object* v_w_1638_, lean_object* v_hlo_1639_, lean_object* v_hhi_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14(v_n_1634_, v_as_1635_, v_lo_1636_, v_hi_1637_, v_w_1638_, v_hlo_1639_, v_hhi_1640_);
lean_dec(v_hi_1637_);
lean_dec(v_n_1634_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0(lean_object* v_00_u03b2_1642_, lean_object* v_a_1643_, lean_object* v_fallback_1644_, lean_object* v_x_1645_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(v_a_1643_, v_fallback_1644_, v_x_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1647_, lean_object* v_a_1648_, lean_object* v_fallback_1649_, lean_object* v_x_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0(v_00_u03b2_1647_, v_a_1648_, v_fallback_1649_, v_x_1650_);
lean_dec(v_x_1650_);
lean_dec(v_fallback_1649_);
lean_dec_ref(v_a_1648_);
return v_res_1651_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2(lean_object* v_00_u03b2_1652_, lean_object* v_a_1653_, lean_object* v_x_1654_){
_start:
{
uint8_t v___x_1655_; 
v___x_1655_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(v_a_1653_, v_x_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1656_, lean_object* v_a_1657_, lean_object* v_x_1658_){
_start:
{
uint8_t v_res_1659_; lean_object* v_r_1660_; 
v_res_1659_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2(v_00_u03b2_1656_, v_a_1657_, v_x_1658_);
lean_dec(v_x_1658_);
lean_dec_ref(v_a_1657_);
v_r_1660_ = lean_box(v_res_1659_);
return v_r_1660_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3(lean_object* v_00_u03b2_1661_, lean_object* v_data_1662_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3___redArg(v_data_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4(lean_object* v_00_u03b2_1664_, lean_object* v_a_1665_, lean_object* v_b_1666_, lean_object* v_x_1667_){
_start:
{
lean_object* v___x_1668_; 
v___x_1668_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(v_a_1665_, v_b_1666_, v_x_1667_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7(lean_object* v_00_u03b2_1669_, lean_object* v_a_1670_, lean_object* v_fallback_1671_, lean_object* v_x_1672_){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(v_a_1670_, v_fallback_1671_, v_x_1672_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___boxed(lean_object* v_00_u03b2_1674_, lean_object* v_a_1675_, lean_object* v_fallback_1676_, lean_object* v_x_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7(v_00_u03b2_1674_, v_a_1675_, v_fallback_1676_, v_x_1677_);
lean_dec(v_x_1677_);
lean_dec(v_fallback_1676_);
lean_dec(v_a_1675_);
return v_res_1678_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11(lean_object* v_00_u03b2_1679_, lean_object* v_a_1680_, lean_object* v_x_1681_){
_start:
{
uint8_t v___x_1682_; 
v___x_1682_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(v_a_1680_, v_x_1681_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___boxed(lean_object* v_00_u03b2_1683_, lean_object* v_a_1684_, lean_object* v_x_1685_){
_start:
{
uint8_t v_res_1686_; lean_object* v_r_1687_; 
v_res_1686_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11(v_00_u03b2_1683_, v_a_1684_, v_x_1685_);
lean_dec(v_x_1685_);
lean_dec(v_a_1684_);
v_r_1687_ = lean_box(v_res_1686_);
return v_r_1687_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12(lean_object* v_00_u03b2_1688_, lean_object* v_data_1689_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12___redArg(v_data_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13(lean_object* v_00_u03b2_1691_, lean_object* v_a_1692_, lean_object* v_b_1693_, lean_object* v_x_1694_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(v_a_1692_, v_b_1693_, v_x_1694_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20(lean_object* v___x_1696_, lean_object* v___x_1697_, lean_object* v_n_1698_, lean_object* v_lo_1699_, lean_object* v_hi_1700_, lean_object* v_hhi_1701_, lean_object* v_pivot_1702_, lean_object* v_as_1703_, lean_object* v_i_1704_, lean_object* v_k_1705_, lean_object* v_ilo_1706_, lean_object* v_ik_1707_, lean_object* v_w_1708_){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(v___x_1696_, v___x_1697_, v_hi_1700_, v_pivot_1702_, v_as_1703_, v_i_1704_, v_k_1705_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___boxed(lean_object* v___x_1710_, lean_object* v___x_1711_, lean_object* v_n_1712_, lean_object* v_lo_1713_, lean_object* v_hi_1714_, lean_object* v_hhi_1715_, lean_object* v_pivot_1716_, lean_object* v_as_1717_, lean_object* v_i_1718_, lean_object* v_k_1719_, lean_object* v_ilo_1720_, lean_object* v_ik_1721_, lean_object* v_w_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20(v___x_1710_, v___x_1711_, v_n_1712_, v_lo_1713_, v_hi_1714_, v_hhi_1715_, v_pivot_1716_, v_as_1717_, v_i_1718_, v_k_1719_, v_ilo_1720_, v_ik_1721_, v_w_1722_);
lean_dec(v_hi_1714_);
lean_dec(v_lo_1713_);
lean_dec(v_n_1712_);
lean_dec(v___x_1711_);
lean_dec(v___x_1710_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25(lean_object* v_n_1724_, lean_object* v_lo_1725_, lean_object* v_hi_1726_, lean_object* v_hhi_1727_, lean_object* v_pivot_1728_, lean_object* v_as_1729_, lean_object* v_i_1730_, lean_object* v_k_1731_, lean_object* v_ilo_1732_, lean_object* v_ik_1733_, lean_object* v_w_1734_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(v_hi_1726_, v_pivot_1728_, v_as_1729_, v_i_1730_, v_k_1731_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___boxed(lean_object* v_n_1736_, lean_object* v_lo_1737_, lean_object* v_hi_1738_, lean_object* v_hhi_1739_, lean_object* v_pivot_1740_, lean_object* v_as_1741_, lean_object* v_i_1742_, lean_object* v_k_1743_, lean_object* v_ilo_1744_, lean_object* v_ik_1745_, lean_object* v_w_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25(v_n_1736_, v_lo_1737_, v_hi_1738_, v_hhi_1739_, v_pivot_1740_, v_as_1741_, v_i_1742_, v_k_1743_, v_ilo_1744_, v_ik_1745_, v_w_1746_);
lean_dec_ref(v_pivot_1740_);
lean_dec(v_hi_1738_);
lean_dec(v_lo_1737_);
lean_dec(v_n_1736_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_1748_, lean_object* v_i_1749_, lean_object* v_source_1750_, lean_object* v_target_1751_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5___redArg(v_i_1749_, v_source_1750_, v_target_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15(lean_object* v_00_u03b2_1753_, lean_object* v_i_1754_, lean_object* v_source_1755_, lean_object* v_target_1756_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15___redArg(v_i_1754_, v_source_1755_, v_target_1756_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26(lean_object* v_00_u03b2_1758_, lean_object* v_x_1759_, lean_object* v_x_1760_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26___redArg(v_x_1759_, v_x_1760_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33(lean_object* v_00_u03b2_1762_, lean_object* v_x_1763_, lean_object* v_x_1764_){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33___redArg(v_x_1763_, v_x_1764_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(lean_object* v_declName_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v_env_1771_; lean_object* v___x_1772_; lean_object* v_env_1773_; lean_object* v___x_1774_; lean_object* v_toEnvExtension_1775_; lean_object* v_asyncMode_1776_; uint8_t v___x_1777_; lean_object* v___x_1778_; 
v___x_1769_ = l_Lean_instInhabitedDeclarationRanges_default;
v___x_1770_ = lean_st_ref_get(v___y_1767_);
v_env_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc_ref(v_env_1771_);
lean_dec(v___x_1770_);
v___x_1772_ = lean_st_ref_get(v___y_1767_);
v_env_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc_ref(v_env_1773_);
lean_dec(v___x_1772_);
v___x_1774_ = l_Lean_declRangeExt;
v_toEnvExtension_1775_ = lean_ctor_get(v___x_1774_, 0);
v_asyncMode_1776_ = lean_ctor_get(v_toEnvExtension_1775_, 2);
v___x_1777_ = 0;
lean_inc(v_declName_1766_);
v___x_1778_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1769_, v___x_1774_, v_env_1771_, v_declName_1766_, v_asyncMode_1776_, v___x_1777_);
if (lean_obj_tag(v___x_1778_) == 0)
{
uint8_t v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1779_ = 1;
v___x_1780_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1769_, v___x_1774_, v_env_1773_, v_declName_1766_, v_asyncMode_1776_, v___x_1779_);
v___x_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1780_);
return v___x_1781_;
}
else
{
lean_object* v___x_1782_; 
lean_dec_ref(v_env_1773_);
lean_dec(v_declName_1766_);
v___x_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1778_);
return v___x_1782_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg___boxed(lean_object* v_declName_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1783_, v___y_1784_);
lean_dec(v___y_1784_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(lean_object* v_declName_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v___x_1790_; lean_object* v_env_1791_; uint8_t v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1790_ = lean_st_ref_get(v___y_1788_);
v_env_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc_ref(v_env_1791_);
lean_dec(v___x_1790_);
v___x_1792_ = l_Lean_isRecCore(v_env_1791_, v_declName_1787_);
v___x_1793_ = lean_box(v___x_1792_);
v___x_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1793_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1795_, v___y_1796_);
lean_dec(v___y_1796_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(lean_object* v_declName_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v_ranges_1804_; lean_object* v___x_1810_; lean_object* v_env_1811_; lean_object* v___x_1812_; lean_object* v_a_1813_; uint8_t v___y_1819_; uint8_t v___x_1823_; 
v___x_1810_ = lean_st_ref_get(v___y_1801_);
v_env_1811_ = lean_ctor_get(v___x_1810_, 0);
lean_inc_ref_n(v_env_1811_, 2);
lean_dec(v___x_1810_);
lean_inc_n(v_declName_1799_, 2);
v___x_1812_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1799_, v___y_1801_);
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_a_1813_);
lean_dec_ref(v___x_1812_);
v___x_1823_ = l_Lean_isAuxRecursor(v_env_1811_, v_declName_1799_);
if (v___x_1823_ == 0)
{
uint8_t v___x_1824_; 
lean_inc(v_declName_1799_);
v___x_1824_ = l_Lean_isNoConfusion(v_env_1811_, v_declName_1799_);
v___y_1819_ = v___x_1824_;
goto v___jp_1818_;
}
else
{
lean_dec_ref(v_env_1811_);
v___y_1819_ = v___x_1823_;
goto v___jp_1818_;
}
v___jp_1803_:
{
if (lean_obj_tag(v_ranges_1804_) == 0)
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1805_ = l_Lean_builtinDeclRanges;
v___x_1806_ = lean_st_ref_get(v___x_1805_);
v___x_1807_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1806_, v_declName_1799_);
lean_dec(v_declName_1799_);
lean_dec(v___x_1806_);
v___x_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
return v___x_1808_;
}
else
{
lean_object* v___x_1809_; 
lean_dec(v_declName_1799_);
v___x_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1809_, 0, v_ranges_1804_);
return v___x_1809_;
}
}
v___jp_1814_:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v_a_1817_; 
v___x_1815_ = l_Lean_Name_getPrefix(v_declName_1799_);
v___x_1816_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v___x_1815_, v___y_1801_);
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
lean_inc(v_a_1817_);
lean_dec_ref(v___x_1816_);
v_ranges_1804_ = v_a_1817_;
goto v___jp_1803_;
}
v___jp_1818_:
{
if (v___y_1819_ == 0)
{
uint8_t v___x_1820_; 
v___x_1820_ = lean_unbox(v_a_1813_);
lean_dec(v_a_1813_);
if (v___x_1820_ == 0)
{
lean_object* v___x_1821_; lean_object* v_a_1822_; 
lean_inc(v_declName_1799_);
v___x_1821_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1799_, v___y_1801_);
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_a_1822_);
lean_dec_ref(v___x_1821_);
v_ranges_1804_ = v_a_1822_;
goto v___jp_1803_;
}
else
{
goto v___jp_1814_;
}
}
else
{
lean_dec(v_a_1813_);
goto v___jp_1814_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0___boxed(lean_object* v_declName_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_declName_1825_, v___y_1826_, v___y_1827_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(lean_object* v_failMod_1830_, lean_object* v_site_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_){
_start:
{
if (lean_obj_tag(v_site_1831_) == 0)
{
lean_object* v_name_1835_; lean_object* v___x_1836_; 
v_name_1835_ = lean_ctor_get(v_site_1831_, 0);
lean_inc(v_name_1835_);
lean_dec_ref_known(v_site_1831_, 1);
v___x_1836_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_name_1835_, v_a_1832_, v_a_1833_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1858_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1839_ = v___x_1836_;
v_isShared_1840_ = v_isSharedCheck_1858_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1836_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1858_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
if (lean_obj_tag(v_a_1837_) == 0)
{
lean_object* v___x_1841_; lean_object* v___x_1843_; 
v___x_1841_ = lean_box(0);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1841_);
v___x_1843_ = v___x_1839_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
else
{
lean_object* v_val_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1857_; 
v_val_1845_ = lean_ctor_get(v_a_1837_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v_a_1837_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1847_ = v_a_1837_;
v_isShared_1848_ = v_isSharedCheck_1857_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_val_1845_);
lean_dec(v_a_1837_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1857_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v_range_1849_; lean_object* v_pos_1850_; lean_object* v___x_1852_; 
v_range_1849_ = lean_ctor_get(v_val_1845_, 0);
lean_inc_ref(v_range_1849_);
lean_dec(v_val_1845_);
v_pos_1850_ = lean_ctor_get(v_range_1849_, 0);
lean_inc_ref(v_pos_1850_);
lean_dec_ref(v_range_1849_);
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 0, v_pos_1850_);
v___x_1852_ = v___x_1847_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_pos_1850_);
v___x_1852_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
lean_object* v___x_1854_; 
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1852_);
v___x_1854_ = v___x_1839_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1852_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
}
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
v_a_1859_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1836_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1836_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
else
{
lean_object* v_n_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1898_; 
v_n_1867_ = lean_ctor_get(v_site_1831_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v_site_1831_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1869_ = v_site_1831_;
v_isShared_1870_ = v_isSharedCheck_1898_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_n_1867_);
lean_dec(v_site_1831_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1898_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1871_; lean_object* v_env_1872_; lean_object* v___x_1873_; 
v___x_1871_ = lean_st_ref_get(v_a_1833_);
v_env_1872_ = lean_ctor_get(v___x_1871_, 0);
lean_inc_ref(v_env_1872_);
lean_dec(v___x_1871_);
v___x_1873_ = l_Lean_getVersoModuleDoc_x3f(v_env_1872_, v_failMod_1830_);
lean_dec_ref(v_env_1872_);
if (lean_obj_tag(v___x_1873_) == 1)
{
lean_object* v_val_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1893_; 
v_val_1874_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1876_ = v___x_1873_;
v_isShared_1877_ = v_isSharedCheck_1893_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_val_1874_);
lean_dec(v___x_1873_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1893_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1878_; uint8_t v___x_1879_; 
v___x_1878_ = lean_array_get_size(v_val_1874_);
v___x_1879_ = lean_nat_dec_lt(v_n_1867_, v___x_1878_);
if (v___x_1879_ == 0)
{
lean_object* v___x_1880_; lean_object* v___x_1882_; 
lean_del_object(v___x_1876_);
lean_dec(v_val_1874_);
lean_dec(v_n_1867_);
v___x_1880_ = lean_box(0);
if (v_isShared_1870_ == 0)
{
lean_ctor_set_tag(v___x_1869_, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1880_);
v___x_1882_ = v___x_1869_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1880_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
else
{
lean_object* v___x_1884_; lean_object* v_declarationRange_1885_; lean_object* v_pos_1886_; lean_object* v___x_1888_; 
v___x_1884_ = lean_array_fget(v_val_1874_, v_n_1867_);
lean_dec(v_n_1867_);
lean_dec(v_val_1874_);
v_declarationRange_1885_ = lean_ctor_get(v___x_1884_, 2);
lean_inc_ref(v_declarationRange_1885_);
lean_dec(v___x_1884_);
v_pos_1886_ = lean_ctor_get(v_declarationRange_1885_, 0);
lean_inc_ref(v_pos_1886_);
lean_dec_ref(v_declarationRange_1885_);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v_pos_1886_);
v___x_1888_ = v___x_1876_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_pos_1886_);
v___x_1888_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___x_1890_; 
if (v_isShared_1870_ == 0)
{
lean_ctor_set_tag(v___x_1869_, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1888_);
v___x_1890_ = v___x_1869_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
}
else
{
lean_object* v___x_1894_; lean_object* v___x_1896_; 
lean_dec(v___x_1873_);
lean_dec(v_n_1867_);
v___x_1894_ = lean_box(0);
if (v_isShared_1870_ == 0)
{
lean_ctor_set_tag(v___x_1869_, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1894_);
v___x_1896_ = v___x_1869_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1894_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f___boxed(lean_object* v_failMod_1899_, lean_object* v_site_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(v_failMod_1899_, v_site_1900_, v_a_1901_, v_a_1902_);
lean_dec(v_a_1902_);
lean_dec_ref(v_a_1901_);
lean_dec(v_failMod_1899_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0(lean_object* v_declName_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v___x_1909_; 
v___x_1909_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1905_, v___y_1907_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___boxed(lean_object* v_declName_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0(v_declName_1910_, v___y_1911_, v___y_1912_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1(lean_object* v_declName_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v___x_1919_; 
v___x_1919_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1915_, v___y_1917_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___boxed(lean_object* v_declName_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1(v_declName_1920_, v___y_1921_, v___y_1922_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(lean_object* v_x_1928_){
_start:
{
if (lean_obj_tag(v_x_1928_) == 0)
{
lean_object* v_name_1929_; lean_object* v___x_1930_; uint8_t v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v_name_1929_ = lean_ctor_get(v_x_1928_, 0);
lean_inc(v_name_1929_);
lean_dec_ref_known(v_x_1928_, 1);
v___x_1930_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__0));
v___x_1931_ = 1;
v___x_1932_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1929_, v___x_1931_);
v___x_1933_ = lean_string_append(v___x_1930_, v___x_1932_);
lean_dec_ref(v___x_1932_);
v___x_1934_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__1));
v___x_1935_ = lean_string_append(v___x_1933_, v___x_1934_);
return v___x_1935_;
}
else
{
lean_object* v_n_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v_n_1936_ = lean_ctor_get(v_x_1928_, 0);
lean_inc(v_n_1936_);
lean_dec_ref_known(v_x_1928_, 1);
v___x_1937_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__2));
v___x_1938_ = lean_unsigned_to_nat(1u);
v___x_1939_ = lean_nat_add(v_n_1936_, v___x_1938_);
lean_dec(v_n_1936_);
v___x_1940_ = l_Nat_reprFast(v___x_1939_);
v___x_1941_ = lean_string_append(v___x_1937_, v___x_1940_);
lean_dec_ref(v___x_1940_);
return v___x_1941_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(lean_object* v_o_1942_, lean_object* v___y_1943_){
_start:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v_env_1947_; lean_object* v___x_1948_; lean_object* v_toEnvExtension_1949_; lean_object* v_asyncMode_1950_; lean_object* v___x_1951_; uint8_t v___x_1952_; lean_object* v___x_1953_; lean_object* v_merged_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1962_; 
v___x_1945_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1946_ = lean_st_ref_get(v___y_1943_);
v_env_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc_ref(v_env_1947_);
lean_dec(v___x_1946_);
v___x_1948_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1949_ = lean_ctor_get(v___x_1948_, 0);
v_asyncMode_1950_ = lean_ctor_get(v_toEnvExtension_1949_, 2);
v___x_1951_ = lean_box(0);
v___x_1952_ = 0;
v___x_1953_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1945_, v___x_1948_, v_env_1947_, v_asyncMode_1950_, v___x_1951_, v___x_1952_);
v_merged_1954_ = lean_ctor_get(v___x_1953_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1962_ == 0)
{
lean_object* v_unused_1963_; 
v_unused_1963_ = lean_ctor_get(v___x_1953_, 1);
lean_dec(v_unused_1963_);
v___x_1956_ = v___x_1953_;
v_isShared_1957_ = v_isSharedCheck_1962_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_merged_1954_);
lean_dec(v___x_1953_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1962_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 1, v_merged_1954_);
lean_ctor_set(v___x_1956_, 0, v_o_1942_);
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_o_1942_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v_merged_1954_);
v___x_1959_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
lean_object* v___x_1960_; 
v___x_1960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1959_);
return v___x_1960_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg___boxed(lean_object* v_o_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_o_1964_, v___y_1965_);
lean_dec(v___y_1965_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0(lean_object* v_o_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
lean_object* v___x_1972_; 
v___x_1972_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_o_1968_, v___y_1970_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___boxed(lean_object* v_o_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0(v_o_1973_, v___y_1974_, v___y_1975_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(lean_object* v_opts_1978_, lean_object* v_opt_1979_){
_start:
{
lean_object* v_name_1980_; lean_object* v_defValue_1981_; lean_object* v_map_1982_; lean_object* v___x_1983_; 
v_name_1980_ = lean_ctor_get(v_opt_1979_, 0);
v_defValue_1981_ = lean_ctor_get(v_opt_1979_, 1);
v_map_1982_ = lean_ctor_get(v_opts_1978_, 0);
v___x_1983_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1982_, v_name_1980_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_inc(v_defValue_1981_);
return v_defValue_1981_;
}
else
{
lean_object* v_val_1984_; 
v_val_1984_ = lean_ctor_get(v___x_1983_, 0);
lean_inc(v_val_1984_);
lean_dec_ref_known(v___x_1983_, 1);
if (lean_obj_tag(v_val_1984_) == 3)
{
lean_object* v_v_1985_; 
v_v_1985_ = lean_ctor_get(v_val_1984_, 0);
lean_inc(v_v_1985_);
lean_dec_ref_known(v_val_1984_, 1);
return v_v_1985_;
}
else
{
lean_dec(v_val_1984_);
lean_inc(v_defValue_1981_);
return v_defValue_1981_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2___boxed(lean_object* v_opts_1986_, lean_object* v_opt_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(v_opts_1986_, v_opt_1987_);
lean_dec_ref(v_opt_1987_);
lean_dec_ref(v_opts_1986_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0(lean_object* v_c_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
lean_object* v_options_1993_; lean_object* v___x_1994_; lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2005_; 
v_options_1993_ = lean_ctor_get(v_c_1989_, 6);
lean_inc_ref(v_options_1993_);
lean_dec_ref(v_c_1989_);
v___x_1994_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_options_1993_, v___y_1991_);
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1997_ = v___x_1994_;
v_isShared_1998_ = v_isSharedCheck_2005_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1994_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2005_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_1999_; uint8_t v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2003_; 
v___x_1999_ = l_Lean_linter_doc_deferred;
v___x_2000_ = l_Lean_Linter_getLinterValue(v___x_1999_, v_a_1995_);
lean_dec(v_a_1995_);
v___x_2001_ = lean_box(v___x_2000_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_2001_);
v___x_2003_ = v___x_1997_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_2001_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0___boxed(lean_object* v_c_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0(v_c_2006_, v___y_2007_, v___y_2008_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
return v_res_2010_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1(lean_object* v_pkgRoot_2011_, lean_object* v_docCheckedModules_2012_, uint8_t v___y_2013_, lean_object* v_m_2014_){
_start:
{
uint8_t v___x_2015_; 
v___x_2015_ = l_Lean_Name_isPrefixOf(v_pkgRoot_2011_, v_m_2014_);
if (v___x_2015_ == 0)
{
return v___x_2015_;
}
else
{
uint8_t v___x_2016_; 
v___x_2016_ = l_Lean_NameSet_contains(v_docCheckedModules_2012_, v_m_2014_);
if (v___x_2016_ == 0)
{
return v___y_2013_;
}
else
{
uint8_t v___x_2017_; 
v___x_2017_ = 0;
return v___x_2017_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1___boxed(lean_object* v_pkgRoot_2018_, lean_object* v_docCheckedModules_2019_, lean_object* v___y_2020_, lean_object* v_m_2021_){
_start:
{
uint8_t v___y_7536__boxed_2022_; uint8_t v_res_2023_; lean_object* v_r_2024_; 
v___y_7536__boxed_2022_ = lean_unbox(v___y_2020_);
v_res_2023_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1(v_pkgRoot_2018_, v_docCheckedModules_2019_, v___y_7536__boxed_2022_, v_m_2021_);
lean_dec(v_m_2021_);
lean_dec(v_docCheckedModules_2019_);
lean_dec(v_pkgRoot_2018_);
v_r_2024_ = lean_box(v_res_2023_);
return v_r_2024_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(uint8_t v___x_2032_, lean_object* v_sp_2033_, lean_object* v_as_2034_, size_t v_sz_2035_, size_t v_i_2036_, lean_object* v_b_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v_a_2042_; uint8_t v_unlocated_2046_; 
v_unlocated_2046_ = lean_usize_dec_lt(v_i_2036_, v_sz_2035_);
if (v_unlocated_2046_ == 0)
{
lean_object* v___x_2047_; 
lean_dec(v_sp_2033_);
v___x_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2047_, 0, v_b_2037_);
return v___x_2047_;
}
else
{
lean_object* v_a_2048_; lean_object* v_snd_2049_; lean_object* v_fst_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2172_; 
v_a_2048_ = lean_array_uget_borrowed(v_as_2034_, v_i_2036_);
v_snd_2049_ = lean_ctor_get(v_a_2048_, 1);
lean_inc(v_snd_2049_);
v_fst_2050_ = lean_ctor_get(v_snd_2049_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v_snd_2049_);
if (v_isSharedCheck_2172_ == 0)
{
lean_object* v_unused_2173_; 
v_unused_2173_ = lean_ctor_get(v_snd_2049_, 1);
lean_dec(v_unused_2173_);
v___x_2052_ = v_snd_2049_;
v_isShared_2053_ = v_isSharedCheck_2172_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_fst_2050_);
lean_dec(v_snd_2049_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2172_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v_fst_2054_; lean_object* v_fst_2055_; lean_object* v_snd_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2171_; 
v_fst_2054_ = lean_ctor_get(v_a_2048_, 0);
v_fst_2055_ = lean_ctor_get(v_b_2037_, 0);
v_snd_2056_ = lean_ctor_get(v_b_2037_, 1);
v_isSharedCheck_2171_ = !lean_is_exclusive(v_b_2037_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2058_ = v_b_2037_;
v_isShared_2059_ = v_isSharedCheck_2171_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_snd_2056_);
lean_inc(v_fst_2055_);
lean_dec(v_b_2037_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2171_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v_site_2060_; lean_object* v___x_2061_; 
v_site_2060_ = lean_ctor_get(v_fst_2050_, 0);
lean_inc_ref_n(v_site_2060_, 2);
lean_dec(v_fst_2050_);
v___x_2061_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(v_fst_2054_, v_site_2060_, v___y_2038_, v___y_2039_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_a_2062_);
lean_dec_ref_known(v___x_2061_, 1);
if (lean_obj_tag(v_a_2062_) == 0)
{
lean_object* v___x_2063_; lean_object* v_name_2064_; lean_object* v_ref_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
lean_dec(v_snd_2056_);
v___x_2063_ = l_Lean_linter_doc_deferred;
v_name_2064_ = lean_ctor_get(v___x_2063_, 0);
v_ref_2065_ = lean_ctor_get(v___y_2038_, 2);
lean_inc(v_fst_2054_);
v___x_2066_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2054_, v___x_2032_);
v___x_2067_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__0));
v___x_2068_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_2060_);
v___x_2069_ = lean_string_append(v___x_2067_, v___x_2068_);
lean_dec_ref(v___x_2068_);
v___x_2070_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__1));
v___x_2071_ = lean_string_append(v___x_2069_, v___x_2070_);
v___x_2072_ = lean_string_append(v___x_2071_, v___x_2066_);
lean_dec_ref(v___x_2066_);
v___x_2073_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__2));
v___x_2074_ = lean_string_append(v___x_2072_, v___x_2073_);
lean_inc(v_name_2064_);
v___x_2075_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2064_, v___x_2032_);
v___x_2076_ = lean_string_append(v___x_2074_, v___x_2075_);
lean_dec_ref(v___x_2075_);
v___x_2077_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__3));
v___x_2078_ = lean_string_append(v___x_2076_, v___x_2077_);
v___x_2079_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2078_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v___x_2080_; lean_object* v___x_2082_; 
lean_dec_ref_known(v___x_2079_, 1);
lean_del_object(v___x_2052_);
v___x_2080_ = lean_box(v_unlocated_2046_);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 1, v___x_2080_);
v___x_2082_ = v___x_2058_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_fst_2055_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v___x_2080_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
v_a_2042_ = v___x_2082_;
goto v___jp_2041_;
}
}
else
{
lean_object* v_a_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2097_; 
lean_del_object(v___x_2058_);
lean_dec(v_fst_2055_);
lean_dec(v_sp_2033_);
v_a_2084_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2086_ = v___x_2079_;
v_isShared_2087_ = v_isSharedCheck_2097_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_a_2084_);
lean_dec(v___x_2079_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2097_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2092_; 
v___x_2088_ = lean_io_error_to_string(v_a_2084_);
v___x_2089_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2088_);
v___x_2090_ = l_Lean_MessageData_ofFormat(v___x_2089_);
lean_inc(v_ref_2065_);
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 1, v___x_2090_);
lean_ctor_set(v___x_2052_, 0, v_ref_2065_);
v___x_2092_ = v___x_2052_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_ref_2065_);
lean_ctor_set(v_reuseFailAlloc_2096_, 1, v___x_2090_);
v___x_2092_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
lean_object* v___x_2094_; 
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 0, v___x_2092_);
v___x_2094_ = v___x_2086_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___x_2092_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
}
else
{
lean_object* v_val_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2162_; 
lean_dec_ref(v_site_2060_);
v_val_2098_ = lean_ctor_get(v_a_2062_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v_a_2062_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2100_ = v_a_2062_;
v_isShared_2101_ = v_isSharedCheck_2162_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_val_2098_);
lean_dec(v_a_2062_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2162_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v_ref_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v_ref_2102_ = lean_ctor_get(v___y_2038_, 2);
v___x_2103_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__4));
lean_inc(v_fst_2054_);
lean_inc(v_sp_2033_);
v___x_2104_ = l_Lean_SearchPath_findWithExt(v_sp_2033_, v___x_2103_, v_fst_2054_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_a_2105_);
lean_dec_ref_known(v___x_2104_, 1);
if (lean_obj_tag(v_a_2105_) == 0)
{
lean_object* v___x_2106_; lean_object* v_name_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
lean_dec(v_val_2098_);
lean_dec(v_snd_2056_);
v___x_2106_ = l_Lean_linter_doc_deferred;
v_name_2107_ = lean_ctor_get(v___x_2106_, 0);
v___x_2108_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__5));
lean_inc(v_fst_2054_);
v___x_2109_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2054_, v___x_2032_);
v___x_2110_ = lean_string_append(v___x_2108_, v___x_2109_);
lean_dec_ref(v___x_2109_);
v___x_2111_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__6));
v___x_2112_ = lean_string_append(v___x_2110_, v___x_2111_);
lean_inc(v_name_2107_);
v___x_2113_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2107_, v___x_2032_);
v___x_2114_ = lean_string_append(v___x_2112_, v___x_2113_);
lean_dec_ref(v___x_2113_);
v___x_2115_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__3));
v___x_2116_ = lean_string_append(v___x_2114_, v___x_2115_);
v___x_2117_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2116_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v___x_2118_; lean_object* v___x_2120_; 
lean_dec_ref_known(v___x_2117_, 1);
lean_del_object(v___x_2100_);
lean_del_object(v___x_2052_);
v___x_2118_ = lean_box(v_unlocated_2046_);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 1, v___x_2118_);
v___x_2120_ = v___x_2058_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_fst_2055_);
lean_ctor_set(v_reuseFailAlloc_2121_, 1, v___x_2118_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
v_a_2042_ = v___x_2120_;
goto v___jp_2041_;
}
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2137_; 
lean_del_object(v___x_2058_);
lean_dec(v_fst_2055_);
lean_dec(v_sp_2033_);
v_a_2122_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2124_ = v___x_2117_;
v_isShared_2125_ = v_isSharedCheck_2137_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2117_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2137_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2126_; lean_object* v___x_2128_; 
v___x_2126_ = lean_io_error_to_string(v_a_2122_);
if (v_isShared_2101_ == 0)
{
lean_ctor_set_tag(v___x_2100_, 3);
lean_ctor_set(v___x_2100_, 0, v___x_2126_);
v___x_2128_ = v___x_2100_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2126_);
v___x_2128_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
lean_object* v___x_2129_; lean_object* v___x_2131_; 
v___x_2129_ = l_Lean_MessageData_ofFormat(v___x_2128_);
lean_inc(v_ref_2102_);
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 1, v___x_2129_);
lean_ctor_set(v___x_2052_, 0, v_ref_2102_);
v___x_2131_ = v___x_2052_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_ref_2102_);
lean_ctor_set(v_reuseFailAlloc_2135_, 1, v___x_2129_);
v___x_2131_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
lean_object* v___x_2133_; 
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v___x_2131_);
v___x_2133_ = v___x_2124_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v___x_2131_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
}
}
else
{
lean_object* v_val_2138_; lean_object* v___x_2139_; lean_object* v_name_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2144_; 
lean_del_object(v___x_2100_);
lean_del_object(v___x_2052_);
v_val_2138_ = lean_ctor_get(v_a_2105_, 0);
lean_inc(v_val_2138_);
lean_dec_ref_known(v_a_2105_, 1);
v___x_2139_ = l_Lean_linter_doc_deferred;
v_name_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_name_2140_);
v___x_2141_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2141_, 0, v_val_2138_);
lean_ctor_set(v___x_2141_, 1, v_val_2098_);
lean_ctor_set(v___x_2141_, 2, v_name_2140_);
v___x_2142_ = lean_array_push(v_fst_2055_, v___x_2141_);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 0, v___x_2142_);
v___x_2144_ = v___x_2058_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2142_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v_snd_2056_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
v_a_2042_ = v___x_2144_;
goto v___jp_2041_;
}
}
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2161_; 
lean_dec(v_val_2098_);
lean_del_object(v___x_2058_);
lean_dec(v_snd_2056_);
lean_dec(v_fst_2055_);
lean_dec(v_sp_2033_);
v_a_2146_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2148_ = v___x_2104_;
v_isShared_2149_ = v_isSharedCheck_2161_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2104_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2161_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2150_; lean_object* v___x_2152_; 
v___x_2150_ = lean_io_error_to_string(v_a_2146_);
if (v_isShared_2101_ == 0)
{
lean_ctor_set_tag(v___x_2100_, 3);
lean_ctor_set(v___x_2100_, 0, v___x_2150_);
v___x_2152_ = v___x_2100_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2150_);
v___x_2152_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v___x_2153_; lean_object* v___x_2155_; 
v___x_2153_ = l_Lean_MessageData_ofFormat(v___x_2152_);
lean_inc(v_ref_2102_);
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 1, v___x_2153_);
lean_ctor_set(v___x_2052_, 0, v_ref_2102_);
v___x_2155_ = v___x_2052_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_ref_2102_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v___x_2153_);
v___x_2155_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
lean_object* v___x_2157_; 
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 0, v___x_2155_);
v___x_2157_ = v___x_2148_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2155_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
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
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2170_; 
lean_dec_ref(v_site_2060_);
lean_del_object(v___x_2058_);
lean_dec(v_snd_2056_);
lean_dec(v_fst_2055_);
lean_del_object(v___x_2052_);
lean_dec(v_sp_2033_);
v_a_2163_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2165_ = v___x_2061_;
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2061_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2168_; 
if (v_isShared_2166_ == 0)
{
v___x_2168_ = v___x_2165_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_a_2163_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
}
}
v___jp_2041_:
{
size_t v___x_2043_; size_t v___x_2044_; 
v___x_2043_ = ((size_t)1ULL);
v___x_2044_ = lean_usize_add(v_i_2036_, v___x_2043_);
v_i_2036_ = v___x_2044_;
v_b_2037_ = v_a_2042_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___boxed(lean_object* v___x_2174_, lean_object* v_sp_2175_, lean_object* v_as_2176_, lean_object* v_sz_2177_, lean_object* v_i_2178_, lean_object* v_b_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
uint8_t v___x_7560__boxed_2183_; size_t v_sz_boxed_2184_; size_t v_i_boxed_2185_; lean_object* v_res_2186_; 
v___x_7560__boxed_2183_ = lean_unbox(v___x_2174_);
v_sz_boxed_2184_ = lean_unbox_usize(v_sz_2177_);
lean_dec(v_sz_2177_);
v_i_boxed_2185_ = lean_unbox_usize(v_i_2178_);
lean_dec(v_i_2178_);
v_res_2186_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(v___x_7560__boxed_2183_, v_sp_2175_, v_as_2176_, v_sz_boxed_2184_, v_i_boxed_2185_, v_b_2179_, v___y_2180_, v___y_2181_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec_ref(v_as_2176_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg(lean_object* v_sp_2193_, uint8_t v___y_2194_, lean_object* v_as_2195_, size_t v_sz_2196_, size_t v_i_2197_, lean_object* v_b_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v_a_2202_; uint8_t v___x_2206_; 
v___x_2206_ = lean_usize_dec_lt(v_i_2197_, v_sz_2196_);
if (v___x_2206_ == 0)
{
lean_object* v___x_2207_; 
lean_dec(v_sp_2193_);
v___x_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2207_, 0, v_b_2198_);
return v___x_2207_;
}
else
{
lean_object* v_a_2208_; lean_object* v_snd_2209_; lean_object* v_fst_2210_; lean_object* v_fst_2211_; lean_object* v_snd_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2305_; 
v_a_2208_ = lean_array_uget_borrowed(v_as_2195_, v_i_2197_);
v_snd_2209_ = lean_ctor_get(v_a_2208_, 1);
lean_inc(v_snd_2209_);
v_fst_2210_ = lean_ctor_get(v_snd_2209_, 0);
lean_inc(v_fst_2210_);
v_fst_2211_ = lean_ctor_get(v_a_2208_, 0);
v_snd_2212_ = lean_ctor_get(v_snd_2209_, 1);
v_isSharedCheck_2305_ = !lean_is_exclusive(v_snd_2209_);
if (v_isSharedCheck_2305_ == 0)
{
lean_object* v_unused_2306_; 
v_unused_2306_ = lean_ctor_get(v_snd_2209_, 0);
lean_dec(v_unused_2306_);
v___x_2214_ = v_snd_2209_;
v_isShared_2215_ = v_isSharedCheck_2305_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_snd_2212_);
lean_dec(v_snd_2209_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2305_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v_site_2216_; lean_object* v_sourceString_2217_; lean_object* v___x_2218_; lean_object* v___y_2220_; lean_object* v___x_2297_; lean_object* v___x_2298_; uint8_t v___x_2299_; 
v_site_2216_ = lean_ctor_get(v_fst_2210_, 0);
lean_inc_ref(v_site_2216_);
v_sourceString_2217_ = lean_ctor_get(v_fst_2210_, 2);
lean_inc_ref(v_sourceString_2217_);
lean_dec(v_fst_2210_);
v___x_2218_ = lean_box(0);
v___x_2297_ = lean_string_utf8_byte_size(v_sourceString_2217_);
v___x_2298_ = lean_unsigned_to_nat(0u);
v___x_2299_ = lean_nat_dec_eq(v___x_2297_, v___x_2298_);
if (v___x_2299_ == 0)
{
lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2300_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__4));
v___x_2301_ = lean_string_append(v___x_2300_, v_sourceString_2217_);
lean_dec_ref(v_sourceString_2217_);
v___x_2302_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__5));
v___x_2303_ = lean_string_append(v___x_2301_, v___x_2302_);
v___y_2220_ = v___x_2303_;
goto v___jp_2219_;
}
else
{
lean_object* v___x_2304_; 
lean_dec_ref(v_sourceString_2217_);
v___x_2304_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___y_2220_ = v___x_2304_;
goto v___jp_2219_;
}
v___jp_2219_:
{
lean_object* v_ref_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v_ref_2221_ = lean_ctor_get(v___y_2199_, 2);
v___x_2222_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__4));
lean_inc(v_fst_2211_);
lean_inc(v_sp_2193_);
v___x_2223_ = l_Lean_SearchPath_findWithExt(v_sp_2193_, v___x_2222_, v_fst_2211_);
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_object* v_a_2224_; 
v_a_2224_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_a_2224_);
lean_dec_ref_known(v___x_2223_, 1);
if (lean_obj_tag(v_a_2224_) == 0)
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2225_ = l_Lean_MessageData_toString(v_snd_2212_);
v___x_2226_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__0));
lean_inc(v_fst_2211_);
v___x_2227_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2211_, v___y_2194_);
v___x_2228_ = lean_string_append(v___x_2226_, v___x_2227_);
lean_dec_ref(v___x_2227_);
v___x_2229_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__1));
v___x_2230_ = lean_string_append(v___x_2228_, v___x_2229_);
v___x_2231_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_2216_);
v___x_2232_ = lean_string_append(v___x_2230_, v___x_2231_);
lean_dec_ref(v___x_2231_);
v___x_2233_ = lean_string_append(v___x_2232_, v___y_2220_);
lean_dec_ref(v___y_2220_);
v___x_2234_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__2));
v___x_2235_ = lean_string_append(v___x_2233_, v___x_2234_);
v___x_2236_ = lean_string_append(v___x_2235_, v___x_2225_);
lean_dec_ref(v___x_2225_);
v___x_2237_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2236_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_dec_ref_known(v___x_2237_, 1);
lean_del_object(v___x_2214_);
v_a_2202_ = v___x_2218_;
goto v___jp_2201_;
}
else
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2251_; 
lean_dec(v_sp_2193_);
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2240_ = v___x_2237_;
v_isShared_2241_ = v_isSharedCheck_2251_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2237_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2251_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2246_; 
v___x_2242_ = lean_io_error_to_string(v_a_2238_);
v___x_2243_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2242_);
v___x_2244_ = l_Lean_MessageData_ofFormat(v___x_2243_);
lean_inc(v_ref_2221_);
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 1, v___x_2244_);
lean_ctor_set(v___x_2214_, 0, v_ref_2221_);
v___x_2246_ = v___x_2214_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_ref_2221_);
lean_ctor_set(v_reuseFailAlloc_2250_, 1, v___x_2244_);
v___x_2246_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
lean_object* v___x_2248_; 
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 0, v___x_2246_);
v___x_2248_ = v___x_2240_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v___x_2246_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
}
else
{
lean_object* v_val_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2282_; 
v_val_2252_ = lean_ctor_get(v_a_2224_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v_a_2224_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2254_ = v_a_2224_;
v_isShared_2255_ = v_isSharedCheck_2282_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_val_2252_);
lean_dec(v_a_2224_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2282_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2256_ = l_Lean_MessageData_toString(v_snd_2212_);
v___x_2257_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__3));
v___x_2258_ = lean_string_append(v_val_2252_, v___x_2257_);
v___x_2259_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_2216_);
v___x_2260_ = lean_string_append(v___x_2258_, v___x_2259_);
lean_dec_ref(v___x_2259_);
v___x_2261_ = lean_string_append(v___x_2260_, v___y_2220_);
lean_dec_ref(v___y_2220_);
v___x_2262_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__2));
v___x_2263_ = lean_string_append(v___x_2261_, v___x_2262_);
v___x_2264_ = lean_string_append(v___x_2263_, v___x_2256_);
lean_dec_ref(v___x_2256_);
v___x_2265_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2264_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_dec_ref_known(v___x_2265_, 1);
lean_del_object(v___x_2254_);
lean_del_object(v___x_2214_);
v_a_2202_ = v___x_2218_;
goto v___jp_2201_;
}
else
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2281_; 
lean_dec(v_sp_2193_);
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2268_ = v___x_2265_;
v_isShared_2269_ = v_isSharedCheck_2281_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2265_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2281_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2270_; lean_object* v___x_2272_; 
v___x_2270_ = lean_io_error_to_string(v_a_2266_);
if (v_isShared_2255_ == 0)
{
lean_ctor_set_tag(v___x_2254_, 3);
lean_ctor_set(v___x_2254_, 0, v___x_2270_);
v___x_2272_ = v___x_2254_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2270_);
v___x_2272_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
lean_object* v___x_2273_; lean_object* v___x_2275_; 
v___x_2273_ = l_Lean_MessageData_ofFormat(v___x_2272_);
lean_inc(v_ref_2221_);
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 1, v___x_2273_);
lean_ctor_set(v___x_2214_, 0, v_ref_2221_);
v___x_2275_ = v___x_2214_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_ref_2221_);
lean_ctor_set(v_reuseFailAlloc_2279_, 1, v___x_2273_);
v___x_2275_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
lean_object* v___x_2277_; 
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 0, v___x_2275_);
v___x_2277_ = v___x_2268_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v___x_2275_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
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
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2296_; 
lean_dec_ref(v___y_2220_);
lean_dec_ref(v_site_2216_);
lean_dec(v_snd_2212_);
lean_dec(v_sp_2193_);
v_a_2283_ = lean_ctor_get(v___x_2223_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2285_ = v___x_2223_;
v_isShared_2286_ = v_isSharedCheck_2296_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2223_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2296_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2291_; 
v___x_2287_ = lean_io_error_to_string(v_a_2283_);
v___x_2288_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2287_);
v___x_2289_ = l_Lean_MessageData_ofFormat(v___x_2288_);
lean_inc(v_ref_2221_);
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 1, v___x_2289_);
lean_ctor_set(v___x_2214_, 0, v_ref_2221_);
v___x_2291_ = v___x_2214_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_ref_2221_);
lean_ctor_set(v_reuseFailAlloc_2295_, 1, v___x_2289_);
v___x_2291_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
lean_object* v___x_2293_; 
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 0, v___x_2291_);
v___x_2293_ = v___x_2285_;
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
v___jp_2201_:
{
size_t v___x_2203_; size_t v___x_2204_; 
v___x_2203_ = ((size_t)1ULL);
v___x_2204_ = lean_usize_add(v_i_2197_, v___x_2203_);
v_i_2197_ = v___x_2204_;
v_b_2198_ = v_a_2202_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___boxed(lean_object* v_sp_2307_, lean_object* v___y_2308_, lean_object* v_as_2309_, lean_object* v_sz_2310_, lean_object* v_i_2311_, lean_object* v_b_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
uint8_t v___y_7842__boxed_2315_; size_t v_sz_boxed_2316_; size_t v_i_boxed_2317_; lean_object* v_res_2318_; 
v___y_7842__boxed_2315_ = lean_unbox(v___y_2308_);
v_sz_boxed_2316_ = lean_unbox_usize(v_sz_2310_);
lean_dec(v_sz_2310_);
v_i_boxed_2317_ = lean_unbox_usize(v_i_2311_);
lean_dec(v_i_2311_);
v_res_2318_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg(v_sp_2307_, v___y_7842__boxed_2315_, v_as_2309_, v_sz_boxed_2316_, v_i_boxed_2317_, v_b_2312_, v___y_2313_);
lean_dec_ref(v___y_2313_);
lean_dec_ref(v_as_2309_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(lean_object* v_pkgRoot_2319_, lean_object* v_as_2320_, size_t v_sz_2321_, size_t v_i_2322_, lean_object* v_b_2323_){
_start:
{
lean_object* v_a_2326_; uint8_t v___x_2330_; 
v___x_2330_ = lean_usize_dec_lt(v_i_2322_, v_sz_2321_);
if (v___x_2330_ == 0)
{
lean_object* v___x_2331_; 
v___x_2331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2331_, 0, v_b_2323_);
return v___x_2331_;
}
else
{
lean_object* v_a_2332_; uint8_t v___x_2333_; 
v_a_2332_ = lean_array_uget_borrowed(v_as_2320_, v_i_2322_);
v___x_2333_ = l_Lean_Name_isPrefixOf(v_pkgRoot_2319_, v_a_2332_);
if (v___x_2333_ == 0)
{
v_a_2326_ = v_b_2323_;
goto v___jp_2325_;
}
else
{
lean_object* v___x_2334_; 
lean_inc(v_a_2332_);
v___x_2334_ = l_Lean_NameSet_insert(v_b_2323_, v_a_2332_);
v_a_2326_ = v___x_2334_;
goto v___jp_2325_;
}
}
v___jp_2325_:
{
size_t v___x_2327_; size_t v___x_2328_; 
v___x_2327_ = ((size_t)1ULL);
v___x_2328_ = lean_usize_add(v_i_2322_, v___x_2327_);
v_i_2322_ = v___x_2328_;
v_b_2323_ = v_a_2326_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1___boxed(lean_object* v_pkgRoot_2335_, lean_object* v_as_2336_, lean_object* v_sz_2337_, lean_object* v_i_2338_, lean_object* v_b_2339_, lean_object* v___y_2340_){
_start:
{
size_t v_sz_boxed_2341_; size_t v_i_boxed_2342_; lean_object* v_res_2343_; 
v_sz_boxed_2341_ = lean_unbox_usize(v_sz_2337_);
lean_dec(v_sz_2337_);
v_i_boxed_2342_ = lean_unbox_usize(v_i_2338_);
lean_dec(v_i_2338_);
v_res_2343_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(v_pkgRoot_2335_, v_as_2336_, v_sz_boxed_2341_, v_i_boxed_2342_, v_b_2339_);
lean_dec_ref(v_as_2336_);
lean_dec(v_pkgRoot_2335_);
return v_res_2343_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5(void){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2350_ = l_Lean_Options_empty;
v___x_2351_ = l_Lean_Core_getMaxHeartbeats(v___x_2350_);
return v___x_2351_;
}
}
static uint16_t _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6(void){
_start:
{
lean_object* v___x_2352_; uint16_t v___x_2353_; 
v___x_2352_ = l_Lean_Options_empty;
v___x_2353_ = l_Lean_OptionFlags_ofOptions(v___x_2352_);
return v___x_2353_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7(void){
_start:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2354_ = lean_unsigned_to_nat(1u);
v___x_2355_ = l_Lean_firstFrontendMacroScope;
v___x_2356_ = lean_nat_add(v___x_2355_, v___x_2354_);
return v___x_2356_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12(void){
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
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13(void){
_start:
{
size_t v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2370_ = ((size_t)5ULL);
v___x_2371_ = lean_unsigned_to_nat(0u);
v___x_2372_ = lean_unsigned_to_nat(32u);
v___x_2373_ = lean_mk_empty_array_with_capacity(v___x_2372_);
v___x_2374_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12);
v___x_2375_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2375_, 0, v___x_2374_);
lean_ctor_set(v___x_2375_, 1, v___x_2373_);
lean_ctor_set(v___x_2375_, 2, v___x_2371_);
lean_ctor_set(v___x_2375_, 3, v___x_2371_);
lean_ctor_set_usize(v___x_2375_, 4, v___x_2370_);
return v___x_2375_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14(void){
_start:
{
lean_object* v___x_2376_; uint64_t v___x_2377_; lean_object* v___x_2378_; 
v___x_2376_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13);
v___x_2377_ = 0ULL;
v___x_2378_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2378_, 0, v___x_2376_);
lean_ctor_set_uint64(v___x_2378_, sizeof(void*)*1, v___x_2377_);
return v___x_2378_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15(void){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2379_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16(void){
_start:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2380_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15);
v___x_2381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2380_);
return v___x_2381_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17(void){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2382_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v___x_2383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2382_);
lean_ctor_set(v___x_2383_, 1, v___x_2382_);
return v___x_2383_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18(void){
_start:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2384_ = lean_unsigned_to_nat(0u);
v___x_2385_ = l_Lean_Options_empty;
v___x_2386_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___closed__0));
v___x_2387_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2386_);
lean_ctor_set(v___x_2387_, 1, v___x_2385_);
lean_ctor_set(v___x_2387_, 2, v___x_2386_);
lean_ctor_set(v___x_2387_, 3, v___x_2384_);
lean_ctor_set(v___x_2387_, 4, v___x_2384_);
lean_ctor_set(v___x_2387_, 5, v___x_2384_);
return v___x_2387_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19(void){
_start:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2388_ = l_Lean_NameSet_empty;
v___x_2389_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13);
v___x_2390_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2389_);
lean_ctor_set(v___x_2390_, 1, v___x_2389_);
lean_ctor_set(v___x_2390_, 2, v___x_2388_);
return v___x_2390_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20(void){
_start:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; uint8_t v_unlocated_2393_; lean_object* v___x_2394_; 
v___x_2391_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13);
v___x_2392_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v_unlocated_2393_ = 1;
v___x_2394_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2394_, 0, v___x_2392_);
lean_ctor_set(v___x_2394_, 1, v___x_2392_);
lean_ctor_set(v___x_2394_, 2, v___x_2391_);
lean_ctor_set_uint8(v___x_2394_, sizeof(void*)*3, v_unlocated_2393_);
return v___x_2394_;
}
}
static uint16_t _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__21(void){
_start:
{
uint16_t v___x_2395_; uint16_t v___x_2396_; uint16_t v___x_2397_; 
v___x_2395_ = 512;
v___x_2396_ = lean_uint16_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_2397_ = lean_uint16_land(v___x_2396_, v___x_2395_);
return v___x_2397_;
}
}
static uint8_t _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22(void){
_start:
{
uint16_t v___x_2398_; uint16_t v___x_2399_; uint8_t v___x_2400_; 
v___x_2398_ = 0;
v___x_2399_ = lean_uint16_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__21, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__21_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__21);
v___x_2400_ = lean_uint16_dec_eq(v___x_2399_, v___x_2398_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(lean_object* v_args_2401_, lean_object* v_linterOpts_2402_, lean_object* v_sp_2403_, lean_object* v_env_2404_, lean_object* v_pkgRoot_2405_, lean_object* v_docCheckedModules_2406_){
_start:
{
lean_object* v___y_2409_; lean_object* v_a_2413_; uint8_t v___y_2417_; lean_object* v_a_2418_; lean_object* v___y_2435_; lean_object* v_a_2436_; lean_object* v___y_2461_; uint8_t v___y_2462_; uint8_t v_lintOnly_2464_; uint8_t v_mode_2465_; lean_object* v___f_2466_; uint8_t v___y_2468_; lean_object* v___y_2469_; uint8_t v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; uint16_t v___y_2474_; lean_object* v_fileName_2475_; lean_object* v_fileMap_2476_; lean_object* v_currNamespace_2477_; lean_object* v_openDecls_2478_; lean_object* v_initHeartbeats_2479_; lean_object* v_maxHeartbeats_2480_; lean_object* v_quotContext_2481_; lean_object* v_currMacroScope_2482_; lean_object* v_cancelTk_x3f_2483_; lean_object* v_inheritedTraceOptions_2484_; lean_object* v_currRecDepth_2485_; lean_object* v_ref_2486_; uint8_t v_suppressElabErrors_2487_; uint8_t v_isRecordingDeps_2488_; lean_object* v___y_2489_; uint8_t v___y_2519_; lean_object* v___y_2520_; uint8_t v___y_2521_; lean_object* v___y_2522_; uint8_t v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; uint16_t v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; uint8_t v___y_2565_; 
v_lintOnly_2464_ = lean_ctor_get_uint8(v_args_2401_, sizeof(void*)*4);
v_mode_2465_ = lean_ctor_get_uint8(v_args_2401_, sizeof(void*)*4 + 1);
v___f_2466_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__3));
if (v_lintOnly_2464_ == 0)
{
lean_object* v___x_2606_; uint8_t v___x_2607_; 
v___x_2606_ = l_Lean_linter_doc_deferred;
v___x_2607_ = l_Lean_Linter_getLinterValue(v___x_2606_, v_linterOpts_2402_);
v___y_2565_ = v___x_2607_;
goto v___jp_2564_;
}
else
{
lean_object* v___x_2608_; lean_object* v_name_2609_; uint8_t v___x_2610_; 
v___x_2608_ = l_Lean_linter_doc_deferred;
v_name_2609_ = lean_ctor_get(v___x_2608_, 0);
v___x_2610_ = l_Lean_Linter_isLinterEnabledByOptions(v_name_2609_, v_linterOpts_2402_);
v___y_2565_ = v___x_2610_;
goto v___jp_2564_;
}
v___jp_2408_:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___y_2409_);
lean_ctor_set(v___x_2410_, 1, v_docCheckedModules_2406_);
v___x_2411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2410_);
return v___x_2411_;
}
v___jp_2412_:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2414_ = lean_mk_io_user_error(v_a_2413_);
v___x_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2414_);
return v___x_2415_;
}
v___jp_2416_:
{
if (lean_obj_tag(v_a_2418_) == 0)
{
lean_object* v_msg_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v_msg_2419_ = lean_ctor_get(v_a_2418_, 1);
lean_inc_ref(v_msg_2419_);
lean_dec_ref_known(v_a_2418_, 2);
v___x_2420_ = l_Lean_MessageData_toString(v_msg_2419_);
v___x_2421_ = lean_mk_io_user_error(v___x_2420_);
v___x_2422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2421_);
return v___x_2422_;
}
else
{
lean_object* v_id_2423_; lean_object* v___x_2424_; 
v_id_2423_ = lean_ctor_get(v_a_2418_, 0);
lean_inc(v_id_2423_);
lean_dec_ref_known(v_a_2418_, 2);
v___x_2424_ = l_Lean_InternalExceptionId_getName(v_id_2423_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v_a_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
lean_dec(v_id_2423_);
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
lean_inc(v_a_2425_);
lean_dec_ref_known(v___x_2424_, 1);
v___x_2426_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_2427_ = l_Lean_Name_toString(v_a_2425_, v___y_2417_);
v___x_2428_ = lean_string_append(v___x_2426_, v___x_2427_);
lean_dec_ref(v___x_2427_);
v_a_2413_ = v___x_2428_;
goto v___jp_2412_;
}
else
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
lean_dec_ref_known(v___x_2424_, 1);
v___x_2429_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_2430_ = l_Nat_reprFast(v_id_2423_);
v___x_2431_ = lean_string_append(v___x_2429_, v___x_2430_);
lean_dec_ref(v___x_2430_);
v___x_2432_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_2433_ = lean_string_append(v___x_2431_, v___x_2432_);
v_a_2413_ = v___x_2433_;
goto v___jp_2412_;
}
}
}
v___jp_2434_:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v_moduleNames_2439_; size_t v_sz_2440_; size_t v___x_2441_; lean_object* v___x_2442_; 
v___x_2437_ = lean_st_ref_get(v___y_2435_);
lean_dec(v___y_2435_);
lean_dec(v___x_2437_);
v___x_2438_ = l_Lean_Environment_header(v_env_2404_);
lean_dec_ref(v_env_2404_);
v_moduleNames_2439_ = lean_ctor_get(v___x_2438_, 4);
lean_inc_ref(v_moduleNames_2439_);
lean_dec_ref(v___x_2438_);
v_sz_2440_ = lean_array_size(v_moduleNames_2439_);
v___x_2441_ = ((size_t)0ULL);
v___x_2442_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(v_pkgRoot_2405_, v_moduleNames_2439_, v_sz_2440_, v___x_2441_, v_docCheckedModules_2406_);
lean_dec_ref(v_moduleNames_2439_);
lean_dec(v_pkgRoot_2405_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2451_; 
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2445_ = v___x_2442_;
v_isShared_2446_ = v_isSharedCheck_2451_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2442_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2451_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2447_; lean_object* v___x_2449_; 
v___x_2447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2447_, 0, v_a_2436_);
lean_ctor_set(v___x_2447_, 1, v_a_2443_);
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 0, v___x_2447_);
v___x_2449_ = v___x_2445_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v___x_2447_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
else
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
lean_dec_ref(v_a_2436_);
v_a_2452_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2454_ = v___x_2442_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2442_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2452_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
}
v___jp_2460_:
{
lean_object* v___x_2463_; 
v___x_2463_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2463_, 0, v___y_2462_);
v___y_2435_ = v___y_2461_;
v_a_2436_ = v___x_2463_;
goto v___jp_2434_;
}
v___jp_2467_:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2490_ = l_Lean_maxRecDepth;
v___x_2491_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(v___y_2472_, v___x_2490_);
lean_inc_ref(v___y_2472_);
v___x_2492_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2492_, 0, v_fileName_2475_);
lean_ctor_set(v___x_2492_, 1, v_fileMap_2476_);
lean_ctor_set(v___x_2492_, 2, v___y_2472_);
lean_ctor_set(v___x_2492_, 3, v___x_2491_);
lean_ctor_set(v___x_2492_, 4, v_currNamespace_2477_);
lean_ctor_set(v___x_2492_, 5, v_openDecls_2478_);
lean_ctor_set(v___x_2492_, 6, v_initHeartbeats_2479_);
lean_ctor_set(v___x_2492_, 7, v_maxHeartbeats_2480_);
lean_ctor_set(v___x_2492_, 8, v_quotContext_2481_);
lean_ctor_set(v___x_2492_, 9, v_currMacroScope_2482_);
lean_ctor_set(v___x_2492_, 10, v_cancelTk_x3f_2483_);
lean_ctor_set(v___x_2492_, 11, v_inheritedTraceOptions_2484_);
v___x_2493_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2493_, 0, v___x_2492_);
lean_ctor_set(v___x_2493_, 1, v_currRecDepth_2485_);
lean_ctor_set(v___x_2493_, 2, v_ref_2486_);
lean_ctor_set_uint16(v___x_2493_, sizeof(void*)*3, v___y_2474_);
lean_ctor_set_uint8(v___x_2493_, sizeof(void*)*3 + 2, v_suppressElabErrors_2487_);
lean_ctor_set_uint8(v___x_2493_, sizeof(void*)*3 + 3, v_isRecordingDeps_2488_);
v___x_2494_ = l_Lean_Doc_DeferredCheck_run(v___y_2469_, v___f_2466_, v___x_2493_, v___y_2489_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v_a_2495_; uint8_t v___x_2496_; uint8_t v___x_2497_; 
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_a_2495_);
lean_dec_ref_known(v___x_2494_, 1);
v___x_2496_ = 1;
v___x_2497_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_2465_, v___x_2496_);
if (v___x_2497_ == 0)
{
lean_object* v___x_2498_; size_t v_sz_2499_; size_t v___x_2500_; lean_object* v___x_2501_; 
lean_dec(v___y_2489_);
v___x_2498_ = lean_box(0);
v_sz_2499_ = lean_array_size(v_a_2495_);
v___x_2500_ = ((size_t)0ULL);
v___x_2501_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg(v_sp_2403_, v___y_2470_, v_a_2495_, v_sz_2499_, v___x_2500_, v___x_2498_, v___x_2493_);
lean_dec_ref_known(v___x_2493_, 3);
if (lean_obj_tag(v___x_2501_) == 0)
{
lean_object* v___x_2502_; uint8_t v___x_2503_; 
lean_dec_ref_known(v___x_2501_, 1);
v___x_2502_ = lean_array_get_size(v_a_2495_);
lean_dec(v_a_2495_);
v___x_2503_ = lean_nat_dec_eq(v___x_2502_, v___y_2471_);
lean_dec(v___y_2471_);
if (v___x_2503_ == 0)
{
v___y_2461_ = v___y_2473_;
v___y_2462_ = v___y_2470_;
goto v___jp_2460_;
}
else
{
v___y_2461_ = v___y_2473_;
v___y_2462_ = v___x_2497_;
goto v___jp_2460_;
}
}
else
{
lean_object* v_a_2504_; 
lean_dec(v_a_2495_);
lean_dec(v___y_2473_);
lean_dec(v___y_2471_);
lean_dec(v_docCheckedModules_2406_);
lean_dec(v_pkgRoot_2405_);
lean_dec_ref(v_env_2404_);
v_a_2504_ = lean_ctor_get(v___x_2501_, 0);
lean_inc(v_a_2504_);
lean_dec_ref_known(v___x_2501_, 1);
v___y_2417_ = v___y_2470_;
v_a_2418_ = v_a_2504_;
goto v___jp_2416_;
}
}
else
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; size_t v_sz_2508_; size_t v___x_2509_; lean_object* v___x_2510_; 
v___x_2505_ = lean_mk_empty_array_with_capacity(v___y_2471_);
lean_dec(v___y_2471_);
v___x_2506_ = lean_box(v___y_2468_);
v___x_2507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2505_);
lean_ctor_set(v___x_2507_, 1, v___x_2506_);
v_sz_2508_ = lean_array_size(v_a_2495_);
v___x_2509_ = ((size_t)0ULL);
v___x_2510_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(v___x_2497_, v_sp_2403_, v_a_2495_, v_sz_2508_, v___x_2509_, v___x_2507_, v___x_2493_, v___y_2489_);
lean_dec(v___y_2489_);
lean_dec_ref_known(v___x_2493_, 3);
lean_dec(v_a_2495_);
if (lean_obj_tag(v___x_2510_) == 0)
{
lean_object* v_a_2511_; lean_object* v_fst_2512_; lean_object* v_snd_2513_; lean_object* v___x_2514_; uint8_t v___x_2515_; 
v_a_2511_ = lean_ctor_get(v___x_2510_, 0);
lean_inc(v_a_2511_);
lean_dec_ref_known(v___x_2510_, 1);
v_fst_2512_ = lean_ctor_get(v_a_2511_, 0);
lean_inc(v_fst_2512_);
v_snd_2513_ = lean_ctor_get(v_a_2511_, 1);
lean_inc(v_snd_2513_);
lean_dec(v_a_2511_);
v___x_2514_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2514_, 0, v_fst_2512_);
v___x_2515_ = lean_unbox(v_snd_2513_);
lean_dec(v_snd_2513_);
lean_ctor_set_uint8(v___x_2514_, sizeof(void*)*1, v___x_2515_);
v___y_2435_ = v___y_2473_;
v_a_2436_ = v___x_2514_;
goto v___jp_2434_;
}
else
{
lean_object* v_a_2516_; 
lean_dec(v___y_2473_);
lean_dec(v_docCheckedModules_2406_);
lean_dec(v_pkgRoot_2405_);
lean_dec_ref(v_env_2404_);
v_a_2516_ = lean_ctor_get(v___x_2510_, 0);
lean_inc(v_a_2516_);
lean_dec_ref_known(v___x_2510_, 1);
v___y_2417_ = v___y_2470_;
v_a_2418_ = v_a_2516_;
goto v___jp_2416_;
}
}
}
else
{
lean_object* v_a_2517_; 
lean_dec_ref_known(v___x_2493_, 3);
lean_dec(v___y_2489_);
lean_dec(v___y_2473_);
lean_dec(v___y_2471_);
lean_dec(v_docCheckedModules_2406_);
lean_dec(v_pkgRoot_2405_);
lean_dec_ref(v_env_2404_);
lean_dec(v_sp_2403_);
v_a_2517_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_a_2517_);
lean_dec_ref_known(v___x_2494_, 1);
v___y_2417_ = v___y_2470_;
v_a_2418_ = v_a_2517_;
goto v___jp_2416_;
}
}
v___jp_2518_:
{
lean_object* v___x_2529_; lean_object* v_env_2530_; lean_object* v_nextMacroScope_2531_; lean_object* v_ngen_2532_; lean_object* v_auxDeclNGen_2533_; lean_object* v_traceState_2534_; lean_object* v_recordedDeps_2535_; lean_object* v_messages_2536_; lean_object* v_infoState_2537_; lean_object* v_snapshotTasks_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2562_; 
v___x_2529_ = lean_st_ref_take(v___y_2527_);
v_env_2530_ = lean_ctor_get(v___x_2529_, 0);
v_nextMacroScope_2531_ = lean_ctor_get(v___x_2529_, 1);
v_ngen_2532_ = lean_ctor_get(v___x_2529_, 2);
v_auxDeclNGen_2533_ = lean_ctor_get(v___x_2529_, 3);
v_traceState_2534_ = lean_ctor_get(v___x_2529_, 4);
v_recordedDeps_2535_ = lean_ctor_get(v___x_2529_, 6);
v_messages_2536_ = lean_ctor_get(v___x_2529_, 7);
v_infoState_2537_ = lean_ctor_get(v___x_2529_, 8);
v_snapshotTasks_2538_ = lean_ctor_get(v___x_2529_, 9);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2562_ == 0)
{
lean_object* v_unused_2563_; 
v_unused_2563_ = lean_ctor_get(v___x_2529_, 5);
lean_dec(v_unused_2563_);
v___x_2540_ = v___x_2529_;
v_isShared_2541_ = v_isSharedCheck_2562_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_snapshotTasks_2538_);
lean_inc(v_infoState_2537_);
lean_inc(v_messages_2536_);
lean_inc(v_recordedDeps_2535_);
lean_inc(v_traceState_2534_);
lean_inc(v_auxDeclNGen_2533_);
lean_inc(v_ngen_2532_);
lean_inc(v_nextMacroScope_2531_);
lean_inc(v_env_2530_);
lean_dec(v___x_2529_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2562_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2542_; lean_object* v___x_2544_; 
v___x_2542_ = l_Lean_Kernel_enableDiag(v_env_2530_, v___y_2523_);
lean_inc_ref(v___y_2528_);
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 5, v___y_2528_);
lean_ctor_set(v___x_2540_, 0, v___x_2542_);
v___x_2544_ = v___x_2540_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2542_);
lean_ctor_set(v_reuseFailAlloc_2561_, 1, v_nextMacroScope_2531_);
lean_ctor_set(v_reuseFailAlloc_2561_, 2, v_ngen_2532_);
lean_ctor_set(v_reuseFailAlloc_2561_, 3, v_auxDeclNGen_2533_);
lean_ctor_set(v_reuseFailAlloc_2561_, 4, v_traceState_2534_);
lean_ctor_set(v_reuseFailAlloc_2561_, 5, v___y_2528_);
lean_ctor_set(v_reuseFailAlloc_2561_, 6, v_recordedDeps_2535_);
lean_ctor_set(v_reuseFailAlloc_2561_, 7, v_messages_2536_);
lean_ctor_set(v_reuseFailAlloc_2561_, 8, v_infoState_2537_);
lean_ctor_set(v_reuseFailAlloc_2561_, 9, v_snapshotTasks_2538_);
v___x_2544_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
lean_object* v___x_2545_; lean_object* v_toCold_2546_; lean_object* v_currRecDepth_2547_; lean_object* v_ref_2548_; uint8_t v_suppressElabErrors_2549_; uint8_t v_isRecordingDeps_2550_; lean_object* v_fileName_2551_; lean_object* v_fileMap_2552_; lean_object* v_currNamespace_2553_; lean_object* v_openDecls_2554_; lean_object* v_initHeartbeats_2555_; lean_object* v_maxHeartbeats_2556_; lean_object* v_quotContext_2557_; lean_object* v_currMacroScope_2558_; lean_object* v_cancelTk_x3f_2559_; lean_object* v_inheritedTraceOptions_2560_; 
v___x_2545_ = lean_st_ref_put(v___y_2527_, v___x_2544_);
v_toCold_2546_ = lean_ctor_get(v___y_2522_, 0);
lean_inc_ref(v_toCold_2546_);
v_currRecDepth_2547_ = lean_ctor_get(v___y_2522_, 1);
lean_inc(v_currRecDepth_2547_);
v_ref_2548_ = lean_ctor_get(v___y_2522_, 2);
lean_inc(v_ref_2548_);
v_suppressElabErrors_2549_ = lean_ctor_get_uint8(v___y_2522_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2550_ = lean_ctor_get_uint8(v___y_2522_, sizeof(void*)*3 + 3);
lean_dec_ref(v___y_2522_);
v_fileName_2551_ = lean_ctor_get(v_toCold_2546_, 0);
lean_inc_ref(v_fileName_2551_);
v_fileMap_2552_ = lean_ctor_get(v_toCold_2546_, 1);
lean_inc_ref(v_fileMap_2552_);
v_currNamespace_2553_ = lean_ctor_get(v_toCold_2546_, 4);
lean_inc(v_currNamespace_2553_);
v_openDecls_2554_ = lean_ctor_get(v_toCold_2546_, 5);
lean_inc(v_openDecls_2554_);
v_initHeartbeats_2555_ = lean_ctor_get(v_toCold_2546_, 6);
lean_inc(v_initHeartbeats_2555_);
v_maxHeartbeats_2556_ = lean_ctor_get(v_toCold_2546_, 7);
lean_inc(v_maxHeartbeats_2556_);
v_quotContext_2557_ = lean_ctor_get(v_toCold_2546_, 8);
lean_inc(v_quotContext_2557_);
v_currMacroScope_2558_ = lean_ctor_get(v_toCold_2546_, 9);
lean_inc(v_currMacroScope_2558_);
v_cancelTk_x3f_2559_ = lean_ctor_get(v_toCold_2546_, 10);
lean_inc(v_cancelTk_x3f_2559_);
v_inheritedTraceOptions_2560_ = lean_ctor_get(v_toCold_2546_, 11);
lean_inc_ref(v_inheritedTraceOptions_2560_);
lean_dec_ref(v_toCold_2546_);
lean_inc(v___y_2527_);
v___y_2468_ = v___y_2519_;
v___y_2469_ = v___y_2520_;
v___y_2470_ = v___y_2521_;
v___y_2471_ = v___y_2524_;
v___y_2472_ = v___y_2525_;
v___y_2473_ = v___y_2527_;
v___y_2474_ = v___y_2526_;
v_fileName_2475_ = v_fileName_2551_;
v_fileMap_2476_ = v_fileMap_2552_;
v_currNamespace_2477_ = v_currNamespace_2553_;
v_openDecls_2478_ = v_openDecls_2554_;
v_initHeartbeats_2479_ = v_initHeartbeats_2555_;
v_maxHeartbeats_2480_ = v_maxHeartbeats_2556_;
v_quotContext_2481_ = v_quotContext_2557_;
v_currMacroScope_2482_ = v_currMacroScope_2558_;
v_cancelTk_x3f_2483_ = v_cancelTk_x3f_2559_;
v_inheritedTraceOptions_2484_ = v_inheritedTraceOptions_2560_;
v_currRecDepth_2485_ = v_currRecDepth_2547_;
v_ref_2486_ = v_ref_2548_;
v_suppressElabErrors_2487_ = v_suppressElabErrors_2549_;
v_isRecordingDeps_2488_ = v_isRecordingDeps_2550_;
v___y_2489_ = v___y_2527_;
goto v___jp_2467_;
}
}
}
v___jp_2564_:
{
if (v___y_2565_ == 0)
{
uint8_t v___x_2566_; uint8_t v___x_2567_; 
lean_dec(v_pkgRoot_2405_);
lean_dec_ref(v_env_2404_);
lean_dec(v_sp_2403_);
v___x_2566_ = 1;
v___x_2567_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_2465_, v___x_2566_);
if (v___x_2567_ == 0)
{
lean_object* v___x_2568_; 
v___x_2568_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2568_, 0, v___x_2567_);
v___y_2409_ = v___x_2568_;
goto v___jp_2408_;
}
else
{
lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2569_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_2570_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2570_, 0, v___x_2569_);
lean_ctor_set_uint8(v___x_2570_, sizeof(void*)*1, v___y_2565_);
v___y_2409_ = v___x_2570_;
goto v___jp_2408_;
}
}
else
{
lean_object* v___x_2571_; lean_object* v___f_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; uint16_t v___x_2584_; uint8_t v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v_env_2603_; uint8_t v___x_2604_; uint8_t v___x_2605_; 
v___x_2571_ = lean_box(v___y_2565_);
lean_inc(v_docCheckedModules_2406_);
lean_inc(v_pkgRoot_2405_);
v___f_2572_ = lean_alloc_closure((void*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2572_, 0, v_pkgRoot_2405_);
lean_closure_set(v___f_2572_, 1, v_docCheckedModules_2406_);
lean_closure_set(v___f_2572_, 2, v___x_2571_);
v___x_2573_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_2574_ = l_Lean_instInhabitedFileMap_default;
v___x_2575_ = l_Lean_Options_empty;
v___x_2576_ = lean_unsigned_to_nat(1000u);
v___x_2577_ = lean_box(0);
v___x_2578_ = lean_box(0);
v___x_2579_ = lean_unsigned_to_nat(0u);
v___x_2580_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5);
v___x_2581_ = l_Lean_firstFrontendMacroScope;
v___x_2582_ = lean_box(0);
v___x_2583_ = lean_box(0);
v___x_2584_ = lean_uint16_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_2585_ = 0;
v___x_2586_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7);
v___x_2587_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10));
v___x_2588_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11));
v___x_2589_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14);
v___x_2590_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_2591_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___closed__0));
v___x_2592_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18);
v___x_2593_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_2594_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
lean_inc_ref(v_env_2404_);
v___x_2595_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2595_, 0, v_env_2404_);
lean_ctor_set(v___x_2595_, 1, v___x_2586_);
lean_ctor_set(v___x_2595_, 2, v___x_2587_);
lean_ctor_set(v___x_2595_, 3, v___x_2588_);
lean_ctor_set(v___x_2595_, 4, v___x_2589_);
lean_ctor_set(v___x_2595_, 5, v___x_2590_);
lean_ctor_set(v___x_2595_, 6, v___x_2592_);
lean_ctor_set(v___x_2595_, 7, v___x_2593_);
lean_ctor_set(v___x_2595_, 8, v___x_2594_);
lean_ctor_set(v___x_2595_, 9, v___x_2591_);
v___x_2596_ = lean_io_get_num_heartbeats();
v___x_2597_ = lean_st_mk_ref(v___x_2595_);
v___x_2598_ = l_Lean_inheritedTraceOptions;
v___x_2599_ = lean_st_ref_get(v___x_2598_);
lean_inc(v___x_2599_);
lean_inc(v___x_2596_);
v___x_2600_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2573_);
lean_ctor_set(v___x_2600_, 1, v___x_2574_);
lean_ctor_set(v___x_2600_, 2, v___x_2575_);
lean_ctor_set(v___x_2600_, 3, v___x_2576_);
lean_ctor_set(v___x_2600_, 4, v___x_2577_);
lean_ctor_set(v___x_2600_, 5, v___x_2578_);
lean_ctor_set(v___x_2600_, 6, v___x_2596_);
lean_ctor_set(v___x_2600_, 7, v___x_2580_);
lean_ctor_set(v___x_2600_, 8, v___x_2577_);
lean_ctor_set(v___x_2600_, 9, v___x_2581_);
lean_ctor_set(v___x_2600_, 10, v___x_2582_);
lean_ctor_set(v___x_2600_, 11, v___x_2599_);
v___x_2601_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
lean_ctor_set(v___x_2601_, 1, v___x_2579_);
lean_ctor_set(v___x_2601_, 2, v___x_2583_);
lean_ctor_set_uint16(v___x_2601_, sizeof(void*)*3, v___x_2584_);
lean_ctor_set_uint8(v___x_2601_, sizeof(void*)*3 + 2, v___x_2585_);
lean_ctor_set_uint8(v___x_2601_, sizeof(void*)*3 + 3, v___x_2585_);
v___x_2602_ = lean_st_ref_get(v___x_2597_);
v_env_2603_ = lean_ctor_get(v___x_2602_, 0);
lean_inc_ref(v_env_2603_);
lean_dec(v___x_2602_);
v___x_2604_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2603_);
lean_dec_ref(v_env_2603_);
v___x_2605_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22);
if (v___x_2605_ == 0)
{
if (v___x_2604_ == 0)
{
lean_dec(v___x_2599_);
lean_dec(v___x_2596_);
v___y_2519_ = v___x_2585_;
v___y_2520_ = v___f_2572_;
v___y_2521_ = v___y_2565_;
v___y_2522_ = v___x_2601_;
v___y_2523_ = v___y_2565_;
v___y_2524_ = v___x_2579_;
v___y_2525_ = v___x_2575_;
v___y_2526_ = v___x_2584_;
v___y_2527_ = v___x_2597_;
v___y_2528_ = v___x_2590_;
goto v___jp_2518_;
}
else
{
lean_dec_ref_known(v___x_2601_, 3);
lean_inc(v___x_2597_);
v___y_2468_ = v___x_2585_;
v___y_2469_ = v___f_2572_;
v___y_2470_ = v___y_2565_;
v___y_2471_ = v___x_2579_;
v___y_2472_ = v___x_2575_;
v___y_2473_ = v___x_2597_;
v___y_2474_ = v___x_2584_;
v_fileName_2475_ = v___x_2573_;
v_fileMap_2476_ = v___x_2574_;
v_currNamespace_2477_ = v___x_2577_;
v_openDecls_2478_ = v___x_2578_;
v_initHeartbeats_2479_ = v___x_2596_;
v_maxHeartbeats_2480_ = v___x_2580_;
v_quotContext_2481_ = v___x_2577_;
v_currMacroScope_2482_ = v___x_2581_;
v_cancelTk_x3f_2483_ = v___x_2582_;
v_inheritedTraceOptions_2484_ = v___x_2599_;
v_currRecDepth_2485_ = v___x_2579_;
v_ref_2486_ = v___x_2583_;
v_suppressElabErrors_2487_ = v___x_2585_;
v_isRecordingDeps_2488_ = v___x_2585_;
v___y_2489_ = v___x_2597_;
goto v___jp_2467_;
}
}
else
{
if (v___x_2604_ == 0)
{
lean_dec_ref_known(v___x_2601_, 3);
lean_inc(v___x_2597_);
v___y_2468_ = v___x_2585_;
v___y_2469_ = v___f_2572_;
v___y_2470_ = v___y_2565_;
v___y_2471_ = v___x_2579_;
v___y_2472_ = v___x_2575_;
v___y_2473_ = v___x_2597_;
v___y_2474_ = v___x_2584_;
v_fileName_2475_ = v___x_2573_;
v_fileMap_2476_ = v___x_2574_;
v_currNamespace_2477_ = v___x_2577_;
v_openDecls_2478_ = v___x_2578_;
v_initHeartbeats_2479_ = v___x_2596_;
v_maxHeartbeats_2480_ = v___x_2580_;
v_quotContext_2481_ = v___x_2577_;
v_currMacroScope_2482_ = v___x_2581_;
v_cancelTk_x3f_2483_ = v___x_2582_;
v_inheritedTraceOptions_2484_ = v___x_2599_;
v_currRecDepth_2485_ = v___x_2579_;
v_ref_2486_ = v___x_2583_;
v_suppressElabErrors_2487_ = v___x_2585_;
v_isRecordingDeps_2488_ = v___x_2585_;
v___y_2489_ = v___x_2597_;
goto v___jp_2467_;
}
else
{
lean_dec(v___x_2599_);
lean_dec(v___x_2596_);
v___y_2519_ = v___x_2585_;
v___y_2520_ = v___f_2572_;
v___y_2521_ = v___y_2565_;
v___y_2522_ = v___x_2601_;
v___y_2523_ = v___x_2585_;
v___y_2524_ = v___x_2579_;
v___y_2525_ = v___x_2575_;
v___y_2526_ = v___x_2584_;
v___y_2527_ = v___x_2597_;
v___y_2528_ = v___x_2590_;
goto v___jp_2518_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___boxed(lean_object* v_args_2611_, lean_object* v_linterOpts_2612_, lean_object* v_sp_2613_, lean_object* v_env_2614_, lean_object* v_pkgRoot_2615_, lean_object* v_docCheckedModules_2616_, lean_object* v_a_2617_){
_start:
{
lean_object* v_res_2618_; 
v_res_2618_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(v_args_2611_, v_linterOpts_2612_, v_sp_2613_, v_env_2614_, v_pkgRoot_2615_, v_docCheckedModules_2616_);
lean_dec_ref(v_linterOpts_2612_);
lean_dec_ref(v_args_2611_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(lean_object* v_sp_2619_, uint8_t v___y_2620_, lean_object* v_as_2621_, size_t v_sz_2622_, size_t v_i_2623_, lean_object* v_b_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_){
_start:
{
lean_object* v___x_2628_; 
v___x_2628_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg(v_sp_2619_, v___y_2620_, v_as_2621_, v_sz_2622_, v_i_2623_, v_b_2624_, v___y_2625_);
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___boxed(lean_object* v_sp_2629_, lean_object* v___y_2630_, lean_object* v_as_2631_, lean_object* v_sz_2632_, lean_object* v_i_2633_, lean_object* v_b_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
uint8_t v___y_8586__boxed_2638_; size_t v_sz_boxed_2639_; size_t v_i_boxed_2640_; lean_object* v_res_2641_; 
v___y_8586__boxed_2638_ = lean_unbox(v___y_2630_);
v_sz_boxed_2639_ = lean_unbox_usize(v_sz_2632_);
lean_dec(v_sz_2632_);
v_i_boxed_2640_ = lean_unbox_usize(v_i_2633_);
lean_dec(v_i_2633_);
v_res_2641_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(v_sp_2629_, v___y_8586__boxed_2638_, v_as_2631_, v_sz_boxed_2639_, v_i_boxed_2640_, v_b_2634_, v___y_2635_, v___y_2636_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec_ref(v_as_2631_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(lean_object* v_linterOpts_2642_, lean_object* v_as_2643_, size_t v_i_2644_, size_t v_stop_2645_, lean_object* v_b_2646_){
_start:
{
lean_object* v___y_2648_; uint8_t v___x_2652_; 
v___x_2652_ = lean_usize_dec_eq(v_i_2644_, v_stop_2645_);
if (v___x_2652_ == 0)
{
lean_object* v___x_2653_; lean_object* v_linter_2654_; uint8_t v___x_2655_; 
v___x_2653_ = lean_array_uget_borrowed(v_as_2643_, v_i_2644_);
v_linter_2654_ = lean_ctor_get(v___x_2653_, 0);
v___x_2655_ = l_Lean_Linter_isLinterEnabledByOptions(v_linter_2654_, v_linterOpts_2642_);
if (v___x_2655_ == 0)
{
v___y_2648_ = v_b_2646_;
goto v___jp_2647_;
}
else
{
lean_object* v___x_2656_; 
lean_inc(v___x_2653_);
v___x_2656_ = lean_array_push(v_b_2646_, v___x_2653_);
v___y_2648_ = v___x_2656_;
goto v___jp_2647_;
}
}
else
{
return v_b_2646_;
}
v___jp_2647_:
{
size_t v___x_2649_; size_t v___x_2650_; 
v___x_2649_ = ((size_t)1ULL);
v___x_2650_ = lean_usize_add(v_i_2644_, v___x_2649_);
v_i_2644_ = v___x_2650_;
v_b_2646_ = v___y_2648_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1___boxed(lean_object* v_linterOpts_2657_, lean_object* v_as_2658_, lean_object* v_i_2659_, lean_object* v_stop_2660_, lean_object* v_b_2661_){
_start:
{
size_t v_i_boxed_2662_; size_t v_stop_boxed_2663_; lean_object* v_res_2664_; 
v_i_boxed_2662_ = lean_unbox_usize(v_i_2659_);
lean_dec(v_i_2659_);
v_stop_boxed_2663_ = lean_unbox_usize(v_stop_2660_);
lean_dec(v_stop_2660_);
v_res_2664_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(v_linterOpts_2657_, v_as_2658_, v_i_boxed_2662_, v_stop_boxed_2663_, v_b_2661_);
lean_dec_ref(v_as_2658_);
lean_dec_ref(v_linterOpts_2657_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(lean_object* v_linterOpts_2667_, lean_object* v_as_2668_, size_t v_i_2669_, size_t v_stop_2670_, lean_object* v_b_2671_){
_start:
{
lean_object* v___y_2673_; uint8_t v___x_2677_; 
v___x_2677_ = lean_usize_dec_eq(v_i_2669_, v_stop_2670_);
if (v___x_2677_ == 0)
{
lean_object* v___x_2678_; lean_object* v_fst_2679_; lean_object* v_snd_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2704_; 
v___x_2678_ = lean_array_uget(v_as_2668_, v_i_2669_);
v_fst_2679_ = lean_ctor_get(v___x_2678_, 0);
v_snd_2680_ = lean_ctor_get(v___x_2678_, 1);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2682_ = v___x_2678_;
v_isShared_2683_ = v_isSharedCheck_2704_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_snd_2680_);
lean_inc(v_fst_2679_);
lean_dec(v___x_2678_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2704_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___y_2685_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; uint8_t v___x_2696_; 
v___x_2693_ = lean_unsigned_to_nat(0u);
v___x_2694_ = lean_array_get_size(v_snd_2680_);
v___x_2695_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9___closed__0));
v___x_2696_ = lean_nat_dec_lt(v___x_2693_, v___x_2694_);
if (v___x_2696_ == 0)
{
lean_dec(v_snd_2680_);
v___y_2685_ = v___x_2695_;
goto v___jp_2684_;
}
else
{
uint8_t v___x_2697_; 
v___x_2697_ = lean_nat_dec_le(v___x_2694_, v___x_2694_);
if (v___x_2697_ == 0)
{
if (v___x_2696_ == 0)
{
lean_dec(v_snd_2680_);
v___y_2685_ = v___x_2695_;
goto v___jp_2684_;
}
else
{
size_t v___x_2698_; size_t v___x_2699_; lean_object* v___x_2700_; 
v___x_2698_ = ((size_t)0ULL);
v___x_2699_ = lean_usize_of_nat(v___x_2694_);
v___x_2700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(v_linterOpts_2667_, v_snd_2680_, v___x_2698_, v___x_2699_, v___x_2695_);
lean_dec(v_snd_2680_);
v___y_2685_ = v___x_2700_;
goto v___jp_2684_;
}
}
else
{
size_t v___x_2701_; size_t v___x_2702_; lean_object* v___x_2703_; 
v___x_2701_ = ((size_t)0ULL);
v___x_2702_ = lean_usize_of_nat(v___x_2694_);
v___x_2703_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(v_linterOpts_2667_, v_snd_2680_, v___x_2701_, v___x_2702_, v___x_2695_);
lean_dec(v_snd_2680_);
v___y_2685_ = v___x_2703_;
goto v___jp_2684_;
}
}
v___jp_2684_:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; uint8_t v___x_2688_; 
v___x_2686_ = lean_array_get_size(v___y_2685_);
v___x_2687_ = lean_unsigned_to_nat(0u);
v___x_2688_ = lean_nat_dec_eq(v___x_2686_, v___x_2687_);
if (v___x_2688_ == 0)
{
lean_object* v___x_2690_; 
if (v_isShared_2683_ == 0)
{
lean_ctor_set(v___x_2682_, 1, v___y_2685_);
v___x_2690_ = v___x_2682_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_fst_2679_);
lean_ctor_set(v_reuseFailAlloc_2692_, 1, v___y_2685_);
v___x_2690_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
lean_object* v___x_2691_; 
v___x_2691_ = lean_array_push(v_b_2671_, v___x_2690_);
v___y_2673_ = v___x_2691_;
goto v___jp_2672_;
}
}
else
{
lean_dec_ref(v___y_2685_);
lean_del_object(v___x_2682_);
lean_dec(v_fst_2679_);
v___y_2673_ = v_b_2671_;
goto v___jp_2672_;
}
}
}
}
else
{
return v_b_2671_;
}
v___jp_2672_:
{
size_t v___x_2674_; size_t v___x_2675_; 
v___x_2674_ = ((size_t)1ULL);
v___x_2675_ = lean_usize_add(v_i_2669_, v___x_2674_);
v_i_2669_ = v___x_2675_;
v_b_2671_ = v___y_2673_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9___boxed(lean_object* v_linterOpts_2705_, lean_object* v_as_2706_, lean_object* v_i_2707_, lean_object* v_stop_2708_, lean_object* v_b_2709_){
_start:
{
size_t v_i_boxed_2710_; size_t v_stop_boxed_2711_; lean_object* v_res_2712_; 
v_i_boxed_2710_ = lean_unbox_usize(v_i_2707_);
lean_dec(v_i_2707_);
v_stop_boxed_2711_ = lean_unbox_usize(v_stop_2708_);
lean_dec(v_stop_2708_);
v_res_2712_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2705_, v_as_2706_, v_i_boxed_2710_, v_stop_boxed_2711_, v_b_2709_);
lean_dec_ref(v_as_2706_);
lean_dec_ref(v_linterOpts_2705_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(lean_object* v_linterOpts_2713_, lean_object* v_as_2714_, lean_object* v_start_2715_, lean_object* v_stop_2716_){
_start:
{
lean_object* v___x_2717_; uint8_t v___x_2718_; 
v___x_2717_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0));
v___x_2718_ = lean_nat_dec_lt(v_start_2715_, v_stop_2716_);
if (v___x_2718_ == 0)
{
return v___x_2717_;
}
else
{
lean_object* v___x_2719_; uint8_t v___x_2720_; 
v___x_2719_ = lean_array_get_size(v_as_2714_);
v___x_2720_ = lean_nat_dec_le(v_stop_2716_, v___x_2719_);
if (v___x_2720_ == 0)
{
uint8_t v___x_2721_; 
v___x_2721_ = lean_nat_dec_lt(v_start_2715_, v___x_2719_);
if (v___x_2721_ == 0)
{
return v___x_2717_;
}
else
{
size_t v___x_2722_; size_t v___x_2723_; lean_object* v___x_2724_; 
v___x_2722_ = lean_usize_of_nat(v_start_2715_);
v___x_2723_ = lean_usize_of_nat(v___x_2719_);
v___x_2724_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2713_, v_as_2714_, v___x_2722_, v___x_2723_, v___x_2717_);
return v___x_2724_;
}
}
else
{
size_t v___x_2725_; size_t v___x_2726_; lean_object* v___x_2727_; 
v___x_2725_ = lean_usize_of_nat(v_start_2715_);
v___x_2726_ = lean_usize_of_nat(v_stop_2716_);
v___x_2727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2713_, v_as_2714_, v___x_2725_, v___x_2726_, v___x_2717_);
return v___x_2727_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9___boxed(lean_object* v_linterOpts_2728_, lean_object* v_as_2729_, lean_object* v_start_2730_, lean_object* v_stop_2731_){
_start:
{
lean_object* v_res_2732_; 
v_res_2732_ = l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(v_linterOpts_2728_, v_as_2729_, v_start_2730_, v_stop_2731_);
lean_dec(v_stop_2731_);
lean_dec(v_start_2730_);
lean_dec_ref(v_as_2729_);
lean_dec_ref(v_linterOpts_2728_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(lean_object* v_fst_2733_, lean_object* v_init_2734_, lean_object* v_x_2735_){
_start:
{
if (lean_obj_tag(v_x_2735_) == 0)
{
lean_object* v_k_2737_; lean_object* v_v_2738_; lean_object* v_l_2739_; lean_object* v_r_2740_; uint8_t v_anyUnlocated_2741_; lean_object* v___x_2742_; lean_object* v_a_2743_; lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2757_; 
v_k_2737_ = lean_ctor_get(v_x_2735_, 1);
lean_inc(v_k_2737_);
v_v_2738_ = lean_ctor_get(v_x_2735_, 2);
lean_inc(v_v_2738_);
v_l_2739_ = lean_ctor_get(v_x_2735_, 3);
lean_inc(v_l_2739_);
v_r_2740_ = lean_ctor_get(v_x_2735_, 4);
lean_inc(v_r_2740_);
lean_dec_ref_known(v_x_2735_, 5);
v_anyUnlocated_2741_ = 1;
lean_inc(v_fst_2733_);
v___x_2742_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2733_, v_init_2734_, v_l_2739_);
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
lean_inc(v_a_2743_);
lean_dec_ref(v___x_2742_);
v_a_2744_ = lean_ctor_get(v_a_2743_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v_a_2743_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2746_ = v_a_2743_;
v_isShared_2747_ = v_isSharedCheck_2757_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v_a_2743_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2757_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2748_; lean_object* v___x_2750_; 
v___x_2748_ = l_Lean_Name_toString(v_k_2737_, v_anyUnlocated_2741_);
lean_inc(v_fst_2733_);
if (v_isShared_2747_ == 0)
{
lean_ctor_set_tag(v___x_2746_, 0);
lean_ctor_set(v___x_2746_, 0, v_fst_2733_);
v___x_2750_ = v___x_2746_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_fst_2733_);
v___x_2750_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
double v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2751_ = lean_float_of_nat(v_v_2738_);
v___x_2752_ = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_float(v___x_2752_, 0, v___x_2751_);
v___x_2753_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2748_);
lean_ctor_set(v___x_2753_, 1, v___x_2750_);
lean_ctor_set(v___x_2753_, 2, v___x_2752_);
v___x_2754_ = lean_array_push(v_a_2744_, v___x_2753_);
v_init_2734_ = v___x_2754_;
v_x_2735_ = v_r_2740_;
goto _start;
}
}
}
else
{
lean_object* v___x_2758_; lean_object* v___x_2759_; 
lean_dec(v_fst_2733_);
v___x_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2758_, 0, v_init_2734_);
v___x_2759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2758_);
return v___x_2759_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3___boxed(lean_object* v_fst_2760_, lean_object* v_init_2761_, lean_object* v_x_2762_, lean_object* v___y_2763_){
_start:
{
lean_object* v_res_2764_; 
v_res_2764_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2760_, v_init_2761_, v_x_2762_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(lean_object* v_t_2765_, lean_object* v_k_2766_, lean_object* v_fallback_2767_){
_start:
{
if (lean_obj_tag(v_t_2765_) == 0)
{
lean_object* v_k_2768_; lean_object* v_v_2769_; lean_object* v_l_2770_; lean_object* v_r_2771_; uint8_t v___x_2772_; 
v_k_2768_ = lean_ctor_get(v_t_2765_, 1);
v_v_2769_ = lean_ctor_get(v_t_2765_, 2);
v_l_2770_ = lean_ctor_get(v_t_2765_, 3);
v_r_2771_ = lean_ctor_get(v_t_2765_, 4);
v___x_2772_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2766_, v_k_2768_);
switch(v___x_2772_)
{
case 0:
{
v_t_2765_ = v_l_2770_;
goto _start;
}
case 1:
{
lean_inc(v_v_2769_);
return v_v_2769_;
}
default: 
{
v_t_2765_ = v_r_2771_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2767_);
return v_fallback_2767_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg___boxed(lean_object* v_t_2775_, lean_object* v_k_2776_, lean_object* v_fallback_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(v_t_2775_, v_k_2776_, v_fallback_2777_);
lean_dec(v_fallback_2777_);
lean_dec(v_k_2776_);
lean_dec(v_t_2775_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(lean_object* v_as_2779_, size_t v_i_2780_, size_t v_stop_2781_, lean_object* v_b_2782_){
_start:
{
uint8_t v___x_2783_; 
v___x_2783_ = lean_usize_dec_eq(v_i_2780_, v_stop_2781_);
if (v___x_2783_ == 0)
{
lean_object* v___x_2784_; lean_object* v_linter_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; size_t v___x_2791_; size_t v___x_2792_; 
v___x_2784_ = lean_array_uget_borrowed(v_as_2779_, v_i_2780_);
v_linter_2785_ = lean_ctor_get(v___x_2784_, 0);
v___x_2786_ = lean_unsigned_to_nat(0u);
v___x_2787_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(v_b_2782_, v_linter_2785_, v___x_2786_);
v___x_2788_ = lean_unsigned_to_nat(1u);
v___x_2789_ = lean_nat_add(v___x_2787_, v___x_2788_);
lean_dec(v___x_2787_);
lean_inc(v_linter_2785_);
v___x_2790_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_linter_2785_, v___x_2789_, v_b_2782_);
v___x_2791_ = ((size_t)1ULL);
v___x_2792_ = lean_usize_add(v_i_2780_, v___x_2791_);
v_i_2780_ = v___x_2792_;
v_b_2782_ = v___x_2790_;
goto _start;
}
else
{
return v_b_2782_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4___boxed(lean_object* v_as_2794_, lean_object* v_i_2795_, lean_object* v_stop_2796_, lean_object* v_b_2797_){
_start:
{
size_t v_i_boxed_2798_; size_t v_stop_boxed_2799_; lean_object* v_res_2800_; 
v_i_boxed_2798_ = lean_unbox_usize(v_i_2795_);
lean_dec(v_i_2795_);
v_stop_boxed_2799_ = lean_unbox_usize(v_stop_2796_);
lean_dec(v_stop_2796_);
v_res_2800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_as_2794_, v_i_boxed_2798_, v_stop_boxed_2799_, v_b_2797_);
lean_dec_ref(v_as_2794_);
return v_res_2800_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(lean_object* v_as_2801_, size_t v_sz_2802_, size_t v_i_2803_, lean_object* v_b_2804_){
_start:
{
lean_object* v_a_2807_; uint8_t v___x_2811_; 
v___x_2811_ = lean_usize_dec_lt(v_i_2803_, v_sz_2802_);
if (v___x_2811_ == 0)
{
lean_object* v___x_2812_; 
v___x_2812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2812_, 0, v_b_2804_);
return v___x_2812_;
}
else
{
lean_object* v_a_2813_; lean_object* v_fst_2814_; lean_object* v_snd_2815_; lean_object* v___y_2817_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; uint8_t v___x_2842_; 
v_a_2813_ = lean_array_uget_borrowed(v_as_2801_, v_i_2803_);
v_fst_2814_ = lean_ctor_get(v_a_2813_, 0);
v_snd_2815_ = lean_ctor_get(v_a_2813_, 1);
v___x_2839_ = lean_box(1);
v___x_2840_ = lean_unsigned_to_nat(0u);
v___x_2841_ = lean_array_get_size(v_snd_2815_);
v___x_2842_ = lean_nat_dec_lt(v___x_2840_, v___x_2841_);
if (v___x_2842_ == 0)
{
v___y_2817_ = v___x_2839_;
goto v___jp_2816_;
}
else
{
uint8_t v___x_2843_; 
v___x_2843_ = lean_nat_dec_le(v___x_2841_, v___x_2841_);
if (v___x_2843_ == 0)
{
if (v___x_2842_ == 0)
{
v___y_2817_ = v___x_2839_;
goto v___jp_2816_;
}
else
{
size_t v___x_2844_; size_t v___x_2845_; lean_object* v___x_2846_; 
v___x_2844_ = ((size_t)0ULL);
v___x_2845_ = lean_usize_of_nat(v___x_2841_);
v___x_2846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_snd_2815_, v___x_2844_, v___x_2845_, v___x_2839_);
v___y_2817_ = v___x_2846_;
goto v___jp_2816_;
}
}
else
{
size_t v___x_2847_; size_t v___x_2848_; lean_object* v___x_2849_; 
v___x_2847_ = ((size_t)0ULL);
v___x_2848_ = lean_usize_of_nat(v___x_2841_);
v___x_2849_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_snd_2815_, v___x_2847_, v___x_2848_, v___x_2839_);
v___y_2817_ = v___x_2849_;
goto v___jp_2816_;
}
}
v___jp_2816_:
{
lean_object* v___x_2818_; 
lean_inc(v_fst_2814_);
v___x_2818_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2814_, v_b_2804_, v___y_2817_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; lean_object* v_a_2820_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2819_);
lean_dec_ref_known(v___x_2818_, 1);
v_a_2820_ = lean_ctor_get(v_a_2819_, 0);
lean_inc(v_a_2820_);
lean_dec(v_a_2819_);
v_a_2807_ = v_a_2820_;
goto v___jp_2806_;
}
else
{
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2830_; 
v_a_2821_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2823_ = v___x_2818_;
v_isShared_2824_ = v_isSharedCheck_2830_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_a_2821_);
lean_dec(v___x_2818_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2830_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
if (lean_obj_tag(v_a_2821_) == 0)
{
lean_object* v_a_2825_; lean_object* v___x_2827_; 
v_a_2825_ = lean_ctor_get(v_a_2821_, 0);
lean_inc(v_a_2825_);
lean_dec_ref_known(v_a_2821_, 1);
if (v_isShared_2824_ == 0)
{
lean_ctor_set_tag(v___x_2823_, 0);
lean_ctor_set(v___x_2823_, 0, v_a_2825_);
v___x_2827_ = v___x_2823_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_a_2825_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
else
{
lean_object* v_a_2829_; 
lean_del_object(v___x_2823_);
v_a_2829_ = lean_ctor_get(v_a_2821_, 0);
lean_inc(v_a_2829_);
lean_dec_ref_known(v_a_2821_, 1);
v_a_2807_ = v_a_2829_;
goto v___jp_2806_;
}
}
}
else
{
lean_object* v_a_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2838_; 
v_a_2831_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2833_ = v___x_2818_;
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_dec(v___x_2818_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2836_; 
if (v_isShared_2834_ == 0)
{
v___x_2836_ = v___x_2833_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_a_2831_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
}
}
}
}
v___jp_2806_:
{
size_t v___x_2808_; size_t v___x_2809_; 
v___x_2808_ = ((size_t)1ULL);
v___x_2809_ = lean_usize_add(v_i_2803_, v___x_2808_);
v_i_2803_ = v___x_2809_;
v_b_2804_ = v_a_2807_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8___boxed(lean_object* v_as_2850_, lean_object* v_sz_2851_, lean_object* v_i_2852_, lean_object* v_b_2853_, lean_object* v___y_2854_){
_start:
{
size_t v_sz_boxed_2855_; size_t v_i_boxed_2856_; lean_object* v_res_2857_; 
v_sz_boxed_2855_ = lean_unbox_usize(v_sz_2851_);
lean_dec(v_sz_2851_);
v_i_boxed_2856_ = lean_unbox_usize(v_i_2852_);
lean_dec(v_i_2852_);
v_res_2857_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(v_as_2850_, v_sz_boxed_2855_, v_i_boxed_2856_, v_b_2853_);
lean_dec_ref(v_as_2850_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(lean_object* v_fst_2861_, lean_object* v_as_2862_, size_t v_sz_2863_, size_t v_i_2864_, lean_object* v_b_2865_){
_start:
{
lean_object* v_a_2868_; uint8_t v_anyUnlocated_2872_; 
v_anyUnlocated_2872_ = lean_usize_dec_lt(v_i_2864_, v_sz_2863_);
if (v_anyUnlocated_2872_ == 0)
{
lean_object* v___x_2873_; 
lean_dec(v_fst_2861_);
v___x_2873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2873_, 0, v_b_2865_);
return v___x_2873_;
}
else
{
lean_object* v_fst_2874_; lean_object* v_snd_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2912_; 
v_fst_2874_ = lean_ctor_get(v_b_2865_, 0);
v_snd_2875_ = lean_ctor_get(v_b_2865_, 1);
v_isSharedCheck_2912_ = !lean_is_exclusive(v_b_2865_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2877_ = v_b_2865_;
v_isShared_2878_ = v_isSharedCheck_2912_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_snd_2875_);
lean_inc(v_fst_2874_);
lean_dec(v_b_2865_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2912_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v_a_2879_; lean_object* v_position_x3f_2880_; 
v_a_2879_ = lean_array_uget_borrowed(v_as_2862_, v_i_2864_);
v_position_x3f_2880_ = lean_ctor_get(v_a_2879_, 2);
if (lean_obj_tag(v_position_x3f_2880_) == 0)
{
lean_object* v_linter_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
lean_dec(v_snd_2875_);
v_linter_2881_ = lean_ctor_get(v_a_2879_, 0);
v___x_2882_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__0));
lean_inc(v_linter_2881_);
v___x_2883_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_linter_2881_, v_anyUnlocated_2872_);
v___x_2884_ = lean_string_append(v___x_2882_, v___x_2883_);
lean_dec_ref(v___x_2883_);
v___x_2885_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__1));
v___x_2886_ = lean_string_append(v___x_2884_, v___x_2885_);
lean_inc(v_fst_2861_);
v___x_2887_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2861_, v_anyUnlocated_2872_);
v___x_2888_ = lean_string_append(v___x_2886_, v___x_2887_);
lean_dec_ref(v___x_2887_);
v___x_2889_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__2));
v___x_2890_ = lean_string_append(v___x_2888_, v___x_2889_);
v___x_2891_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2890_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v___x_2892_; lean_object* v___x_2894_; 
lean_dec_ref_known(v___x_2891_, 1);
v___x_2892_ = lean_box(v_anyUnlocated_2872_);
if (v_isShared_2878_ == 0)
{
lean_ctor_set(v___x_2877_, 1, v___x_2892_);
v___x_2894_ = v___x_2877_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_fst_2874_);
lean_ctor_set(v_reuseFailAlloc_2895_, 1, v___x_2892_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
v_a_2868_ = v___x_2894_;
goto v___jp_2867_;
}
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
lean_del_object(v___x_2877_);
lean_dec(v_fst_2874_);
lean_dec(v_fst_2861_);
v_a_2896_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2891_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2891_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
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
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
else
{
lean_object* v_linter_2904_; lean_object* v_file_2905_; lean_object* v_val_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2910_; 
v_linter_2904_ = lean_ctor_get(v_a_2879_, 0);
v_file_2905_ = lean_ctor_get(v_a_2879_, 3);
v_val_2906_ = lean_ctor_get(v_position_x3f_2880_, 0);
lean_inc(v_linter_2904_);
lean_inc(v_val_2906_);
lean_inc_ref(v_file_2905_);
v___x_2907_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2907_, 0, v_file_2905_);
lean_ctor_set(v___x_2907_, 1, v_val_2906_);
lean_ctor_set(v___x_2907_, 2, v_linter_2904_);
v___x_2908_ = lean_array_push(v_fst_2874_, v___x_2907_);
if (v_isShared_2878_ == 0)
{
lean_ctor_set(v___x_2877_, 0, v___x_2908_);
v___x_2910_ = v___x_2877_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v___x_2908_);
lean_ctor_set(v_reuseFailAlloc_2911_, 1, v_snd_2875_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
v_a_2868_ = v___x_2910_;
goto v___jp_2867_;
}
}
}
}
v___jp_2867_:
{
size_t v___x_2869_; size_t v___x_2870_; 
v___x_2869_ = ((size_t)1ULL);
v___x_2870_ = lean_usize_add(v_i_2864_, v___x_2869_);
v_i_2864_ = v___x_2870_;
v_b_2865_ = v_a_2868_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___boxed(lean_object* v_fst_2913_, lean_object* v_as_2914_, lean_object* v_sz_2915_, lean_object* v_i_2916_, lean_object* v_b_2917_, lean_object* v___y_2918_){
_start:
{
size_t v_sz_boxed_2919_; size_t v_i_boxed_2920_; lean_object* v_res_2921_; 
v_sz_boxed_2919_ = lean_unbox_usize(v_sz_2915_);
lean_dec(v_sz_2915_);
v_i_boxed_2920_ = lean_unbox_usize(v_i_2916_);
lean_dec(v_i_2916_);
v_res_2921_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(v_fst_2913_, v_as_2914_, v_sz_boxed_2919_, v_i_boxed_2920_, v_b_2917_);
lean_dec_ref(v_as_2914_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(lean_object* v_as_2922_, size_t v_sz_2923_, size_t v_i_2924_, lean_object* v_b_2925_){
_start:
{
uint8_t v___x_2927_; 
v___x_2927_ = lean_usize_dec_lt(v_i_2924_, v_sz_2923_);
if (v___x_2927_ == 0)
{
lean_object* v___x_2928_; 
v___x_2928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2928_, 0, v_b_2925_);
return v___x_2928_;
}
else
{
lean_object* v_a_2929_; lean_object* v_fst_2930_; lean_object* v_snd_2931_; lean_object* v_fst_2932_; lean_object* v_snd_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2956_; 
v_a_2929_ = lean_array_uget_borrowed(v_as_2922_, v_i_2924_);
v_fst_2930_ = lean_ctor_get(v_a_2929_, 0);
v_snd_2931_ = lean_ctor_get(v_a_2929_, 1);
v_fst_2932_ = lean_ctor_get(v_b_2925_, 0);
v_snd_2933_ = lean_ctor_get(v_b_2925_, 1);
v_isSharedCheck_2956_ = !lean_is_exclusive(v_b_2925_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2935_ = v_b_2925_;
v_isShared_2936_ = v_isSharedCheck_2956_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_snd_2933_);
lean_inc(v_fst_2932_);
lean_dec(v_b_2925_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2956_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2938_; 
if (v_isShared_2936_ == 0)
{
v___x_2938_ = v___x_2935_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_fst_2932_);
lean_ctor_set(v_reuseFailAlloc_2955_, 1, v_snd_2933_);
v___x_2938_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
size_t v_sz_2939_; size_t v___x_2940_; lean_object* v___x_2941_; 
v_sz_2939_ = lean_array_size(v_snd_2931_);
v___x_2940_ = ((size_t)0ULL);
lean_inc(v_fst_2930_);
v___x_2941_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(v_fst_2930_, v_snd_2931_, v_sz_2939_, v___x_2940_, v___x_2938_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v_a_2942_; lean_object* v_fst_2943_; lean_object* v_snd_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2954_; 
v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
lean_inc(v_a_2942_);
lean_dec_ref_known(v___x_2941_, 1);
v_fst_2943_ = lean_ctor_get(v_a_2942_, 0);
v_snd_2944_ = lean_ctor_get(v_a_2942_, 1);
v_isSharedCheck_2954_ = !lean_is_exclusive(v_a_2942_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2946_ = v_a_2942_;
v_isShared_2947_ = v_isSharedCheck_2954_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_snd_2944_);
lean_inc(v_fst_2943_);
lean_dec(v_a_2942_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2954_;
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
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_fst_2943_);
lean_ctor_set(v_reuseFailAlloc_2953_, 1, v_snd_2944_);
v___x_2949_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
size_t v___x_2950_; size_t v___x_2951_; 
v___x_2950_ = ((size_t)1ULL);
v___x_2951_ = lean_usize_add(v_i_2924_, v___x_2950_);
v_i_2924_ = v___x_2951_;
v_b_2925_ = v___x_2949_;
goto _start;
}
}
}
else
{
return v___x_2941_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7___boxed(lean_object* v_as_2957_, lean_object* v_sz_2958_, lean_object* v_i_2959_, lean_object* v_b_2960_, lean_object* v___y_2961_){
_start:
{
size_t v_sz_boxed_2962_; size_t v_i_boxed_2963_; lean_object* v_res_2964_; 
v_sz_boxed_2962_ = lean_unbox_usize(v_sz_2958_);
lean_dec(v_sz_2958_);
v_i_boxed_2963_ = lean_unbox_usize(v_i_2959_);
lean_dec(v_i_2959_);
v_res_2964_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(v_as_2957_, v_sz_boxed_2962_, v_i_boxed_2963_, v_b_2960_);
lean_dec_ref(v_as_2957_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(lean_object* v_as_2965_, size_t v_sz_2966_, size_t v_i_2967_, lean_object* v_b_2968_){
_start:
{
uint8_t v___x_2970_; 
v___x_2970_ = lean_usize_dec_lt(v_i_2967_, v_sz_2966_);
if (v___x_2970_ == 0)
{
lean_object* v___x_2971_; 
v___x_2971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2971_, 0, v_b_2968_);
return v___x_2971_;
}
else
{
lean_object* v_a_2972_; lean_object* v_message_2973_; lean_object* v___x_2974_; uint8_t v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v_a_2972_ = lean_array_uget_borrowed(v_as_2965_, v_i_2967_);
v_message_2973_ = lean_ctor_get(v_a_2972_, 1);
v___x_2974_ = lean_box(0);
v___x_2975_ = 0;
lean_inc_ref(v_message_2973_);
v___x_2976_ = l_Lean_SerialMessage_toString(v_message_2973_, v___x_2975_);
v___x_2977_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_2976_);
if (lean_obj_tag(v___x_2977_) == 0)
{
size_t v___x_2978_; size_t v___x_2979_; 
lean_dec_ref_known(v___x_2977_, 1);
v___x_2978_ = ((size_t)1ULL);
v___x_2979_ = lean_usize_add(v_i_2967_, v___x_2978_);
v_i_2967_ = v___x_2979_;
v_b_2968_ = v___x_2974_;
goto _start;
}
else
{
return v___x_2977_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5___boxed(lean_object* v_as_2981_, lean_object* v_sz_2982_, lean_object* v_i_2983_, lean_object* v_b_2984_, lean_object* v___y_2985_){
_start:
{
size_t v_sz_boxed_2986_; size_t v_i_boxed_2987_; lean_object* v_res_2988_; 
v_sz_boxed_2986_ = lean_unbox_usize(v_sz_2982_);
lean_dec(v_sz_2982_);
v_i_boxed_2987_ = lean_unbox_usize(v_i_2983_);
lean_dec(v_i_2983_);
v_res_2988_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(v_as_2981_, v_sz_boxed_2986_, v_i_boxed_2987_, v_b_2984_);
lean_dec_ref(v_as_2981_);
return v_res_2988_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(lean_object* v_as_2991_, size_t v_sz_2992_, size_t v_i_2993_, lean_object* v_b_2994_){
_start:
{
uint8_t v___x_2996_; 
v___x_2996_ = lean_usize_dec_lt(v_i_2993_, v_sz_2992_);
if (v___x_2996_ == 0)
{
lean_object* v___x_2997_; 
v___x_2997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2997_, 0, v_b_2994_);
return v___x_2997_;
}
else
{
lean_object* v_a_2998_; lean_object* v_fst_2999_; lean_object* v_snd_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v_a_2998_ = lean_array_uget_borrowed(v_as_2991_, v_i_2993_);
v_fst_2999_ = lean_ctor_get(v_a_2998_, 0);
v_snd_3000_ = lean_ctor_get(v_a_2998_, 1);
v___x_3001_ = lean_box(0);
v___x_3002_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___closed__0));
lean_inc(v_fst_2999_);
v___x_3003_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2999_, v___x_2996_);
v___x_3004_ = lean_string_append(v___x_3002_, v___x_3003_);
lean_dec_ref(v___x_3003_);
v___x_3005_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___closed__1));
v___x_3006_ = lean_string_append(v___x_3004_, v___x_3005_);
v___x_3007_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_3006_);
if (lean_obj_tag(v___x_3007_) == 0)
{
size_t v_sz_3008_; size_t v___x_3009_; lean_object* v___x_3010_; 
lean_dec_ref_known(v___x_3007_, 1);
v_sz_3008_ = lean_array_size(v_snd_3000_);
v___x_3009_ = ((size_t)0ULL);
v___x_3010_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(v_snd_3000_, v_sz_3008_, v___x_3009_, v___x_3001_);
if (lean_obj_tag(v___x_3010_) == 0)
{
size_t v___x_3011_; size_t v___x_3012_; 
lean_dec_ref_known(v___x_3010_, 1);
v___x_3011_ = ((size_t)1ULL);
v___x_3012_ = lean_usize_add(v_i_2993_, v___x_3011_);
v_i_2993_ = v___x_3012_;
v_b_2994_ = v___x_3001_;
goto _start;
}
else
{
return v___x_3010_;
}
}
else
{
return v___x_3007_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___boxed(lean_object* v_as_3014_, lean_object* v_sz_3015_, lean_object* v_i_3016_, lean_object* v_b_3017_, lean_object* v___y_3018_){
_start:
{
size_t v_sz_boxed_3019_; size_t v_i_boxed_3020_; lean_object* v_res_3021_; 
v_sz_boxed_3019_ = lean_unbox_usize(v_sz_3015_);
lean_dec(v_sz_3015_);
v_i_boxed_3020_ = lean_unbox_usize(v_i_3016_);
lean_dec(v_i_3016_);
v_res_3021_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(v_as_3014_, v_sz_boxed_3019_, v_i_boxed_3020_, v_b_3017_);
lean_dec_ref(v_as_3014_);
return v_res_3021_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(lean_object* v_args_3026_, lean_object* v_linterOpts_3027_, lean_object* v_env_3028_, lean_object* v_mod_3029_){
_start:
{
uint8_t v_lintOnly_3031_; uint8_t v_mode_3032_; lean_object* v___y_3034_; uint8_t v___y_3035_; lean_object* v___y_3103_; lean_object* v___x_3109_; lean_object* v_textGroups_3110_; 
v_lintOnly_3031_ = lean_ctor_get_uint8(v_args_3026_, sizeof(void*)*4);
v_mode_3032_ = lean_ctor_get_uint8(v_args_3026_, sizeof(void*)*4 + 1);
v___x_3109_ = l_Lean_Name_getRoot(v_mod_3029_);
v_textGroups_3110_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(v_env_3028_, v___x_3109_);
lean_dec(v___x_3109_);
if (v_lintOnly_3031_ == 0)
{
v___y_3103_ = v_textGroups_3110_;
goto v___jp_3102_;
}
else
{
lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3111_ = lean_unsigned_to_nat(0u);
v___x_3112_ = lean_array_get_size(v_textGroups_3110_);
v___x_3113_ = l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(v_linterOpts_3027_, v_textGroups_3110_, v___x_3111_, v___x_3112_);
lean_dec_ref(v_textGroups_3110_);
v___y_3103_ = v___x_3113_;
goto v___jp_3102_;
}
v___jp_3033_:
{
switch(v_mode_3032_)
{
case 0:
{
lean_object* v___x_3036_; size_t v_sz_3037_; size_t v___x_3038_; lean_object* v___x_3039_; 
v___x_3036_ = lean_box(0);
v_sz_3037_ = lean_array_size(v___y_3034_);
v___x_3038_ = ((size_t)0ULL);
v___x_3039_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(v___y_3034_, v_sz_3037_, v___x_3038_, v___x_3036_);
lean_dec_ref(v___y_3034_);
if (lean_obj_tag(v___x_3039_) == 0)
{
lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3047_; 
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_3039_);
if (v_isSharedCheck_3047_ == 0)
{
lean_object* v_unused_3048_; 
v_unused_3048_ = lean_ctor_get(v___x_3039_, 0);
lean_dec(v_unused_3048_);
v___x_3041_ = v___x_3039_;
v_isShared_3042_ = v_isSharedCheck_3047_;
goto v_resetjp_3040_;
}
else
{
lean_dec(v___x_3039_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3047_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3043_; lean_object* v___x_3045_; 
v___x_3043_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_3043_, 0, v___y_3035_);
if (v_isShared_3042_ == 0)
{
lean_ctor_set(v___x_3041_, 0, v___x_3043_);
v___x_3045_ = v___x_3041_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v___x_3043_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
}
else
{
lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3056_; 
v_a_3049_ = lean_ctor_get(v___x_3039_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3039_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3051_ = v___x_3039_;
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___x_3039_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3054_; 
if (v_isShared_3052_ == 0)
{
v___x_3054_ = v___x_3051_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3049_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
}
case 1:
{
lean_object* v___x_3057_; size_t v_sz_3058_; size_t v___x_3059_; lean_object* v___x_3060_; 
v___x_3057_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___closed__0));
v_sz_3058_ = lean_array_size(v___y_3034_);
v___x_3059_ = ((size_t)0ULL);
v___x_3060_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(v___y_3034_, v_sz_3058_, v___x_3059_, v___x_3057_);
lean_dec_ref(v___y_3034_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3072_; 
v_a_3061_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3063_ = v___x_3060_;
v_isShared_3064_ = v_isSharedCheck_3072_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3060_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3072_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v_fst_3065_; lean_object* v_snd_3066_; lean_object* v___x_3067_; uint8_t v___x_3068_; lean_object* v___x_3070_; 
v_fst_3065_ = lean_ctor_get(v_a_3061_, 0);
lean_inc(v_fst_3065_);
v_snd_3066_ = lean_ctor_get(v_a_3061_, 1);
lean_inc(v_snd_3066_);
lean_dec(v_a_3061_);
v___x_3067_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_3067_, 0, v_fst_3065_);
v___x_3068_ = lean_unbox(v_snd_3066_);
lean_dec(v_snd_3066_);
lean_ctor_set_uint8(v___x_3067_, sizeof(void*)*1, v___x_3068_);
if (v_isShared_3064_ == 0)
{
lean_ctor_set(v___x_3063_, 0, v___x_3067_);
v___x_3070_ = v___x_3063_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v___x_3067_);
v___x_3070_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
return v___x_3070_;
}
}
}
else
{
lean_object* v_a_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3080_; 
v_a_3073_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3075_ = v___x_3060_;
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_a_3073_);
lean_dec(v___x_3060_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
lean_object* v___x_3078_; 
if (v_isShared_3076_ == 0)
{
v___x_3078_ = v___x_3075_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_a_3073_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
}
}
default: 
{
lean_object* v_codeQualityEntries_3081_; size_t v_sz_3082_; size_t v___x_3083_; lean_object* v___x_3084_; 
v_codeQualityEntries_3081_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality___closed__0));
v_sz_3082_ = lean_array_size(v___y_3034_);
v___x_3083_ = ((size_t)0ULL);
v___x_3084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(v___y_3034_, v_sz_3082_, v___x_3083_, v_codeQualityEntries_3081_);
lean_dec_ref(v___y_3034_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3093_; 
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3087_ = v___x_3084_;
v_isShared_3088_ = v_isSharedCheck_3093_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3084_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3093_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3089_; lean_object* v___x_3091_; 
v___x_3089_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3089_, 0, v_a_3085_);
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 0, v___x_3089_);
v___x_3091_ = v___x_3087_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v___x_3089_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
else
{
lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3101_; 
v_a_3094_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3096_ = v___x_3084_;
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_3084_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3099_; 
if (v_isShared_3097_ == 0)
{
v___x_3099_ = v___x_3096_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_a_3094_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
}
}
}
v___jp_3102_:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; uint8_t v___x_3106_; 
v___x_3104_ = lean_array_get_size(v___y_3103_);
v___x_3105_ = lean_unsigned_to_nat(0u);
v___x_3106_ = lean_nat_dec_eq(v___x_3104_, v___x_3105_);
if (v___x_3106_ == 0)
{
uint8_t v___x_3107_; 
v___x_3107_ = 1;
v___y_3034_ = v___y_3103_;
v___y_3035_ = v___x_3107_;
goto v___jp_3033_;
}
else
{
uint8_t v___x_3108_; 
v___x_3108_ = 0;
v___y_3034_ = v___y_3103_;
v___y_3035_ = v___x_3108_;
goto v___jp_3033_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___boxed(lean_object* v_args_3114_, lean_object* v_linterOpts_3115_, lean_object* v_env_3116_, lean_object* v_mod_3117_, lean_object* v_a_3118_){
_start:
{
lean_object* v_res_3119_; 
v_res_3119_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(v_args_3114_, v_linterOpts_3115_, v_env_3116_, v_mod_3117_);
lean_dec(v_mod_3117_);
lean_dec_ref(v_env_3116_);
lean_dec_ref(v_linterOpts_3115_);
lean_dec_ref(v_args_3114_);
return v_res_3119_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0(lean_object* v_00_u03b4_3120_, lean_object* v_t_3121_, lean_object* v_k_3122_, lean_object* v_fallback_3123_){
_start:
{
lean_object* v___x_3124_; 
v___x_3124_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(v_t_3121_, v_k_3122_, v_fallback_3123_);
return v___x_3124_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___boxed(lean_object* v_00_u03b4_3125_, lean_object* v_t_3126_, lean_object* v_k_3127_, lean_object* v_fallback_3128_){
_start:
{
lean_object* v_res_3129_; 
v_res_3129_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0(v_00_u03b4_3125_, v_t_3126_, v_k_3127_, v_fallback_3128_);
lean_dec(v_fallback_3128_);
lean_dec(v_k_3127_);
lean_dec(v_t_3126_);
return v_res_3129_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(uint8_t v___y_3130_, lean_object* v_____r_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_){
_start:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3135_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_3135_, 0, v___y_3130_);
v___x_3136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3135_);
return v___x_3136_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0___boxed(lean_object* v___y_3137_, lean_object* v_____r_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
uint8_t v___y_16494__boxed_3142_; lean_object* v_res_3143_; 
v___y_16494__boxed_3142_ = lean_unbox(v___y_3137_);
v_res_3143_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_16494__boxed_3142_, v_____r_3138_, v___y_3139_, v___y_3140_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
return v_res_3143_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0(void){
_start:
{
lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___x_3144_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15);
v___x_3145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3145_, 0, v___x_3144_);
return v___x_3145_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1(void){
_start:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3146_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_3147_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0);
v___x_3148_ = lean_unsigned_to_nat(0u);
v___x_3149_ = lean_alloc_ctor(0, 12, 0);
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
lean_ctor_set(v___x_3149_, 11, v___x_3146_);
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
lean_object* v___x_3167_; lean_object* v_toCold_3168_; lean_object* v_env_3169_; lean_object* v_options_3170_; uint8_t v___x_3171_; lean_object* v_env_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3167_ = lean_st_ref_get(v___y_3165_);
v_toCold_3168_ = lean_ctor_get(v___y_3164_, 0);
v_env_3169_ = lean_ctor_get(v___x_3167_, 0);
lean_inc_ref(v_env_3169_);
lean_dec(v___x_3167_);
v_options_3170_ = lean_ctor_get(v_toCold_3168_, 2);
v___x_3171_ = 0;
v_env_3172_ = l_Lean_Environment_setRecordingDeps(v_env_3169_, v___x_3171_);
v___x_3173_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1);
v___x_3174_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4);
lean_inc_ref(v_options_3170_);
v___x_3175_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3175_, 0, v_env_3172_);
lean_ctor_set(v___x_3175_, 1, v___x_3173_);
lean_ctor_set(v___x_3175_, 2, v___x_3174_);
lean_ctor_set(v___x_3175_, 3, v_options_3170_);
v___x_3176_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3176_, 0, v___x_3175_);
lean_ctor_set(v___x_3176_, 1, v_msgData_3163_);
v___x_3177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3176_);
return v___x_3177_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___boxed(lean_object* v_msgData_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_){
_start:
{
lean_object* v_res_3182_; 
v_res_3182_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(v_msgData_3178_, v___y_3179_, v___y_3180_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
return v_res_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(lean_object* v_msg_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_){
_start:
{
lean_object* v_ref_3187_; lean_object* v___x_3188_; lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3197_; 
v_ref_3187_ = lean_ctor_get(v___y_3184_, 2);
v___x_3188_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(v_msg_3183_, v___y_3184_, v___y_3185_);
v_a_3189_ = lean_ctor_get(v___x_3188_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3191_ = v___x_3188_;
v_isShared_3192_ = v_isSharedCheck_3197_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___x_3188_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3197_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3193_; lean_object* v___x_3195_; 
lean_inc(v_ref_3187_);
v___x_3193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3193_, 0, v_ref_3187_);
lean_ctor_set(v___x_3193_, 1, v_a_3189_);
if (v_isShared_3192_ == 0)
{
lean_ctor_set_tag(v___x_3191_, 1);
lean_ctor_set(v___x_3191_, 0, v___x_3193_);
v___x_3195_ = v___x_3191_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v___x_3193_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg___boxed(lean_object* v_msg_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_){
_start:
{
lean_object* v_res_3202_; 
v_res_3202_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_3198_, v___y_3199_, v___y_3200_);
lean_dec(v___y_3200_);
lean_dec_ref(v___y_3199_);
return v_res_3202_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(lean_object* v_ref_3203_, lean_object* v_msg_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_){
_start:
{
lean_object* v_toCold_3208_; lean_object* v_currRecDepth_3209_; lean_object* v_ref_3210_; uint16_t v_optionFlags_3211_; uint8_t v_suppressElabErrors_3212_; uint8_t v_isRecordingDeps_3213_; lean_object* v_ref_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
v_toCold_3208_ = lean_ctor_get(v___y_3205_, 0);
v_currRecDepth_3209_ = lean_ctor_get(v___y_3205_, 1);
v_ref_3210_ = lean_ctor_get(v___y_3205_, 2);
v_optionFlags_3211_ = lean_ctor_get_uint16(v___y_3205_, sizeof(void*)*3);
v_suppressElabErrors_3212_ = lean_ctor_get_uint8(v___y_3205_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3213_ = lean_ctor_get_uint8(v___y_3205_, sizeof(void*)*3 + 3);
v_ref_3214_ = l_Lean_replaceRef(v_ref_3203_, v_ref_3210_);
lean_inc(v_currRecDepth_3209_);
lean_inc_ref(v_toCold_3208_);
v___x_3215_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3215_, 0, v_toCold_3208_);
lean_ctor_set(v___x_3215_, 1, v_currRecDepth_3209_);
lean_ctor_set(v___x_3215_, 2, v_ref_3214_);
lean_ctor_set_uint16(v___x_3215_, sizeof(void*)*3, v_optionFlags_3211_);
lean_ctor_set_uint8(v___x_3215_, sizeof(void*)*3 + 2, v_suppressElabErrors_3212_);
lean_ctor_set_uint8(v___x_3215_, sizeof(void*)*3 + 3, v_isRecordingDeps_3213_);
v___x_3216_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_3204_, v___x_3215_, v___y_3206_);
lean_dec_ref_known(v___x_3215_, 3);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg___boxed(lean_object* v_ref_3217_, lean_object* v_msg_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_){
_start:
{
lean_object* v_res_3222_; 
v_res_3222_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_3217_, v_msg_3218_, v___y_3219_, v___y_3220_);
lean_dec(v___y_3220_);
lean_dec_ref(v___y_3219_);
lean_dec(v_ref_3217_);
return v_res_3222_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3224_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__0));
v___x_3225_ = l_Lean_stringToMessageData(v___x_3224_);
return v___x_3225_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3227_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__2));
v___x_3228_ = l_Lean_stringToMessageData(v___x_3227_);
return v___x_3228_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5(void){
_start:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3230_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__4));
v___x_3231_ = l_Lean_stringToMessageData(v___x_3230_);
return v___x_3231_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7(void){
_start:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3233_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__6));
v___x_3234_ = l_Lean_stringToMessageData(v___x_3233_);
return v___x_3234_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9(void){
_start:
{
lean_object* v___x_3236_; lean_object* v___x_3237_; 
v___x_3236_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__8));
v___x_3237_ = l_Lean_stringToMessageData(v___x_3236_);
return v___x_3237_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11(void){
_start:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; 
v___x_3239_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__10));
v___x_3240_ = l_Lean_stringToMessageData(v___x_3239_);
return v___x_3240_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13(void){
_start:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; 
v___x_3242_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__12));
v___x_3243_ = l_Lean_stringToMessageData(v___x_3242_);
return v___x_3243_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__15(void){
_start:
{
lean_object* v___x_3245_; lean_object* v___x_3246_; 
v___x_3245_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__14));
v___x_3246_ = l_Lean_stringToMessageData(v___x_3245_);
return v___x_3246_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__17(void){
_start:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3248_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__16));
v___x_3249_ = l_Lean_stringToMessageData(v___x_3248_);
return v___x_3249_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__19(void){
_start:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3251_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__18));
v___x_3252_ = l_Lean_stringToMessageData(v___x_3251_);
return v___x_3252_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__21(void){
_start:
{
lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3254_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__20));
v___x_3255_ = l_Lean_stringToMessageData(v___x_3254_);
return v___x_3255_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(lean_object* v_msg_3256_, lean_object* v_declHint_3257_, lean_object* v___y_3258_){
_start:
{
lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v_env_3262_; uint8_t v___x_3263_; 
v___x_3260_ = lean_box(0);
v___x_3261_ = lean_st_ref_get(v___y_3258_);
v_env_3262_ = lean_ctor_get(v___x_3261_, 0);
lean_inc_ref(v_env_3262_);
lean_dec(v___x_3261_);
v___x_3263_ = l_Lean_Name_isAnonymous(v_declHint_3257_);
if (v___x_3263_ == 0)
{
uint8_t v_isExporting_3264_; 
v_isExporting_3264_ = lean_ctor_get_uint8(v_env_3262_, sizeof(void*)*13);
if (v_isExporting_3264_ == 0)
{
lean_object* v___x_3265_; 
lean_dec_ref(v_env_3262_);
lean_dec(v_declHint_3257_);
v___x_3265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3265_, 0, v_msg_3256_);
return v___x_3265_;
}
else
{
lean_object* v___x_3266_; uint8_t v___x_3267_; 
lean_inc_ref(v_env_3262_);
v___x_3266_ = l_Lean_Environment_setExporting(v_env_3262_, v___x_3263_);
lean_inc(v_declHint_3257_);
lean_inc_ref(v___x_3266_);
v___x_3267_ = l_Lean_Environment_contains(v___x_3266_, v_declHint_3257_, v_isExporting_3264_);
if (v___x_3267_ == 0)
{
lean_object* v___x_3268_; 
lean_dec_ref(v___x_3266_);
lean_dec_ref(v_env_3262_);
lean_dec(v_declHint_3257_);
v___x_3268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3268_, 0, v_msg_3256_);
return v___x_3268_;
}
else
{
lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v_c_3274_; lean_object* v___x_3275_; 
v___x_3269_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1);
v___x_3270_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4);
v___x_3271_ = l_Lean_Options_empty;
v___x_3272_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3272_, 0, v___x_3266_);
lean_ctor_set(v___x_3272_, 1, v___x_3269_);
lean_ctor_set(v___x_3272_, 2, v___x_3270_);
lean_ctor_set(v___x_3272_, 3, v___x_3271_);
lean_inc(v_declHint_3257_);
v___x_3273_ = l_Lean_MessageData_ofConstName(v_declHint_3257_, v___x_3263_);
v_c_3274_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3274_, 0, v___x_3272_);
lean_ctor_set(v_c_3274_, 1, v___x_3273_);
v___x_3275_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3262_, v_declHint_3257_);
if (lean_obj_tag(v___x_3275_) == 0)
{
lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
lean_dec_ref(v_env_3262_);
lean_dec(v_declHint_3257_);
v___x_3276_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1);
v___x_3277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3276_);
lean_ctor_set(v___x_3277_, 1, v_c_3274_);
v___x_3278_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3);
v___x_3279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3277_);
lean_ctor_set(v___x_3279_, 1, v___x_3278_);
v___x_3280_ = l_Lean_MessageData_note(v___x_3279_);
v___x_3281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3281_, 0, v_msg_3256_);
lean_ctor_set(v___x_3281_, 1, v___x_3280_);
v___x_3282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3281_);
return v___x_3282_;
}
else
{
lean_object* v_val_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3339_; 
v_val_3283_ = lean_ctor_get(v___x_3275_, 0);
v_isSharedCheck_3339_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3339_ == 0)
{
v___x_3285_ = v___x_3275_;
v_isShared_3286_ = v_isSharedCheck_3339_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_val_3283_);
lean_dec(v___x_3275_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3339_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3287_; lean_object* v_modules_3288_; lean_object* v_moduleNames_3289_; lean_object* v_mod_3290_; uint8_t v___y_3292_; uint8_t v___x_3322_; 
v___x_3287_ = l_Lean_Environment_header(v_env_3262_);
lean_dec_ref(v_env_3262_);
v_modules_3288_ = lean_ctor_get(v___x_3287_, 3);
lean_inc_ref(v_modules_3288_);
v_moduleNames_3289_ = lean_ctor_get(v___x_3287_, 4);
lean_inc_ref(v_moduleNames_3289_);
lean_dec_ref(v___x_3287_);
v_mod_3290_ = lean_array_get(v___x_3260_, v_moduleNames_3289_, v_val_3283_);
lean_dec_ref(v_moduleNames_3289_);
v___x_3322_ = l_Lean_isPrivateName(v_declHint_3257_);
lean_dec(v_declHint_3257_);
if (v___x_3322_ == 0)
{
lean_object* v___x_3323_; uint8_t v___x_3324_; 
v___x_3323_ = lean_array_get_size(v_modules_3288_);
v___x_3324_ = lean_nat_dec_lt(v_val_3283_, v___x_3323_);
if (v___x_3324_ == 0)
{
lean_dec_ref(v_modules_3288_);
lean_dec(v_val_3283_);
v___y_3292_ = v___x_3322_;
goto v___jp_3291_;
}
else
{
lean_object* v___x_3325_; lean_object* v_toImport_3326_; uint8_t v_isExported_3327_; 
v___x_3325_ = lean_array_fget(v_modules_3288_, v_val_3283_);
lean_dec(v_val_3283_);
lean_dec_ref(v_modules_3288_);
v_toImport_3326_ = lean_ctor_get(v___x_3325_, 0);
lean_inc_ref(v_toImport_3326_);
lean_dec(v___x_3325_);
v_isExported_3327_ = lean_ctor_get_uint8(v_toImport_3326_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_3326_);
v___y_3292_ = v_isExported_3327_;
goto v___jp_3291_;
}
}
else
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
lean_dec_ref(v_modules_3288_);
lean_del_object(v___x_3285_);
lean_dec(v_val_3283_);
v___x_3328_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1);
v___x_3329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3328_);
lean_ctor_set(v___x_3329_, 1, v_c_3274_);
v___x_3330_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__19);
v___x_3331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3329_);
lean_ctor_set(v___x_3331_, 1, v___x_3330_);
v___x_3332_ = l_Lean_MessageData_ofName(v_mod_3290_);
v___x_3333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3331_);
lean_ctor_set(v___x_3333_, 1, v___x_3332_);
v___x_3334_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__21);
v___x_3335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3333_);
lean_ctor_set(v___x_3335_, 1, v___x_3334_);
v___x_3336_ = l_Lean_MessageData_note(v___x_3335_);
v___x_3337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3337_, 0, v_msg_3256_);
lean_ctor_set(v___x_3337_, 1, v___x_3336_);
v___x_3338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3337_);
return v___x_3338_;
}
v___jp_3291_:
{
if (v___y_3292_ == 0)
{
lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3304_; 
v___x_3293_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5);
v___x_3294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3293_);
lean_ctor_set(v___x_3294_, 1, v_c_3274_);
v___x_3295_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7);
v___x_3296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3296_, 0, v___x_3294_);
lean_ctor_set(v___x_3296_, 1, v___x_3295_);
v___x_3297_ = l_Lean_MessageData_ofName(v_mod_3290_);
v___x_3298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3296_);
lean_ctor_set(v___x_3298_, 1, v___x_3297_);
v___x_3299_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9);
v___x_3300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3298_);
lean_ctor_set(v___x_3300_, 1, v___x_3299_);
v___x_3301_ = l_Lean_MessageData_note(v___x_3300_);
v___x_3302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3302_, 0, v_msg_3256_);
lean_ctor_set(v___x_3302_, 1, v___x_3301_);
if (v_isShared_3286_ == 0)
{
lean_ctor_set_tag(v___x_3285_, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3302_);
v___x_3304_ = v___x_3285_;
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
lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3320_; 
v___x_3306_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11);
v___x_3307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3306_);
lean_ctor_set(v___x_3307_, 1, v_c_3274_);
v___x_3308_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13);
v___x_3309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3307_);
lean_ctor_set(v___x_3309_, 1, v___x_3308_);
v___x_3310_ = l_Lean_MessageData_ofName(v_mod_3290_);
lean_inc_ref(v___x_3310_);
v___x_3311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3309_);
lean_ctor_set(v___x_3311_, 1, v___x_3310_);
v___x_3312_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__15);
v___x_3313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3311_);
lean_ctor_set(v___x_3313_, 1, v___x_3312_);
v___x_3314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3313_);
lean_ctor_set(v___x_3314_, 1, v___x_3310_);
v___x_3315_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__17);
v___x_3316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3314_);
lean_ctor_set(v___x_3316_, 1, v___x_3315_);
v___x_3317_ = l_Lean_MessageData_note(v___x_3316_);
v___x_3318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3318_, 0, v_msg_3256_);
lean_ctor_set(v___x_3318_, 1, v___x_3317_);
if (v_isShared_3286_ == 0)
{
lean_ctor_set_tag(v___x_3285_, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3318_);
v___x_3320_ = v___x_3285_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v___x_3318_);
v___x_3320_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
return v___x_3320_;
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
lean_object* v___x_3340_; 
lean_dec_ref(v_env_3262_);
lean_dec(v_declHint_3257_);
v___x_3340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3340_, 0, v_msg_3256_);
return v___x_3340_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___boxed(lean_object* v_msg_3341_, lean_object* v_declHint_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_){
_start:
{
lean_object* v_res_3345_; 
v_res_3345_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_3341_, v_declHint_3342_, v___y_3343_);
lean_dec(v___y_3343_);
return v_res_3345_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(lean_object* v_msg_3346_, lean_object* v_declHint_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
lean_object* v___x_3351_; lean_object* v_a_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3361_; 
v___x_3351_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_3346_, v_declHint_3347_, v___y_3349_);
v_a_3352_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3354_ = v___x_3351_;
v_isShared_3355_ = v_isSharedCheck_3361_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_a_3352_);
lean_dec(v___x_3351_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3361_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3359_; 
v___x_3356_ = l_Lean_unknownIdentifierMessageTag;
v___x_3357_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3356_);
lean_ctor_set(v___x_3357_, 1, v_a_3352_);
if (v_isShared_3355_ == 0)
{
lean_ctor_set(v___x_3354_, 0, v___x_3357_);
v___x_3359_ = v___x_3354_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v___x_3357_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14___boxed(lean_object* v_msg_3362_, lean_object* v_declHint_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_){
_start:
{
lean_object* v_res_3367_; 
v_res_3367_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(v_msg_3362_, v_declHint_3363_, v___y_3364_, v___y_3365_);
lean_dec(v___y_3365_);
lean_dec_ref(v___y_3364_);
return v_res_3367_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(lean_object* v_ref_3368_, lean_object* v_msg_3369_, lean_object* v_declHint_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_){
_start:
{
lean_object* v___x_3374_; lean_object* v_a_3375_; lean_object* v___x_3376_; 
v___x_3374_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(v_msg_3369_, v_declHint_3370_, v___y_3371_, v___y_3372_);
v_a_3375_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_a_3375_);
lean_dec_ref(v___x_3374_);
v___x_3376_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_3368_, v_a_3375_, v___y_3371_, v___y_3372_);
return v___x_3376_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg___boxed(lean_object* v_ref_3377_, lean_object* v_msg_3378_, lean_object* v_declHint_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_){
_start:
{
lean_object* v_res_3383_; 
v_res_3383_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_3377_, v_msg_3378_, v_declHint_3379_, v___y_3380_, v___y_3381_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
lean_dec(v_ref_3377_);
return v_res_3383_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___x_3385_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__0));
v___x_3386_ = l_Lean_stringToMessageData(v___x_3385_);
return v___x_3386_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3387_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__1));
v___x_3388_ = l_Lean_stringToMessageData(v___x_3387_);
return v___x_3388_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(lean_object* v_ref_3389_, lean_object* v_constName_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_){
_start:
{
lean_object* v___x_3394_; uint8_t v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
v___x_3394_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1);
v___x_3395_ = 0;
lean_inc(v_constName_3390_);
v___x_3396_ = l_Lean_MessageData_ofConstName(v_constName_3390_, v___x_3395_);
v___x_3397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3397_, 0, v___x_3394_);
lean_ctor_set(v___x_3397_, 1, v___x_3396_);
v___x_3398_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2);
v___x_3399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3397_);
lean_ctor_set(v___x_3399_, 1, v___x_3398_);
v___x_3400_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_3389_, v___x_3399_, v_constName_3390_, v___y_3391_, v___y_3392_);
return v___x_3400_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___boxed(lean_object* v_ref_3401_, lean_object* v_constName_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_){
_start:
{
lean_object* v_res_3406_; 
v_res_3406_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_3401_, v_constName_3402_, v___y_3403_, v___y_3404_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
lean_dec(v_ref_3401_);
return v_res_3406_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_){
_start:
{
lean_object* v_ref_3411_; lean_object* v___x_3412_; 
v_ref_3411_ = lean_ctor_get(v___y_3408_, 2);
v___x_3412_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_3411_, v_constName_3407_, v___y_3408_, v___y_3409_);
return v___x_3412_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_){
_start:
{
lean_object* v_res_3417_; 
v_res_3417_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_3413_, v___y_3414_, v___y_3415_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(lean_object* v_constName_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
lean_object* v___x_3422_; lean_object* v_env_3423_; uint8_t v___x_3424_; lean_object* v___x_3425_; 
v___x_3422_ = lean_st_ref_get(v___y_3420_);
v_env_3423_ = lean_ctor_get(v___x_3422_, 0);
lean_inc_ref(v_env_3423_);
lean_dec(v___x_3422_);
v___x_3424_ = 0;
lean_inc(v_constName_3418_);
v___x_3425_ = l_Lean_Environment_find_x3f(v_env_3423_, v_constName_3418_, v___x_3424_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v___x_3426_; 
v___x_3426_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_3418_, v___y_3419_, v___y_3420_);
return v___x_3426_;
}
else
{
lean_object* v_val_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3434_; 
lean_dec(v_constName_3418_);
v_val_3427_ = lean_ctor_get(v___x_3425_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3429_ = v___x_3425_;
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_val_3427_);
lean_dec(v___x_3425_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3432_; 
if (v_isShared_3430_ == 0)
{
lean_ctor_set_tag(v___x_3429_, 0);
v___x_3432_ = v___x_3429_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_val_3427_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0___boxed(lean_object* v_constName_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_){
_start:
{
lean_object* v_res_3439_; 
v_res_3439_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(v_constName_3435_, v___y_3436_, v___y_3437_);
lean_dec(v___y_3437_);
lean_dec_ref(v___y_3436_);
return v_res_3439_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(lean_object* v_declName_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_){
_start:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; 
v___x_3444_ = lean_box(0);
lean_inc(v_declName_3440_);
v___x_3445_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(v_declName_3440_, v___y_3441_, v___y_3442_);
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3471_; 
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3471_ == 0)
{
lean_object* v_unused_3472_; 
v_unused_3472_ = lean_ctor_get(v___x_3445_, 0);
lean_dec(v_unused_3472_);
v___x_3447_ = v___x_3445_;
v_isShared_3448_ = v_isSharedCheck_3471_;
goto v_resetjp_3446_;
}
else
{
lean_dec(v___x_3445_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3471_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3449_; lean_object* v_env_3450_; lean_object* v___x_3451_; 
v___x_3449_ = lean_st_ref_get(v___y_3442_);
v_env_3450_ = lean_ctor_get(v___x_3449_, 0);
lean_inc_ref(v_env_3450_);
lean_dec(v___x_3449_);
v___x_3451_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3450_, v_declName_3440_);
lean_dec(v_declName_3440_);
lean_dec_ref(v_env_3450_);
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_object* v___x_3452_; lean_object* v___x_3454_; 
v___x_3452_ = lean_box(0);
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 0, v___x_3452_);
v___x_3454_ = v___x_3447_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v___x_3452_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
return v___x_3454_;
}
}
else
{
lean_object* v_val_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3470_; 
v_val_3456_ = lean_ctor_get(v___x_3451_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3451_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3458_ = v___x_3451_;
v_isShared_3459_ = v_isSharedCheck_3470_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_val_3456_);
lean_dec(v___x_3451_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3470_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3460_; lean_object* v_env_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3465_; 
v___x_3460_ = lean_st_ref_get(v___y_3442_);
v_env_3461_ = lean_ctor_get(v___x_3460_, 0);
lean_inc_ref(v_env_3461_);
lean_dec(v___x_3460_);
v___x_3462_ = l_Lean_Environment_allImportedModuleNames(v_env_3461_);
lean_dec_ref(v_env_3461_);
v___x_3463_ = lean_array_get(v___x_3444_, v___x_3462_, v_val_3456_);
lean_dec(v_val_3456_);
lean_dec_ref(v___x_3462_);
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 0, v___x_3463_);
v___x_3465_ = v___x_3458_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v___x_3463_);
v___x_3465_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
lean_object* v___x_3467_; 
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 0, v___x_3465_);
v___x_3467_ = v___x_3447_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3465_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
}
}
}
}
else
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3480_; 
lean_dec(v_declName_3440_);
v_a_3473_ = lean_ctor_get(v___x_3445_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3475_ = v___x_3445_;
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3445_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3478_; 
if (v_isShared_3476_ == 0)
{
v___x_3478_ = v___x_3475_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3473_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0___boxed(lean_object* v_declName_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_){
_start:
{
lean_object* v_res_3485_; 
v_res_3485_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_declName_3481_, v___y_3482_, v___y_3483_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(lean_object* v_fst_3487_, lean_object* v_sp_3488_, lean_object* v___x_3489_, lean_object* v_as_3490_, size_t v_sz_3491_, size_t v_i_3492_, lean_object* v_b_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_){
_start:
{
lean_object* v_a_3498_; uint8_t v___x_3502_; 
v___x_3502_ = lean_usize_dec_lt(v_i_3492_, v_sz_3491_);
if (v___x_3502_ == 0)
{
lean_object* v___x_3503_; 
lean_dec(v___x_3489_);
lean_dec(v_sp_3488_);
lean_dec_ref(v_fst_3487_);
v___x_3503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3503_, 0, v_b_3493_);
return v___x_3503_;
}
else
{
lean_object* v_a_3504_; lean_object* v_fst_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3633_; 
v_a_3504_ = lean_array_uget(v_as_3490_, v_i_3492_);
v_fst_3505_ = lean_ctor_get(v_a_3504_, 0);
v_isSharedCheck_3633_ = !lean_is_exclusive(v_a_3504_);
if (v_isSharedCheck_3633_ == 0)
{
lean_object* v_unused_3634_; 
v_unused_3634_ = lean_ctor_get(v_a_3504_, 1);
lean_dec(v_unused_3634_);
v___x_3507_ = v_a_3504_;
v_isShared_3508_ = v_isSharedCheck_3633_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_fst_3505_);
lean_dec(v_a_3504_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3633_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v_fst_3509_; lean_object* v_snd_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3632_; 
v_fst_3509_ = lean_ctor_get(v_b_3493_, 0);
v_snd_3510_ = lean_ctor_get(v_b_3493_, 1);
v_isSharedCheck_3632_ = !lean_is_exclusive(v_b_3493_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3512_ = v_b_3493_;
v_isShared_3513_ = v_isSharedCheck_3632_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_snd_3510_);
lean_inc(v_fst_3509_);
lean_dec(v_b_3493_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3632_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3514_; 
lean_inc(v_fst_3505_);
v___x_3514_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_fst_3505_, v___y_3494_, v___y_3495_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_object* v_a_3515_; 
v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_a_3515_);
lean_dec_ref_known(v___x_3514_, 1);
if (lean_obj_tag(v_a_3515_) == 0)
{
lean_object* v_optName_3516_; lean_object* v_ref_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; 
lean_dec(v_snd_3510_);
v_optName_3516_ = lean_ctor_get(v_fst_3487_, 1);
v_ref_3517_ = lean_ctor_get(v___y_3494_, 2);
v___x_3518_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_3505_, v___x_3502_);
v___x_3519_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1___closed__0));
v___x_3520_ = lean_string_append(v___x_3519_, v___x_3518_);
lean_dec_ref(v___x_3518_);
v___x_3521_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__2));
v___x_3522_ = lean_string_append(v___x_3520_, v___x_3521_);
lean_inc(v_optName_3516_);
v___x_3523_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_optName_3516_, v___x_3502_);
v___x_3524_ = lean_string_append(v___x_3522_, v___x_3523_);
lean_dec_ref(v___x_3523_);
v___x_3525_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__3));
v___x_3526_ = lean_string_append(v___x_3524_, v___x_3525_);
v___x_3527_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_3526_);
if (lean_obj_tag(v___x_3527_) == 0)
{
lean_object* v___x_3528_; lean_object* v___x_3530_; 
lean_dec_ref_known(v___x_3527_, 1);
lean_del_object(v___x_3507_);
v___x_3528_ = lean_box(v___x_3502_);
if (v_isShared_3513_ == 0)
{
lean_ctor_set(v___x_3512_, 1, v___x_3528_);
v___x_3530_ = v___x_3512_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_fst_3509_);
lean_ctor_set(v_reuseFailAlloc_3531_, 1, v___x_3528_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
v_a_3498_ = v___x_3530_;
goto v___jp_3497_;
}
}
else
{
lean_object* v_a_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3545_; 
lean_del_object(v___x_3512_);
lean_dec(v_fst_3509_);
lean_dec(v___x_3489_);
lean_dec(v_sp_3488_);
lean_dec_ref(v_fst_3487_);
v_a_3532_ = lean_ctor_get(v___x_3527_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3527_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3534_ = v___x_3527_;
v_isShared_3535_ = v_isSharedCheck_3545_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_a_3532_);
lean_dec(v___x_3527_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3545_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3540_; 
v___x_3536_ = lean_io_error_to_string(v_a_3532_);
v___x_3537_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3537_, 0, v___x_3536_);
v___x_3538_ = l_Lean_MessageData_ofFormat(v___x_3537_);
lean_inc(v_ref_3517_);
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 1, v___x_3538_);
lean_ctor_set(v___x_3507_, 0, v_ref_3517_);
v___x_3540_ = v___x_3507_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_ref_3517_);
lean_ctor_set(v_reuseFailAlloc_3544_, 1, v___x_3538_);
v___x_3540_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
lean_object* v___x_3542_; 
if (v_isShared_3535_ == 0)
{
lean_ctor_set(v___x_3534_, 0, v___x_3540_);
v___x_3542_ = v___x_3534_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v___x_3540_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
return v___x_3542_;
}
}
}
}
}
else
{
lean_object* v_val_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3623_; 
v_val_3546_ = lean_ctor_get(v_a_3515_, 0);
v_isSharedCheck_3623_ = !lean_is_exclusive(v_a_3515_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3548_ = v_a_3515_;
v_isShared_3549_ = v_isSharedCheck_3623_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_val_3546_);
lean_dec(v_a_3515_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3623_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
lean_object* v___x_3550_; 
v___x_3550_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_fst_3505_, v___y_3494_, v___y_3495_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v_a_3551_; lean_object* v___y_3553_; 
v_a_3551_ = lean_ctor_get(v___x_3550_, 0);
lean_inc(v_a_3551_);
lean_dec_ref_known(v___x_3550_, 1);
if (lean_obj_tag(v_a_3551_) == 0)
{
lean_inc(v___x_3489_);
v___y_3553_ = v___x_3489_;
goto v___jp_3552_;
}
else
{
lean_object* v_val_3614_; 
v_val_3614_ = lean_ctor_get(v_a_3551_, 0);
lean_inc(v_val_3614_);
lean_dec_ref_known(v_a_3551_, 1);
v___y_3553_ = v_val_3614_;
goto v___jp_3552_;
}
v___jp_3552_:
{
lean_object* v_ref_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; 
v_ref_3554_ = lean_ctor_get(v___y_3494_, 2);
v___x_3555_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__4));
lean_inc(v___y_3553_);
lean_inc(v_sp_3488_);
v___x_3556_ = l_Lean_SearchPath_findWithExt(v_sp_3488_, v___x_3555_, v___y_3553_);
if (lean_obj_tag(v___x_3556_) == 0)
{
lean_object* v_a_3557_; 
v_a_3557_ = lean_ctor_get(v___x_3556_, 0);
lean_inc(v_a_3557_);
lean_dec_ref_known(v___x_3556_, 1);
if (lean_obj_tag(v_a_3557_) == 0)
{
lean_object* v_optName_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
lean_dec(v_val_3546_);
lean_dec(v_snd_3510_);
v_optName_3558_ = lean_ctor_get(v_fst_3487_, 1);
v___x_3559_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__5));
v___x_3560_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_3553_, v___x_3502_);
v___x_3561_ = lean_string_append(v___x_3559_, v___x_3560_);
lean_dec_ref(v___x_3560_);
v___x_3562_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__6));
v___x_3563_ = lean_string_append(v___x_3561_, v___x_3562_);
lean_inc(v_optName_3558_);
v___x_3564_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_optName_3558_, v___x_3502_);
v___x_3565_ = lean_string_append(v___x_3563_, v___x_3564_);
lean_dec_ref(v___x_3564_);
v___x_3566_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__3));
v___x_3567_ = lean_string_append(v___x_3565_, v___x_3566_);
v___x_3568_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_3567_);
if (lean_obj_tag(v___x_3568_) == 0)
{
lean_object* v___x_3569_; lean_object* v___x_3571_; 
lean_dec_ref_known(v___x_3568_, 1);
lean_del_object(v___x_3548_);
lean_del_object(v___x_3507_);
v___x_3569_ = lean_box(v___x_3502_);
if (v_isShared_3513_ == 0)
{
lean_ctor_set(v___x_3512_, 1, v___x_3569_);
v___x_3571_ = v___x_3512_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v_fst_3509_);
lean_ctor_set(v_reuseFailAlloc_3572_, 1, v___x_3569_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
v_a_3498_ = v___x_3571_;
goto v___jp_3497_;
}
}
else
{
lean_object* v_a_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3588_; 
lean_del_object(v___x_3512_);
lean_dec(v_fst_3509_);
lean_dec(v___x_3489_);
lean_dec(v_sp_3488_);
lean_dec_ref(v_fst_3487_);
v_a_3573_ = lean_ctor_get(v___x_3568_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3568_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3575_ = v___x_3568_;
v_isShared_3576_ = v_isSharedCheck_3588_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_a_3573_);
lean_dec(v___x_3568_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3588_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3577_; lean_object* v___x_3579_; 
v___x_3577_ = lean_io_error_to_string(v_a_3573_);
if (v_isShared_3549_ == 0)
{
lean_ctor_set_tag(v___x_3548_, 3);
lean_ctor_set(v___x_3548_, 0, v___x_3577_);
v___x_3579_ = v___x_3548_;
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
lean_inc(v_ref_3554_);
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 1, v___x_3580_);
lean_ctor_set(v___x_3507_, 0, v_ref_3554_);
v___x_3582_ = v___x_3507_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_ref_3554_);
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
else
{
lean_object* v_range_3589_; lean_object* v_val_3590_; lean_object* v_pos_3591_; lean_object* v_optName_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3596_; 
lean_dec(v___y_3553_);
lean_del_object(v___x_3548_);
lean_del_object(v___x_3507_);
v_range_3589_ = lean_ctor_get(v_val_3546_, 0);
lean_inc_ref(v_range_3589_);
lean_dec(v_val_3546_);
v_val_3590_ = lean_ctor_get(v_a_3557_, 0);
lean_inc(v_val_3590_);
lean_dec_ref_known(v_a_3557_, 1);
v_pos_3591_ = lean_ctor_get(v_range_3589_, 0);
lean_inc_ref(v_pos_3591_);
lean_dec_ref(v_range_3589_);
v_optName_3592_ = lean_ctor_get(v_fst_3487_, 1);
lean_inc(v_optName_3592_);
v___x_3593_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3593_, 0, v_val_3590_);
lean_ctor_set(v___x_3593_, 1, v_pos_3591_);
lean_ctor_set(v___x_3593_, 2, v_optName_3592_);
v___x_3594_ = lean_array_push(v_fst_3509_, v___x_3593_);
if (v_isShared_3513_ == 0)
{
lean_ctor_set(v___x_3512_, 0, v___x_3594_);
v___x_3596_ = v___x_3512_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v___x_3594_);
lean_ctor_set(v_reuseFailAlloc_3597_, 1, v_snd_3510_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
v_a_3498_ = v___x_3596_;
goto v___jp_3497_;
}
}
}
else
{
lean_object* v_a_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3613_; 
lean_dec(v___y_3553_);
lean_dec(v_val_3546_);
lean_del_object(v___x_3512_);
lean_dec(v_snd_3510_);
lean_dec(v_fst_3509_);
lean_dec(v___x_3489_);
lean_dec(v_sp_3488_);
lean_dec_ref(v_fst_3487_);
v_a_3598_ = lean_ctor_get(v___x_3556_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3600_ = v___x_3556_;
v_isShared_3601_ = v_isSharedCheck_3613_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_a_3598_);
lean_dec(v___x_3556_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3613_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___x_3602_; lean_object* v___x_3604_; 
v___x_3602_ = lean_io_error_to_string(v_a_3598_);
if (v_isShared_3549_ == 0)
{
lean_ctor_set_tag(v___x_3548_, 3);
lean_ctor_set(v___x_3548_, 0, v___x_3602_);
v___x_3604_ = v___x_3548_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v___x_3602_);
v___x_3604_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
lean_object* v___x_3605_; lean_object* v___x_3607_; 
v___x_3605_ = l_Lean_MessageData_ofFormat(v___x_3604_);
lean_inc(v_ref_3554_);
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 1, v___x_3605_);
lean_ctor_set(v___x_3507_, 0, v_ref_3554_);
v___x_3607_ = v___x_3507_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_ref_3554_);
lean_ctor_set(v_reuseFailAlloc_3611_, 1, v___x_3605_);
v___x_3607_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
lean_object* v___x_3609_; 
if (v_isShared_3601_ == 0)
{
lean_ctor_set(v___x_3600_, 0, v___x_3607_);
v___x_3609_ = v___x_3600_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3607_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3622_; 
lean_del_object(v___x_3548_);
lean_dec(v_val_3546_);
lean_del_object(v___x_3512_);
lean_dec(v_snd_3510_);
lean_dec(v_fst_3509_);
lean_del_object(v___x_3507_);
lean_dec(v___x_3489_);
lean_dec(v_sp_3488_);
lean_dec_ref(v_fst_3487_);
v_a_3615_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3617_ = v___x_3550_;
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_a_3615_);
lean_dec(v___x_3550_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3620_; 
if (v_isShared_3618_ == 0)
{
v___x_3620_ = v___x_3617_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_a_3615_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
}
}
}
}
else
{
lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3631_; 
lean_del_object(v___x_3512_);
lean_dec(v_snd_3510_);
lean_dec(v_fst_3509_);
lean_del_object(v___x_3507_);
lean_dec(v_fst_3505_);
lean_dec(v___x_3489_);
lean_dec(v_sp_3488_);
lean_dec_ref(v_fst_3487_);
v_a_3624_ = lean_ctor_get(v___x_3514_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3514_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3626_ = v___x_3514_;
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3514_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3629_; 
if (v_isShared_3627_ == 0)
{
v___x_3629_ = v___x_3626_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v_a_3624_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
return v___x_3629_;
}
}
}
}
}
}
v___jp_3497_:
{
size_t v___x_3499_; size_t v___x_3500_; 
v___x_3499_ = ((size_t)1ULL);
v___x_3500_ = lean_usize_add(v_i_3492_, v___x_3499_);
v_i_3492_ = v___x_3500_;
v_b_3493_ = v_a_3498_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1___boxed(lean_object* v_fst_3635_, lean_object* v_sp_3636_, lean_object* v___x_3637_, lean_object* v_as_3638_, lean_object* v_sz_3639_, lean_object* v_i_3640_, lean_object* v_b_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_){
_start:
{
size_t v_sz_boxed_3645_; size_t v_i_boxed_3646_; lean_object* v_res_3647_; 
v_sz_boxed_3645_ = lean_unbox_usize(v_sz_3639_);
lean_dec(v_sz_3639_);
v_i_boxed_3646_ = lean_unbox_usize(v_i_3640_);
lean_dec(v_i_3640_);
v_res_3647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(v_fst_3635_, v_sp_3636_, v___x_3637_, v_as_3638_, v_sz_boxed_3645_, v_i_boxed_3646_, v_b_3641_, v___y_3642_, v___y_3643_);
lean_dec(v___y_3643_);
lean_dec_ref(v___y_3642_);
lean_dec_ref(v_as_3638_);
return v_res_3647_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(lean_object* v_x_3648_, lean_object* v_x_3649_){
_start:
{
if (lean_obj_tag(v_x_3649_) == 0)
{
return v_x_3648_;
}
else
{
lean_object* v_key_3650_; lean_object* v_value_3651_; lean_object* v_tail_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; 
v_key_3650_ = lean_ctor_get(v_x_3649_, 0);
v_value_3651_ = lean_ctor_get(v_x_3649_, 1);
v_tail_3652_ = lean_ctor_get(v_x_3649_, 2);
lean_inc(v_value_3651_);
lean_inc(v_key_3650_);
v___x_3653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3653_, 0, v_key_3650_);
lean_ctor_set(v___x_3653_, 1, v_value_3651_);
v___x_3654_ = lean_array_push(v_x_3648_, v___x_3653_);
v_x_3648_ = v___x_3654_;
v_x_3649_ = v_tail_3652_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2___boxed(lean_object* v_x_3656_, lean_object* v_x_3657_){
_start:
{
lean_object* v_res_3658_; 
v_res_3658_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(v_x_3656_, v_x_3657_);
lean_dec(v_x_3657_);
return v_res_3658_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(lean_object* v_as_3659_, size_t v_i_3660_, size_t v_stop_3661_, lean_object* v_b_3662_){
_start:
{
uint8_t v___x_3663_; 
v___x_3663_ = lean_usize_dec_eq(v_i_3660_, v_stop_3661_);
if (v___x_3663_ == 0)
{
lean_object* v___x_3664_; lean_object* v___x_3665_; size_t v___x_3666_; size_t v___x_3667_; 
v___x_3664_ = lean_array_uget_borrowed(v_as_3659_, v_i_3660_);
v___x_3665_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(v_b_3662_, v___x_3664_);
v___x_3666_ = ((size_t)1ULL);
v___x_3667_ = lean_usize_add(v_i_3660_, v___x_3666_);
v_i_3660_ = v___x_3667_;
v_b_3662_ = v___x_3665_;
goto _start;
}
else
{
return v_b_3662_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3___boxed(lean_object* v_as_3669_, lean_object* v_i_3670_, lean_object* v_stop_3671_, lean_object* v_b_3672_){
_start:
{
size_t v_i_boxed_3673_; size_t v_stop_boxed_3674_; lean_object* v_res_3675_; 
v_i_boxed_3673_ = lean_unbox_usize(v_i_3670_);
lean_dec(v_i_3670_);
v_stop_boxed_3674_ = lean_unbox_usize(v_stop_3671_);
lean_dec(v_stop_3671_);
v_res_3675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_as_3669_, v_i_boxed_3673_, v_stop_boxed_3674_, v_b_3672_);
lean_dec_ref(v_as_3669_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(lean_object* v_sp_3676_, lean_object* v___x_3677_, lean_object* v_as_3678_, size_t v_sz_3679_, size_t v_i_3680_, lean_object* v_b_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_){
_start:
{
uint8_t v___x_3685_; 
v___x_3685_ = lean_usize_dec_lt(v_i_3680_, v_sz_3679_);
if (v___x_3685_ == 0)
{
lean_object* v___x_3686_; 
lean_dec(v___x_3677_);
lean_dec(v_sp_3676_);
v___x_3686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3686_, 0, v_b_3681_);
return v___x_3686_;
}
else
{
lean_object* v_a_3687_; lean_object* v_fst_3688_; lean_object* v_snd_3689_; lean_object* v_fst_3690_; lean_object* v_snd_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3725_; 
v_a_3687_ = lean_array_uget_borrowed(v_as_3678_, v_i_3680_);
v_fst_3688_ = lean_ctor_get(v_a_3687_, 0);
v_snd_3689_ = lean_ctor_get(v_a_3687_, 1);
v_fst_3690_ = lean_ctor_get(v_b_3681_, 0);
v_snd_3691_ = lean_ctor_get(v_b_3681_, 1);
v_isSharedCheck_3725_ = !lean_is_exclusive(v_b_3681_);
if (v_isSharedCheck_3725_ == 0)
{
v___x_3693_ = v_b_3681_;
v_isShared_3694_ = v_isSharedCheck_3725_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_snd_3691_);
lean_inc(v_fst_3690_);
lean_dec(v_b_3681_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3725_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___y_3696_; lean_object* v_size_3716_; lean_object* v_buckets_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; uint8_t v___x_3721_; 
v_size_3716_ = lean_ctor_get(v_snd_3689_, 0);
v_buckets_3717_ = lean_ctor_get(v_snd_3689_, 1);
v___x_3718_ = lean_mk_empty_array_with_capacity(v_size_3716_);
v___x_3719_ = lean_unsigned_to_nat(0u);
v___x_3720_ = lean_array_get_size(v_buckets_3717_);
v___x_3721_ = lean_nat_dec_lt(v___x_3719_, v___x_3720_);
if (v___x_3721_ == 0)
{
v___y_3696_ = v___x_3718_;
goto v___jp_3695_;
}
else
{
size_t v___x_3722_; size_t v___x_3723_; lean_object* v___x_3724_; 
v___x_3722_ = ((size_t)0ULL);
v___x_3723_ = lean_usize_of_nat(v___x_3720_);
v___x_3724_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_buckets_3717_, v___x_3722_, v___x_3723_, v___x_3718_);
v___y_3696_ = v___x_3724_;
goto v___jp_3695_;
}
v___jp_3695_:
{
lean_object* v___x_3698_; 
if (v_isShared_3694_ == 0)
{
v___x_3698_ = v___x_3693_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_fst_3690_);
lean_ctor_set(v_reuseFailAlloc_3715_, 1, v_snd_3691_);
v___x_3698_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
size_t v_sz_3699_; size_t v___x_3700_; lean_object* v___x_3701_; 
v_sz_3699_ = lean_array_size(v___y_3696_);
v___x_3700_ = ((size_t)0ULL);
lean_inc(v___x_3677_);
lean_inc(v_sp_3676_);
lean_inc(v_fst_3688_);
v___x_3701_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(v_fst_3688_, v_sp_3676_, v___x_3677_, v___y_3696_, v_sz_3699_, v___x_3700_, v___x_3698_, v___y_3682_, v___y_3683_);
lean_dec_ref(v___y_3696_);
if (lean_obj_tag(v___x_3701_) == 0)
{
lean_object* v_a_3702_; lean_object* v_fst_3703_; lean_object* v_snd_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3714_; 
v_a_3702_ = lean_ctor_get(v___x_3701_, 0);
lean_inc(v_a_3702_);
lean_dec_ref_known(v___x_3701_, 1);
v_fst_3703_ = lean_ctor_get(v_a_3702_, 0);
v_snd_3704_ = lean_ctor_get(v_a_3702_, 1);
v_isSharedCheck_3714_ = !lean_is_exclusive(v_a_3702_);
if (v_isSharedCheck_3714_ == 0)
{
v___x_3706_ = v_a_3702_;
v_isShared_3707_ = v_isSharedCheck_3714_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_snd_3704_);
lean_inc(v_fst_3703_);
lean_dec(v_a_3702_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3714_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3709_; 
if (v_isShared_3707_ == 0)
{
v___x_3709_ = v___x_3706_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v_fst_3703_);
lean_ctor_set(v_reuseFailAlloc_3713_, 1, v_snd_3704_);
v___x_3709_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
size_t v___x_3710_; size_t v___x_3711_; 
v___x_3710_ = ((size_t)1ULL);
v___x_3711_ = lean_usize_add(v_i_3680_, v___x_3710_);
v_i_3680_ = v___x_3711_;
v_b_3681_ = v___x_3709_;
goto _start;
}
}
}
else
{
lean_dec(v___x_3677_);
lean_dec(v_sp_3676_);
return v___x_3701_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4___boxed(lean_object* v_sp_3726_, lean_object* v___x_3727_, lean_object* v_as_3728_, lean_object* v_sz_3729_, lean_object* v_i_3730_, lean_object* v_b_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_){
_start:
{
size_t v_sz_boxed_3735_; size_t v_i_boxed_3736_; lean_object* v_res_3737_; 
v_sz_boxed_3735_ = lean_unbox_usize(v_sz_3729_);
lean_dec(v_sz_3729_);
v_i_boxed_3736_ = lean_unbox_usize(v_i_3730_);
lean_dec(v_i_3730_);
v_res_3737_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(v_sp_3726_, v___x_3727_, v_as_3728_, v_sz_boxed_3735_, v_i_boxed_3736_, v_b_3731_, v___y_3732_, v___y_3733_);
lean_dec(v___y_3733_);
lean_dec_ref(v___y_3732_);
lean_dec_ref(v_as_3728_);
return v_res_3737_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(uint8_t v___y_3738_, lean_object* v_as_3739_, size_t v_i_3740_, size_t v_stop_3741_){
_start:
{
uint8_t v___x_3742_; 
v___x_3742_ = lean_usize_dec_eq(v_i_3740_, v_stop_3741_);
if (v___x_3742_ == 0)
{
lean_object* v___x_3743_; lean_object* v_snd_3744_; lean_object* v_size_3745_; uint8_t v___x_3746_; lean_object* v___x_3747_; uint8_t v___x_3748_; 
v___x_3743_ = lean_array_uget_borrowed(v_as_3739_, v_i_3740_);
v_snd_3744_ = lean_ctor_get(v___x_3743_, 1);
v_size_3745_ = lean_ctor_get(v_snd_3744_, 0);
v___x_3746_ = 1;
v___x_3747_ = lean_unsigned_to_nat(0u);
v___x_3748_ = lean_nat_dec_eq(v_size_3745_, v___x_3747_);
if (v___x_3748_ == 0)
{
return v___x_3746_;
}
else
{
if (v___y_3738_ == 0)
{
size_t v___x_3749_; size_t v___x_3750_; 
v___x_3749_ = ((size_t)1ULL);
v___x_3750_ = lean_usize_add(v_i_3740_, v___x_3749_);
v_i_3740_ = v___x_3750_;
goto _start;
}
else
{
return v___x_3746_;
}
}
}
else
{
uint8_t v___x_3752_; 
v___x_3752_ = 0;
return v___x_3752_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10___boxed(lean_object* v___y_3753_, lean_object* v_as_3754_, lean_object* v_i_3755_, lean_object* v_stop_3756_){
_start:
{
uint8_t v___y_17543__boxed_3757_; size_t v_i_boxed_3758_; size_t v_stop_boxed_3759_; uint8_t v_res_3760_; lean_object* v_r_3761_; 
v___y_17543__boxed_3757_ = lean_unbox(v___y_3753_);
v_i_boxed_3758_ = lean_unbox_usize(v_i_3755_);
lean_dec(v_i_3755_);
v_stop_boxed_3759_ = lean_unbox_usize(v_stop_3756_);
lean_dec(v_stop_3756_);
v_res_3760_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(v___y_17543__boxed_3757_, v_as_3754_, v_i_boxed_3758_, v_stop_boxed_3759_);
lean_dec_ref(v_as_3754_);
v_r_3761_ = lean_box(v_res_3760_);
return v_r_3761_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(lean_object* v_k_3762_, lean_object* v_v_3763_, lean_object* v_t_3764_){
_start:
{
lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; 
if (lean_obj_tag(v_t_3764_) == 0)
{
lean_object* v_size_3779_; lean_object* v_k_3780_; lean_object* v_v_3781_; lean_object* v_l_3782_; lean_object* v_r_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_4043_; 
v_size_3779_ = lean_ctor_get(v_t_3764_, 0);
v_k_3780_ = lean_ctor_get(v_t_3764_, 1);
v_v_3781_ = lean_ctor_get(v_t_3764_, 2);
v_l_3782_ = lean_ctor_get(v_t_3764_, 3);
v_r_3783_ = lean_ctor_get(v_t_3764_, 4);
v_isSharedCheck_4043_ = !lean_is_exclusive(v_t_3764_);
if (v_isSharedCheck_4043_ == 0)
{
v___x_3785_ = v_t_3764_;
v_isShared_3786_ = v_isSharedCheck_4043_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_r_3783_);
lean_inc(v_l_3782_);
lean_inc(v_v_3781_);
lean_inc(v_k_3780_);
lean_inc(v_size_3779_);
lean_dec(v_t_3764_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_4043_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3819_; lean_object* v___y_3820_; lean_object* v___y_3821_; lean_object* v___y_3822_; lean_object* v___y_3823_; lean_object* v___y_3824_; lean_object* v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; uint8_t v___y_3837_; lean_object* v_fst_4037_; lean_object* v_snd_4038_; lean_object* v_fst_4039_; lean_object* v_snd_4040_; uint8_t v___x_4041_; 
v_fst_4037_ = lean_ctor_get(v_k_3762_, 0);
v_snd_4038_ = lean_ctor_get(v_k_3762_, 1);
v_fst_4039_ = lean_ctor_get(v_k_3780_, 0);
v_snd_4040_ = lean_ctor_get(v_k_3780_, 1);
v___x_4041_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_fst_4037_, v_fst_4039_);
if (v___x_4041_ == 1)
{
uint8_t v___x_4042_; 
v___x_4042_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_snd_4038_, v_snd_4040_);
v___y_3837_ = v___x_4042_;
goto v___jp_3836_;
}
else
{
v___y_3837_ = v___x_4041_;
goto v___jp_3836_;
}
v___jp_3787_:
{
lean_object* v___x_3795_; lean_object* v___x_3797_; 
v___x_3795_ = lean_nat_add(v___y_3791_, v___y_3794_);
lean_dec(v___y_3794_);
lean_dec(v___y_3791_);
if (v_isShared_3786_ == 0)
{
lean_ctor_set(v___x_3785_, 3, v___y_3792_);
lean_ctor_set(v___x_3785_, 0, v___x_3795_);
v___x_3797_ = v___x_3785_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v___x_3795_);
lean_ctor_set(v_reuseFailAlloc_3799_, 1, v_k_3780_);
lean_ctor_set(v_reuseFailAlloc_3799_, 2, v_v_3781_);
lean_ctor_set(v_reuseFailAlloc_3799_, 3, v___y_3792_);
lean_ctor_set(v_reuseFailAlloc_3799_, 4, v_r_3783_);
v___x_3797_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
lean_object* v___x_3798_; 
v___x_3798_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3798_, 0, v___y_3788_);
lean_ctor_set(v___x_3798_, 1, v___y_3789_);
lean_ctor_set(v___x_3798_, 2, v___y_3790_);
lean_ctor_set(v___x_3798_, 3, v___y_3793_);
lean_ctor_set(v___x_3798_, 4, v___x_3797_);
return v___x_3798_;
}
}
v___jp_3800_:
{
lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; 
v___x_3813_ = lean_nat_add(v___y_3807_, v___y_3812_);
lean_dec(v___y_3812_);
lean_dec(v___y_3807_);
v___x_3814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3813_);
lean_ctor_set(v___x_3814_, 1, v___y_3809_);
lean_ctor_set(v___x_3814_, 2, v___y_3805_);
lean_ctor_set(v___x_3814_, 3, v___y_3804_);
lean_ctor_set(v___x_3814_, 4, v___y_3808_);
v___x_3815_ = lean_nat_add(v___y_3803_, v___y_3811_);
lean_dec(v___y_3811_);
if (lean_obj_tag(v___y_3810_) == 0)
{
lean_object* v_size_3816_; 
v_size_3816_ = lean_ctor_get(v___y_3810_, 0);
lean_inc(v_size_3816_);
v___y_3788_ = v___y_3801_;
v___y_3789_ = v___y_3802_;
v___y_3790_ = v___y_3806_;
v___y_3791_ = v___x_3815_;
v___y_3792_ = v___y_3810_;
v___y_3793_ = v___x_3814_;
v___y_3794_ = v_size_3816_;
goto v___jp_3787_;
}
else
{
lean_object* v___x_3817_; 
v___x_3817_ = lean_unsigned_to_nat(0u);
v___y_3788_ = v___y_3801_;
v___y_3789_ = v___y_3802_;
v___y_3790_ = v___y_3806_;
v___y_3791_ = v___x_3815_;
v___y_3792_ = v___y_3810_;
v___y_3793_ = v___x_3814_;
v___y_3794_ = v___x_3817_;
goto v___jp_3787_;
}
}
v___jp_3818_:
{
lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; 
v___x_3831_ = lean_nat_add(v___y_3829_, v___y_3830_);
lean_dec(v___y_3830_);
lean_dec(v___y_3829_);
v___x_3832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3832_, 0, v___x_3831_);
lean_ctor_set(v___x_3832_, 1, v_k_3780_);
lean_ctor_set(v___x_3832_, 2, v_v_3781_);
lean_ctor_set(v___x_3832_, 3, v_l_3782_);
lean_ctor_set(v___x_3832_, 4, v___y_3819_);
v___x_3833_ = lean_nat_add(v___y_3822_, v___y_3827_);
lean_dec(v___y_3827_);
if (lean_obj_tag(v___y_3820_) == 0)
{
lean_object* v_size_3834_; 
v_size_3834_ = lean_ctor_get(v___y_3820_, 0);
lean_inc(v_size_3834_);
v___y_3766_ = v___x_3832_;
v___y_3767_ = v___y_3821_;
v___y_3768_ = v___y_3820_;
v___y_3769_ = v___x_3833_;
v___y_3770_ = v___y_3823_;
v___y_3771_ = v___y_3824_;
v___y_3772_ = v___y_3825_;
v___y_3773_ = v___y_3826_;
v___y_3774_ = v___y_3828_;
v___y_3775_ = v_size_3834_;
goto v___jp_3765_;
}
else
{
lean_object* v___x_3835_; 
v___x_3835_ = lean_unsigned_to_nat(0u);
v___y_3766_ = v___x_3832_;
v___y_3767_ = v___y_3821_;
v___y_3768_ = v___y_3820_;
v___y_3769_ = v___x_3833_;
v___y_3770_ = v___y_3823_;
v___y_3771_ = v___y_3824_;
v___y_3772_ = v___y_3825_;
v___y_3773_ = v___y_3826_;
v___y_3774_ = v___y_3828_;
v___y_3775_ = v___x_3835_;
goto v___jp_3765_;
}
}
v___jp_3836_:
{
switch(v___y_3837_)
{
case 0:
{
lean_object* v_impl_3838_; lean_object* v___x_3839_; 
lean_dec(v_size_3779_);
v_impl_3838_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_3762_, v_v_3763_, v_l_3782_);
v___x_3839_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3783_) == 0)
{
lean_object* v_size_3840_; lean_object* v_size_3841_; lean_object* v_k_3842_; lean_object* v_v_3843_; lean_object* v_l_3844_; lean_object* v_r_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; uint8_t v___x_3848_; 
v_size_3840_ = lean_ctor_get(v_r_3783_, 0);
v_size_3841_ = lean_ctor_get(v_impl_3838_, 0);
v_k_3842_ = lean_ctor_get(v_impl_3838_, 1);
v_v_3843_ = lean_ctor_get(v_impl_3838_, 2);
v_l_3844_ = lean_ctor_get(v_impl_3838_, 3);
v_r_3845_ = lean_ctor_get(v_impl_3838_, 4);
v___x_3846_ = lean_unsigned_to_nat(3u);
v___x_3847_ = lean_nat_mul(v___x_3846_, v_size_3840_);
v___x_3848_ = lean_nat_dec_lt(v___x_3847_, v_size_3841_);
lean_dec(v___x_3847_);
if (v___x_3848_ == 0)
{
lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; 
lean_del_object(v___x_3785_);
v___x_3849_ = lean_nat_add(v___x_3839_, v_size_3841_);
v___x_3850_ = lean_nat_add(v___x_3849_, v_size_3840_);
lean_dec(v___x_3849_);
v___x_3851_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3851_, 0, v___x_3850_);
lean_ctor_set(v___x_3851_, 1, v_k_3780_);
lean_ctor_set(v___x_3851_, 2, v_v_3781_);
lean_ctor_set(v___x_3851_, 3, v_impl_3838_);
lean_ctor_set(v___x_3851_, 4, v_r_3783_);
return v___x_3851_;
}
else
{
lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3888_; 
lean_inc(v_r_3845_);
lean_inc(v_l_3844_);
lean_inc(v_v_3843_);
lean_inc(v_k_3842_);
lean_inc(v_size_3841_);
v_isSharedCheck_3888_ = !lean_is_exclusive(v_impl_3838_);
if (v_isSharedCheck_3888_ == 0)
{
lean_object* v_unused_3889_; lean_object* v_unused_3890_; lean_object* v_unused_3891_; lean_object* v_unused_3892_; lean_object* v_unused_3893_; 
v_unused_3889_ = lean_ctor_get(v_impl_3838_, 4);
lean_dec(v_unused_3889_);
v_unused_3890_ = lean_ctor_get(v_impl_3838_, 3);
lean_dec(v_unused_3890_);
v_unused_3891_ = lean_ctor_get(v_impl_3838_, 2);
lean_dec(v_unused_3891_);
v_unused_3892_ = lean_ctor_get(v_impl_3838_, 1);
lean_dec(v_unused_3892_);
v_unused_3893_ = lean_ctor_get(v_impl_3838_, 0);
lean_dec(v_unused_3893_);
v___x_3853_ = v_impl_3838_;
v_isShared_3854_ = v_isSharedCheck_3888_;
goto v_resetjp_3852_;
}
else
{
lean_dec(v_impl_3838_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3888_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v_size_3855_; lean_object* v_size_3856_; lean_object* v_k_3857_; lean_object* v_v_3858_; lean_object* v_l_3859_; lean_object* v_r_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; uint8_t v___x_3863_; 
v_size_3855_ = lean_ctor_get(v_l_3844_, 0);
v_size_3856_ = lean_ctor_get(v_r_3845_, 0);
v_k_3857_ = lean_ctor_get(v_r_3845_, 1);
v_v_3858_ = lean_ctor_get(v_r_3845_, 2);
v_l_3859_ = lean_ctor_get(v_r_3845_, 3);
v_r_3860_ = lean_ctor_get(v_r_3845_, 4);
v___x_3861_ = lean_unsigned_to_nat(2u);
v___x_3862_ = lean_nat_mul(v___x_3861_, v_size_3855_);
v___x_3863_ = lean_nat_dec_lt(v_size_3856_, v___x_3862_);
lean_dec(v___x_3862_);
if (v___x_3863_ == 0)
{
lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; 
lean_inc(v_r_3860_);
lean_inc(v_l_3859_);
lean_inc(v_v_3858_);
lean_inc(v_k_3857_);
lean_del_object(v___x_3853_);
lean_dec(v_r_3845_);
v___x_3864_ = lean_nat_add(v___x_3839_, v_size_3841_);
lean_dec(v_size_3841_);
v___x_3865_ = lean_nat_add(v___x_3864_, v_size_3840_);
lean_dec(v___x_3864_);
v___x_3866_ = lean_nat_add(v___x_3839_, v_size_3855_);
if (lean_obj_tag(v_l_3859_) == 0)
{
lean_object* v_size_3867_; 
v_size_3867_ = lean_ctor_get(v_l_3859_, 0);
lean_inc(v_size_3867_);
lean_inc(v_size_3840_);
v___y_3801_ = v___x_3865_;
v___y_3802_ = v_k_3857_;
v___y_3803_ = v___x_3839_;
v___y_3804_ = v_l_3844_;
v___y_3805_ = v_v_3843_;
v___y_3806_ = v_v_3858_;
v___y_3807_ = v___x_3866_;
v___y_3808_ = v_l_3859_;
v___y_3809_ = v_k_3842_;
v___y_3810_ = v_r_3860_;
v___y_3811_ = v_size_3840_;
v___y_3812_ = v_size_3867_;
goto v___jp_3800_;
}
else
{
lean_object* v___x_3868_; 
v___x_3868_ = lean_unsigned_to_nat(0u);
lean_inc(v_size_3840_);
v___y_3801_ = v___x_3865_;
v___y_3802_ = v_k_3857_;
v___y_3803_ = v___x_3839_;
v___y_3804_ = v_l_3844_;
v___y_3805_ = v_v_3843_;
v___y_3806_ = v_v_3858_;
v___y_3807_ = v___x_3866_;
v___y_3808_ = v_l_3859_;
v___y_3809_ = v_k_3842_;
v___y_3810_ = v_r_3860_;
v___y_3811_ = v_size_3840_;
v___y_3812_ = v___x_3868_;
goto v___jp_3800_;
}
}
else
{
lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3874_; 
lean_del_object(v___x_3785_);
v___x_3869_ = lean_nat_add(v___x_3839_, v_size_3841_);
lean_dec(v_size_3841_);
v___x_3870_ = lean_nat_add(v___x_3869_, v_size_3840_);
lean_dec(v___x_3869_);
v___x_3871_ = lean_nat_add(v___x_3839_, v_size_3840_);
v___x_3872_ = lean_nat_add(v___x_3871_, v_size_3856_);
lean_dec(v___x_3871_);
lean_inc_ref(v_r_3783_);
if (v_isShared_3854_ == 0)
{
lean_ctor_set(v___x_3853_, 4, v_r_3783_);
lean_ctor_set(v___x_3853_, 3, v_r_3845_);
lean_ctor_set(v___x_3853_, 2, v_v_3781_);
lean_ctor_set(v___x_3853_, 1, v_k_3780_);
lean_ctor_set(v___x_3853_, 0, v___x_3872_);
v___x_3874_ = v___x_3853_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v___x_3872_);
lean_ctor_set(v_reuseFailAlloc_3887_, 1, v_k_3780_);
lean_ctor_set(v_reuseFailAlloc_3887_, 2, v_v_3781_);
lean_ctor_set(v_reuseFailAlloc_3887_, 3, v_r_3845_);
lean_ctor_set(v_reuseFailAlloc_3887_, 4, v_r_3783_);
v___x_3874_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3881_; 
v_isSharedCheck_3881_ = !lean_is_exclusive(v_r_3783_);
if (v_isSharedCheck_3881_ == 0)
{
lean_object* v_unused_3882_; lean_object* v_unused_3883_; lean_object* v_unused_3884_; lean_object* v_unused_3885_; lean_object* v_unused_3886_; 
v_unused_3882_ = lean_ctor_get(v_r_3783_, 4);
lean_dec(v_unused_3882_);
v_unused_3883_ = lean_ctor_get(v_r_3783_, 3);
lean_dec(v_unused_3883_);
v_unused_3884_ = lean_ctor_get(v_r_3783_, 2);
lean_dec(v_unused_3884_);
v_unused_3885_ = lean_ctor_get(v_r_3783_, 1);
lean_dec(v_unused_3885_);
v_unused_3886_ = lean_ctor_get(v_r_3783_, 0);
lean_dec(v_unused_3886_);
v___x_3876_ = v_r_3783_;
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
else
{
lean_dec(v_r_3783_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v___x_3879_; 
if (v_isShared_3877_ == 0)
{
lean_ctor_set(v___x_3876_, 4, v___x_3874_);
lean_ctor_set(v___x_3876_, 3, v_l_3844_);
lean_ctor_set(v___x_3876_, 2, v_v_3843_);
lean_ctor_set(v___x_3876_, 1, v_k_3842_);
lean_ctor_set(v___x_3876_, 0, v___x_3870_);
v___x_3879_ = v___x_3876_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v___x_3870_);
lean_ctor_set(v_reuseFailAlloc_3880_, 1, v_k_3842_);
lean_ctor_set(v_reuseFailAlloc_3880_, 2, v_v_3843_);
lean_ctor_set(v_reuseFailAlloc_3880_, 3, v_l_3844_);
lean_ctor_set(v_reuseFailAlloc_3880_, 4, v___x_3874_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3894_; 
lean_del_object(v___x_3785_);
v_l_3894_ = lean_ctor_get(v_impl_3838_, 3);
if (lean_obj_tag(v_l_3894_) == 0)
{
lean_object* v_r_3895_; lean_object* v_k_3896_; lean_object* v_v_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3906_; 
lean_inc_ref(v_l_3894_);
v_r_3895_ = lean_ctor_get(v_impl_3838_, 4);
v_k_3896_ = lean_ctor_get(v_impl_3838_, 1);
v_v_3897_ = lean_ctor_get(v_impl_3838_, 2);
v_isSharedCheck_3906_ = !lean_is_exclusive(v_impl_3838_);
if (v_isSharedCheck_3906_ == 0)
{
lean_object* v_unused_3907_; lean_object* v_unused_3908_; 
v_unused_3907_ = lean_ctor_get(v_impl_3838_, 3);
lean_dec(v_unused_3907_);
v_unused_3908_ = lean_ctor_get(v_impl_3838_, 0);
lean_dec(v_unused_3908_);
v___x_3899_ = v_impl_3838_;
v_isShared_3900_ = v_isSharedCheck_3906_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_r_3895_);
lean_inc(v_v_3897_);
lean_inc(v_k_3896_);
lean_dec(v_impl_3838_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3906_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___x_3901_; lean_object* v___x_3903_; 
v___x_3901_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3895_);
if (v_isShared_3900_ == 0)
{
lean_ctor_set(v___x_3899_, 3, v_r_3895_);
lean_ctor_set(v___x_3899_, 2, v_v_3781_);
lean_ctor_set(v___x_3899_, 1, v_k_3780_);
lean_ctor_set(v___x_3899_, 0, v___x_3839_);
v___x_3903_ = v___x_3899_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v___x_3839_);
lean_ctor_set(v_reuseFailAlloc_3905_, 1, v_k_3780_);
lean_ctor_set(v_reuseFailAlloc_3905_, 2, v_v_3781_);
lean_ctor_set(v_reuseFailAlloc_3905_, 3, v_r_3895_);
lean_ctor_set(v_reuseFailAlloc_3905_, 4, v_r_3895_);
v___x_3903_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
lean_object* v___x_3904_; 
v___x_3904_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3901_);
lean_ctor_set(v___x_3904_, 1, v_k_3896_);
lean_ctor_set(v___x_3904_, 2, v_v_3897_);
lean_ctor_set(v___x_3904_, 3, v_l_3894_);
lean_ctor_set(v___x_3904_, 4, v___x_3903_);
return v___x_3904_;
}
}
}
else
{
lean_object* v_r_3909_; 
v_r_3909_ = lean_ctor_get(v_impl_3838_, 4);
lean_inc(v_r_3909_);
if (lean_obj_tag(v_r_3909_) == 0)
{
lean_object* v_k_3910_; lean_object* v_v_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3932_; 
lean_inc(v_l_3894_);
v_k_3910_ = lean_ctor_get(v_impl_3838_, 1);
v_v_3911_ = lean_ctor_get(v_impl_3838_, 2);
v_isSharedCheck_3932_ = !lean_is_exclusive(v_impl_3838_);
if (v_isSharedCheck_3932_ == 0)
{
lean_object* v_unused_3933_; lean_object* v_unused_3934_; lean_object* v_unused_3935_; 
v_unused_3933_ = lean_ctor_get(v_impl_3838_, 4);
lean_dec(v_unused_3933_);
v_unused_3934_ = lean_ctor_get(v_impl_3838_, 3);
lean_dec(v_unused_3934_);
v_unused_3935_ = lean_ctor_get(v_impl_3838_, 0);
lean_dec(v_unused_3935_);
v___x_3913_ = v_impl_3838_;
v_isShared_3914_ = v_isSharedCheck_3932_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_v_3911_);
lean_inc(v_k_3910_);
lean_dec(v_impl_3838_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3932_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
lean_object* v_k_3915_; lean_object* v_v_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3928_; 
v_k_3915_ = lean_ctor_get(v_r_3909_, 1);
v_v_3916_ = lean_ctor_get(v_r_3909_, 2);
v_isSharedCheck_3928_ = !lean_is_exclusive(v_r_3909_);
if (v_isSharedCheck_3928_ == 0)
{
lean_object* v_unused_3929_; lean_object* v_unused_3930_; lean_object* v_unused_3931_; 
v_unused_3929_ = lean_ctor_get(v_r_3909_, 4);
lean_dec(v_unused_3929_);
v_unused_3930_ = lean_ctor_get(v_r_3909_, 3);
lean_dec(v_unused_3930_);
v_unused_3931_ = lean_ctor_get(v_r_3909_, 0);
lean_dec(v_unused_3931_);
v___x_3918_ = v_r_3909_;
v_isShared_3919_ = v_isSharedCheck_3928_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_v_3916_);
lean_inc(v_k_3915_);
lean_dec(v_r_3909_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3928_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3920_; lean_object* v___x_3922_; 
v___x_3920_ = lean_unsigned_to_nat(3u);
if (v_isShared_3919_ == 0)
{
lean_ctor_set(v___x_3918_, 4, v_l_3894_);
lean_ctor_set(v___x_3918_, 3, v_l_3894_);
lean_ctor_set(v___x_3918_, 2, v_v_3911_);
lean_ctor_set(v___x_3918_, 1, v_k_3910_);
lean_ctor_set(v___x_3918_, 0, v___x_3839_);
v___x_3922_ = v___x_3918_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v___x_3839_);
lean_ctor_set(v_reuseFailAlloc_3927_, 1, v_k_3910_);
lean_ctor_set(v_reuseFailAlloc_3927_, 2, v_v_3911_);
lean_ctor_set(v_reuseFailAlloc_3927_, 3, v_l_3894_);
lean_ctor_set(v_reuseFailAlloc_3927_, 4, v_l_3894_);
v___x_3922_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
lean_object* v___x_3924_; 
if (v_isShared_3914_ == 0)
{
lean_ctor_set(v___x_3913_, 4, v_l_3894_);
lean_ctor_set(v___x_3913_, 2, v_v_3781_);
lean_ctor_set(v___x_3913_, 1, v_k_3780_);
lean_ctor_set(v___x_3913_, 0, v___x_3839_);
v___x_3924_ = v___x_3913_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v___x_3839_);
lean_ctor_set(v_reuseFailAlloc_3926_, 1, v_k_3780_);
lean_ctor_set(v_reuseFailAlloc_3926_, 2, v_v_3781_);
lean_ctor_set(v_reuseFailAlloc_3926_, 3, v_l_3894_);
lean_ctor_set(v_reuseFailAlloc_3926_, 4, v_l_3894_);
v___x_3924_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
lean_object* v___x_3925_; 
v___x_3925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3920_);
lean_ctor_set(v___x_3925_, 1, v_k_3915_);
lean_ctor_set(v___x_3925_, 2, v_v_3916_);
lean_ctor_set(v___x_3925_, 3, v___x_3922_);
lean_ctor_set(v___x_3925_, 4, v___x_3924_);
return v___x_3925_;
}
}
}
}
}
else
{
lean_object* v___x_3936_; lean_object* v___x_3937_; 
v___x_3936_ = lean_unsigned_to_nat(2u);
v___x_3937_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3936_);
lean_ctor_set(v___x_3937_, 1, v_k_3780_);
lean_ctor_set(v___x_3937_, 2, v_v_3781_);
lean_ctor_set(v___x_3937_, 3, v_impl_3838_);
lean_ctor_set(v___x_3937_, 4, v_r_3909_);
return v___x_3937_;
}
}
}
}
case 1:
{
lean_object* v___x_3938_; 
lean_del_object(v___x_3785_);
lean_dec(v_v_3781_);
lean_dec(v_k_3780_);
v___x_3938_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3938_, 0, v_size_3779_);
lean_ctor_set(v___x_3938_, 1, v_k_3762_);
lean_ctor_set(v___x_3938_, 2, v_v_3763_);
lean_ctor_set(v___x_3938_, 3, v_l_3782_);
lean_ctor_set(v___x_3938_, 4, v_r_3783_);
return v___x_3938_;
}
default: 
{
lean_object* v_impl_3939_; lean_object* v___x_3940_; 
lean_del_object(v___x_3785_);
lean_dec(v_size_3779_);
v_impl_3939_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_3762_, v_v_3763_, v_r_3783_);
v___x_3940_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3782_) == 0)
{
lean_object* v_size_3941_; lean_object* v_size_3942_; lean_object* v_k_3943_; lean_object* v_v_3944_; lean_object* v_l_3945_; lean_object* v_r_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; uint8_t v___x_3949_; 
v_size_3941_ = lean_ctor_get(v_l_3782_, 0);
v_size_3942_ = lean_ctor_get(v_impl_3939_, 0);
v_k_3943_ = lean_ctor_get(v_impl_3939_, 1);
v_v_3944_ = lean_ctor_get(v_impl_3939_, 2);
v_l_3945_ = lean_ctor_get(v_impl_3939_, 3);
v_r_3946_ = lean_ctor_get(v_impl_3939_, 4);
v___x_3947_ = lean_unsigned_to_nat(3u);
v___x_3948_ = lean_nat_mul(v___x_3947_, v_size_3941_);
v___x_3949_ = lean_nat_dec_lt(v___x_3948_, v_size_3942_);
lean_dec(v___x_3948_);
if (v___x_3949_ == 0)
{
lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; 
v___x_3950_ = lean_nat_add(v___x_3940_, v_size_3941_);
v___x_3951_ = lean_nat_add(v___x_3950_, v_size_3942_);
lean_dec(v___x_3950_);
v___x_3952_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3952_, 0, v___x_3951_);
lean_ctor_set(v___x_3952_, 1, v_k_3780_);
lean_ctor_set(v___x_3952_, 2, v_v_3781_);
lean_ctor_set(v___x_3952_, 3, v_l_3782_);
lean_ctor_set(v___x_3952_, 4, v_impl_3939_);
return v___x_3952_;
}
else
{
lean_object* v___x_3954_; uint8_t v_isShared_3955_; uint8_t v_isSharedCheck_3987_; 
lean_inc(v_r_3946_);
lean_inc(v_l_3945_);
lean_inc(v_v_3944_);
lean_inc(v_k_3943_);
lean_inc(v_size_3942_);
v_isSharedCheck_3987_ = !lean_is_exclusive(v_impl_3939_);
if (v_isSharedCheck_3987_ == 0)
{
lean_object* v_unused_3988_; lean_object* v_unused_3989_; lean_object* v_unused_3990_; lean_object* v_unused_3991_; lean_object* v_unused_3992_; 
v_unused_3988_ = lean_ctor_get(v_impl_3939_, 4);
lean_dec(v_unused_3988_);
v_unused_3989_ = lean_ctor_get(v_impl_3939_, 3);
lean_dec(v_unused_3989_);
v_unused_3990_ = lean_ctor_get(v_impl_3939_, 2);
lean_dec(v_unused_3990_);
v_unused_3991_ = lean_ctor_get(v_impl_3939_, 1);
lean_dec(v_unused_3991_);
v_unused_3992_ = lean_ctor_get(v_impl_3939_, 0);
lean_dec(v_unused_3992_);
v___x_3954_ = v_impl_3939_;
v_isShared_3955_ = v_isSharedCheck_3987_;
goto v_resetjp_3953_;
}
else
{
lean_dec(v_impl_3939_);
v___x_3954_ = lean_box(0);
v_isShared_3955_ = v_isSharedCheck_3987_;
goto v_resetjp_3953_;
}
v_resetjp_3953_:
{
lean_object* v_size_3956_; lean_object* v_k_3957_; lean_object* v_v_3958_; lean_object* v_l_3959_; lean_object* v_r_3960_; lean_object* v_size_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; uint8_t v___x_3964_; 
v_size_3956_ = lean_ctor_get(v_l_3945_, 0);
v_k_3957_ = lean_ctor_get(v_l_3945_, 1);
v_v_3958_ = lean_ctor_get(v_l_3945_, 2);
v_l_3959_ = lean_ctor_get(v_l_3945_, 3);
v_r_3960_ = lean_ctor_get(v_l_3945_, 4);
v_size_3961_ = lean_ctor_get(v_r_3946_, 0);
v___x_3962_ = lean_unsigned_to_nat(2u);
v___x_3963_ = lean_nat_mul(v___x_3962_, v_size_3961_);
v___x_3964_ = lean_nat_dec_lt(v_size_3956_, v___x_3963_);
lean_dec(v___x_3963_);
if (v___x_3964_ == 0)
{
lean_object* v___x_3965_; lean_object* v___x_3966_; 
lean_inc(v_size_3961_);
lean_inc(v_r_3960_);
lean_inc(v_l_3959_);
lean_inc(v_v_3958_);
lean_inc(v_k_3957_);
lean_del_object(v___x_3954_);
lean_dec(v_l_3945_);
v___x_3965_ = lean_nat_add(v___x_3940_, v_size_3941_);
v___x_3966_ = lean_nat_add(v___x_3965_, v_size_3942_);
lean_dec(v_size_3942_);
if (lean_obj_tag(v_l_3959_) == 0)
{
lean_object* v_size_3967_; 
v_size_3967_ = lean_ctor_get(v_l_3959_, 0);
lean_inc(v_size_3967_);
v___y_3819_ = v_l_3959_;
v___y_3820_ = v_r_3960_;
v___y_3821_ = v_r_3946_;
v___y_3822_ = v___x_3940_;
v___y_3823_ = v_k_3943_;
v___y_3824_ = v_k_3957_;
v___y_3825_ = v___x_3966_;
v___y_3826_ = v_v_3958_;
v___y_3827_ = v_size_3961_;
v___y_3828_ = v_v_3944_;
v___y_3829_ = v___x_3965_;
v___y_3830_ = v_size_3967_;
goto v___jp_3818_;
}
else
{
lean_object* v___x_3968_; 
v___x_3968_ = lean_unsigned_to_nat(0u);
v___y_3819_ = v_l_3959_;
v___y_3820_ = v_r_3960_;
v___y_3821_ = v_r_3946_;
v___y_3822_ = v___x_3940_;
v___y_3823_ = v_k_3943_;
v___y_3824_ = v_k_3957_;
v___y_3825_ = v___x_3966_;
v___y_3826_ = v_v_3958_;
v___y_3827_ = v_size_3961_;
v___y_3828_ = v_v_3944_;
v___y_3829_ = v___x_3965_;
v___y_3830_ = v___x_3968_;
goto v___jp_3818_;
}
}
else
{
lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3973_; 
v___x_3969_ = lean_nat_add(v___x_3940_, v_size_3941_);
v___x_3970_ = lean_nat_add(v___x_3969_, v_size_3942_);
lean_dec(v_size_3942_);
v___x_3971_ = lean_nat_add(v___x_3969_, v_size_3956_);
lean_dec(v___x_3969_);
lean_inc_ref(v_l_3782_);
if (v_isShared_3955_ == 0)
{
lean_ctor_set(v___x_3954_, 4, v_l_3945_);
lean_ctor_set(v___x_3954_, 3, v_l_3782_);
lean_ctor_set(v___x_3954_, 2, v_v_3781_);
lean_ctor_set(v___x_3954_, 1, v_k_3780_);
lean_ctor_set(v___x_3954_, 0, v___x_3971_);
v___x_3973_ = v___x_3954_;
goto v_reusejp_3972_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v___x_3971_);
lean_ctor_set(v_reuseFailAlloc_3986_, 1, v_k_3780_);
lean_ctor_set(v_reuseFailAlloc_3986_, 2, v_v_3781_);
lean_ctor_set(v_reuseFailAlloc_3986_, 3, v_l_3782_);
lean_ctor_set(v_reuseFailAlloc_3986_, 4, v_l_3945_);
v___x_3973_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3972_;
}
v_reusejp_3972_:
{
lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3980_; 
v_isSharedCheck_3980_ = !lean_is_exclusive(v_l_3782_);
if (v_isSharedCheck_3980_ == 0)
{
lean_object* v_unused_3981_; lean_object* v_unused_3982_; lean_object* v_unused_3983_; lean_object* v_unused_3984_; lean_object* v_unused_3985_; 
v_unused_3981_ = lean_ctor_get(v_l_3782_, 4);
lean_dec(v_unused_3981_);
v_unused_3982_ = lean_ctor_get(v_l_3782_, 3);
lean_dec(v_unused_3982_);
v_unused_3983_ = lean_ctor_get(v_l_3782_, 2);
lean_dec(v_unused_3983_);
v_unused_3984_ = lean_ctor_get(v_l_3782_, 1);
lean_dec(v_unused_3984_);
v_unused_3985_ = lean_ctor_get(v_l_3782_, 0);
lean_dec(v_unused_3985_);
v___x_3975_ = v_l_3782_;
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
else
{
lean_dec(v_l_3782_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3978_; 
if (v_isShared_3976_ == 0)
{
lean_ctor_set(v___x_3975_, 4, v_r_3946_);
lean_ctor_set(v___x_3975_, 3, v___x_3973_);
lean_ctor_set(v___x_3975_, 2, v_v_3944_);
lean_ctor_set(v___x_3975_, 1, v_k_3943_);
lean_ctor_set(v___x_3975_, 0, v___x_3970_);
v___x_3978_ = v___x_3975_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v___x_3970_);
lean_ctor_set(v_reuseFailAlloc_3979_, 1, v_k_3943_);
lean_ctor_set(v_reuseFailAlloc_3979_, 2, v_v_3944_);
lean_ctor_set(v_reuseFailAlloc_3979_, 3, v___x_3973_);
lean_ctor_set(v_reuseFailAlloc_3979_, 4, v_r_3946_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
return v___x_3978_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3993_; 
v_l_3993_ = lean_ctor_get(v_impl_3939_, 3);
lean_inc(v_l_3993_);
if (lean_obj_tag(v_l_3993_) == 0)
{
lean_object* v_r_3994_; lean_object* v_k_3995_; lean_object* v_v_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4017_; 
v_r_3994_ = lean_ctor_get(v_impl_3939_, 4);
v_k_3995_ = lean_ctor_get(v_impl_3939_, 1);
v_v_3996_ = lean_ctor_get(v_impl_3939_, 2);
v_isSharedCheck_4017_ = !lean_is_exclusive(v_impl_3939_);
if (v_isSharedCheck_4017_ == 0)
{
lean_object* v_unused_4018_; lean_object* v_unused_4019_; 
v_unused_4018_ = lean_ctor_get(v_impl_3939_, 3);
lean_dec(v_unused_4018_);
v_unused_4019_ = lean_ctor_get(v_impl_3939_, 0);
lean_dec(v_unused_4019_);
v___x_3998_ = v_impl_3939_;
v_isShared_3999_ = v_isSharedCheck_4017_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_r_3994_);
lean_inc(v_v_3996_);
lean_inc(v_k_3995_);
lean_dec(v_impl_3939_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4017_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v_k_4000_; lean_object* v_v_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4013_; 
v_k_4000_ = lean_ctor_get(v_l_3993_, 1);
v_v_4001_ = lean_ctor_get(v_l_3993_, 2);
v_isSharedCheck_4013_ = !lean_is_exclusive(v_l_3993_);
if (v_isSharedCheck_4013_ == 0)
{
lean_object* v_unused_4014_; lean_object* v_unused_4015_; lean_object* v_unused_4016_; 
v_unused_4014_ = lean_ctor_get(v_l_3993_, 4);
lean_dec(v_unused_4014_);
v_unused_4015_ = lean_ctor_get(v_l_3993_, 3);
lean_dec(v_unused_4015_);
v_unused_4016_ = lean_ctor_get(v_l_3993_, 0);
lean_dec(v_unused_4016_);
v___x_4003_ = v_l_3993_;
v_isShared_4004_ = v_isSharedCheck_4013_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_v_4001_);
lean_inc(v_k_4000_);
lean_dec(v_l_3993_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4013_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4005_; lean_object* v___x_4007_; 
v___x_4005_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3994_, 2);
if (v_isShared_4004_ == 0)
{
lean_ctor_set(v___x_4003_, 4, v_r_3994_);
lean_ctor_set(v___x_4003_, 3, v_r_3994_);
lean_ctor_set(v___x_4003_, 2, v_v_3781_);
lean_ctor_set(v___x_4003_, 1, v_k_3780_);
lean_ctor_set(v___x_4003_, 0, v___x_3940_);
v___x_4007_ = v___x_4003_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v___x_3940_);
lean_ctor_set(v_reuseFailAlloc_4012_, 1, v_k_3780_);
lean_ctor_set(v_reuseFailAlloc_4012_, 2, v_v_3781_);
lean_ctor_set(v_reuseFailAlloc_4012_, 3, v_r_3994_);
lean_ctor_set(v_reuseFailAlloc_4012_, 4, v_r_3994_);
v___x_4007_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
lean_object* v___x_4009_; 
lean_inc(v_r_3994_);
if (v_isShared_3999_ == 0)
{
lean_ctor_set(v___x_3998_, 3, v_r_3994_);
lean_ctor_set(v___x_3998_, 0, v___x_3940_);
v___x_4009_ = v___x_3998_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v___x_3940_);
lean_ctor_set(v_reuseFailAlloc_4011_, 1, v_k_3995_);
lean_ctor_set(v_reuseFailAlloc_4011_, 2, v_v_3996_);
lean_ctor_set(v_reuseFailAlloc_4011_, 3, v_r_3994_);
lean_ctor_set(v_reuseFailAlloc_4011_, 4, v_r_3994_);
v___x_4009_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
lean_object* v___x_4010_; 
v___x_4010_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4010_, 0, v___x_4005_);
lean_ctor_set(v___x_4010_, 1, v_k_4000_);
lean_ctor_set(v___x_4010_, 2, v_v_4001_);
lean_ctor_set(v___x_4010_, 3, v___x_4007_);
lean_ctor_set(v___x_4010_, 4, v___x_4009_);
return v___x_4010_;
}
}
}
}
}
else
{
lean_object* v_r_4020_; 
v_r_4020_ = lean_ctor_get(v_impl_3939_, 4);
lean_inc(v_r_4020_);
if (lean_obj_tag(v_r_4020_) == 0)
{
lean_object* v_k_4021_; lean_object* v_v_4022_; lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4031_; 
v_k_4021_ = lean_ctor_get(v_impl_3939_, 1);
v_v_4022_ = lean_ctor_get(v_impl_3939_, 2);
v_isSharedCheck_4031_ = !lean_is_exclusive(v_impl_3939_);
if (v_isSharedCheck_4031_ == 0)
{
lean_object* v_unused_4032_; lean_object* v_unused_4033_; lean_object* v_unused_4034_; 
v_unused_4032_ = lean_ctor_get(v_impl_3939_, 4);
lean_dec(v_unused_4032_);
v_unused_4033_ = lean_ctor_get(v_impl_3939_, 3);
lean_dec(v_unused_4033_);
v_unused_4034_ = lean_ctor_get(v_impl_3939_, 0);
lean_dec(v_unused_4034_);
v___x_4024_ = v_impl_3939_;
v_isShared_4025_ = v_isSharedCheck_4031_;
goto v_resetjp_4023_;
}
else
{
lean_inc(v_v_4022_);
lean_inc(v_k_4021_);
lean_dec(v_impl_3939_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4031_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
lean_object* v___x_4026_; lean_object* v___x_4028_; 
v___x_4026_ = lean_unsigned_to_nat(3u);
if (v_isShared_4025_ == 0)
{
lean_ctor_set(v___x_4024_, 4, v_l_3993_);
lean_ctor_set(v___x_4024_, 2, v_v_3781_);
lean_ctor_set(v___x_4024_, 1, v_k_3780_);
lean_ctor_set(v___x_4024_, 0, v___x_3940_);
v___x_4028_ = v___x_4024_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4030_; 
v_reuseFailAlloc_4030_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4030_, 0, v___x_3940_);
lean_ctor_set(v_reuseFailAlloc_4030_, 1, v_k_3780_);
lean_ctor_set(v_reuseFailAlloc_4030_, 2, v_v_3781_);
lean_ctor_set(v_reuseFailAlloc_4030_, 3, v_l_3993_);
lean_ctor_set(v_reuseFailAlloc_4030_, 4, v_l_3993_);
v___x_4028_ = v_reuseFailAlloc_4030_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
lean_object* v___x_4029_; 
v___x_4029_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4029_, 0, v___x_4026_);
lean_ctor_set(v___x_4029_, 1, v_k_4021_);
lean_ctor_set(v___x_4029_, 2, v_v_4022_);
lean_ctor_set(v___x_4029_, 3, v___x_4028_);
lean_ctor_set(v___x_4029_, 4, v_r_4020_);
return v___x_4029_;
}
}
}
else
{
lean_object* v___x_4035_; lean_object* v___x_4036_; 
v___x_4035_ = lean_unsigned_to_nat(2u);
v___x_4036_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4036_, 0, v___x_4035_);
lean_ctor_set(v___x_4036_, 1, v_k_3780_);
lean_ctor_set(v___x_4036_, 2, v_v_3781_);
lean_ctor_set(v___x_4036_, 3, v_r_4020_);
lean_ctor_set(v___x_4036_, 4, v_impl_3939_);
return v___x_4036_;
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
lean_object* v___x_4044_; lean_object* v___x_4045_; 
v___x_4044_ = lean_unsigned_to_nat(1u);
v___x_4045_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4045_, 0, v___x_4044_);
lean_ctor_set(v___x_4045_, 1, v_k_3762_);
lean_ctor_set(v___x_4045_, 2, v_v_3763_);
lean_ctor_set(v___x_4045_, 3, v_t_3764_);
lean_ctor_set(v___x_4045_, 4, v_t_3764_);
return v___x_4045_;
}
v___jp_3765_:
{
lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; 
v___x_3776_ = lean_nat_add(v___y_3769_, v___y_3775_);
lean_dec(v___y_3775_);
lean_dec(v___y_3769_);
v___x_3777_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3776_);
lean_ctor_set(v___x_3777_, 1, v___y_3770_);
lean_ctor_set(v___x_3777_, 2, v___y_3774_);
lean_ctor_set(v___x_3777_, 3, v___y_3768_);
lean_ctor_set(v___x_3777_, 4, v___y_3767_);
v___x_3778_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3778_, 0, v___y_3772_);
lean_ctor_set(v___x_3778_, 1, v___y_3771_);
lean_ctor_set(v___x_3778_, 2, v___y_3773_);
lean_ctor_set(v___x_3778_, 3, v___y_3766_);
lean_ctor_set(v___x_3778_, 4, v___x_3777_);
return v___x_3778_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(lean_object* v_t_4046_, lean_object* v_k_4047_, lean_object* v_fallback_4048_){
_start:
{
if (lean_obj_tag(v_t_4046_) == 0)
{
lean_object* v_k_4049_; lean_object* v_v_4050_; lean_object* v_l_4051_; lean_object* v_r_4052_; uint8_t v___y_4054_; lean_object* v_fst_4057_; lean_object* v_snd_4058_; lean_object* v_fst_4059_; lean_object* v_snd_4060_; uint8_t v___x_4061_; 
v_k_4049_ = lean_ctor_get(v_t_4046_, 1);
v_v_4050_ = lean_ctor_get(v_t_4046_, 2);
v_l_4051_ = lean_ctor_get(v_t_4046_, 3);
v_r_4052_ = lean_ctor_get(v_t_4046_, 4);
v_fst_4057_ = lean_ctor_get(v_k_4047_, 0);
v_snd_4058_ = lean_ctor_get(v_k_4047_, 1);
v_fst_4059_ = lean_ctor_get(v_k_4049_, 0);
v_snd_4060_ = lean_ctor_get(v_k_4049_, 1);
v___x_4061_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_fst_4057_, v_fst_4059_);
if (v___x_4061_ == 1)
{
uint8_t v___x_4062_; 
v___x_4062_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_snd_4058_, v_snd_4060_);
v___y_4054_ = v___x_4062_;
goto v___jp_4053_;
}
else
{
v___y_4054_ = v___x_4061_;
goto v___jp_4053_;
}
v___jp_4053_:
{
switch(v___y_4054_)
{
case 0:
{
v_t_4046_ = v_l_4051_;
goto _start;
}
case 1:
{
lean_inc(v_v_4050_);
return v_v_4050_;
}
default: 
{
v_t_4046_ = v_r_4052_;
goto _start;
}
}
}
}
else
{
lean_inc(v_fallback_4048_);
return v_fallback_4048_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg___boxed(lean_object* v_t_4063_, lean_object* v_k_4064_, lean_object* v_fallback_4065_){
_start:
{
lean_object* v_res_4066_; 
v_res_4066_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_t_4063_, v_k_4064_, v_fallback_4065_);
lean_dec(v_fallback_4065_);
lean_dec_ref(v_k_4064_);
lean_dec(v_t_4063_);
return v_res_4066_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(lean_object* v___x_4067_, lean_object* v_as_4068_, size_t v_sz_4069_, size_t v_i_4070_, lean_object* v_b_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_){
_start:
{
uint8_t v___x_4075_; 
v___x_4075_ = lean_usize_dec_lt(v_i_4070_, v_sz_4069_);
if (v___x_4075_ == 0)
{
lean_object* v___x_4076_; 
lean_dec(v___x_4067_);
v___x_4076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4076_, 0, v_b_4071_);
return v___x_4076_;
}
else
{
lean_object* v_a_4077_; lean_object* v_fst_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4106_; 
v_a_4077_ = lean_array_uget(v_as_4068_, v_i_4070_);
v_fst_4078_ = lean_ctor_get(v_a_4077_, 0);
v_isSharedCheck_4106_ = !lean_is_exclusive(v_a_4077_);
if (v_isSharedCheck_4106_ == 0)
{
lean_object* v_unused_4107_; 
v_unused_4107_ = lean_ctor_get(v_a_4077_, 1);
lean_dec(v_unused_4107_);
v___x_4080_ = v_a_4077_;
v_isShared_4081_ = v_isSharedCheck_4106_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_fst_4078_);
lean_dec(v_a_4077_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4106_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4082_ = lean_unsigned_to_nat(0u);
lean_inc(v_fst_4078_);
v___x_4083_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_fst_4078_, v___y_4072_, v___y_4073_);
if (lean_obj_tag(v___x_4083_) == 0)
{
lean_object* v_a_4084_; lean_object* v___y_4086_; 
v_a_4084_ = lean_ctor_get(v___x_4083_, 0);
lean_inc(v_a_4084_);
lean_dec_ref_known(v___x_4083_, 1);
if (lean_obj_tag(v_a_4084_) == 0)
{
lean_inc(v___x_4067_);
v___y_4086_ = v___x_4067_;
goto v___jp_4085_;
}
else
{
lean_object* v_val_4097_; 
v_val_4097_ = lean_ctor_get(v_a_4084_, 0);
lean_inc(v_val_4097_);
lean_dec_ref_known(v_a_4084_, 1);
v___y_4086_ = v_val_4097_;
goto v___jp_4085_;
}
v___jp_4085_:
{
lean_object* v___x_4088_; 
if (v_isShared_4081_ == 0)
{
lean_ctor_set(v___x_4080_, 1, v_fst_4078_);
lean_ctor_set(v___x_4080_, 0, v___y_4086_);
v___x_4088_ = v___x_4080_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v___y_4086_);
lean_ctor_set(v_reuseFailAlloc_4096_, 1, v_fst_4078_);
v___x_4088_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; size_t v___x_4093_; size_t v___x_4094_; 
v___x_4089_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_b_4071_, v___x_4088_, v___x_4082_);
v___x_4090_ = lean_unsigned_to_nat(1u);
v___x_4091_ = lean_nat_add(v___x_4089_, v___x_4090_);
lean_dec(v___x_4089_);
v___x_4092_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v___x_4088_, v___x_4091_, v_b_4071_);
v___x_4093_ = ((size_t)1ULL);
v___x_4094_ = lean_usize_add(v_i_4070_, v___x_4093_);
v_i_4070_ = v___x_4094_;
v_b_4071_ = v___x_4092_;
goto _start;
}
}
}
else
{
lean_object* v_a_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4105_; 
lean_del_object(v___x_4080_);
lean_dec(v_fst_4078_);
lean_dec(v_b_4071_);
lean_dec(v___x_4067_);
v_a_4098_ = lean_ctor_get(v___x_4083_, 0);
v_isSharedCheck_4105_ = !lean_is_exclusive(v___x_4083_);
if (v_isSharedCheck_4105_ == 0)
{
v___x_4100_ = v___x_4083_;
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_a_4098_);
lean_dec(v___x_4083_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
lean_object* v___x_4103_; 
if (v_isShared_4101_ == 0)
{
v___x_4103_ = v___x_4100_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v_a_4098_);
v___x_4103_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
return v___x_4103_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7___boxed(lean_object* v___x_4108_, lean_object* v_as_4109_, lean_object* v_sz_4110_, lean_object* v_i_4111_, lean_object* v_b_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_){
_start:
{
size_t v_sz_boxed_4116_; size_t v_i_boxed_4117_; lean_object* v_res_4118_; 
v_sz_boxed_4116_ = lean_unbox_usize(v_sz_4110_);
lean_dec(v_sz_4110_);
v_i_boxed_4117_ = lean_unbox_usize(v_i_4111_);
lean_dec(v_i_4111_);
v_res_4118_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(v___x_4108_, v_as_4109_, v_sz_boxed_4116_, v_i_boxed_4117_, v_b_4112_, v___y_4113_, v___y_4114_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
lean_dec_ref(v_as_4109_);
return v_res_4118_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(lean_object* v_fst_4119_, lean_object* v_init_4120_, lean_object* v_x_4121_){
_start:
{
if (lean_obj_tag(v_x_4121_) == 0)
{
lean_object* v_k_4123_; lean_object* v_v_4124_; lean_object* v_l_4125_; lean_object* v_r_4126_; uint8_t v___x_4127_; lean_object* v___x_4128_; lean_object* v_a_4129_; lean_object* v_a_4130_; lean_object* v_fst_4131_; lean_object* v_snd_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4146_; 
v_k_4123_ = lean_ctor_get(v_x_4121_, 1);
lean_inc(v_k_4123_);
v_v_4124_ = lean_ctor_get(v_x_4121_, 2);
lean_inc(v_v_4124_);
v_l_4125_ = lean_ctor_get(v_x_4121_, 3);
lean_inc(v_l_4125_);
v_r_4126_ = lean_ctor_get(v_x_4121_, 4);
lean_inc(v_r_4126_);
lean_dec_ref_known(v_x_4121_, 5);
v___x_4127_ = 1;
lean_inc_ref(v_fst_4119_);
v___x_4128_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4119_, v_init_4120_, v_l_4125_);
v_a_4129_ = lean_ctor_get(v___x_4128_, 0);
lean_inc(v_a_4129_);
lean_dec_ref(v___x_4128_);
v_a_4130_ = lean_ctor_get(v_a_4129_, 0);
lean_inc(v_a_4130_);
lean_dec(v_a_4129_);
v_fst_4131_ = lean_ctor_get(v_k_4123_, 0);
v_snd_4132_ = lean_ctor_get(v_k_4123_, 1);
v_isSharedCheck_4146_ = !lean_is_exclusive(v_k_4123_);
if (v_isSharedCheck_4146_ == 0)
{
v___x_4134_ = v_k_4123_;
v_isShared_4135_ = v_isSharedCheck_4146_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_snd_4132_);
lean_inc(v_fst_4131_);
lean_dec(v_k_4123_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4146_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v_optName_4136_; lean_object* v___x_4137_; lean_object* v___x_4139_; 
v_optName_4136_ = lean_ctor_get(v_fst_4119_, 1);
lean_inc(v_optName_4136_);
v___x_4137_ = l_Lean_Name_toString(v_optName_4136_, v___x_4127_);
if (v_isShared_4135_ == 0)
{
lean_ctor_set_tag(v___x_4134_, 1);
v___x_4139_ = v___x_4134_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4145_; 
v_reuseFailAlloc_4145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4145_, 0, v_fst_4131_);
lean_ctor_set(v_reuseFailAlloc_4145_, 1, v_snd_4132_);
v___x_4139_ = v_reuseFailAlloc_4145_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
double v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; 
v___x_4140_ = lean_float_of_nat(v_v_4124_);
v___x_4141_ = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_float(v___x_4141_, 0, v___x_4140_);
v___x_4142_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4142_, 0, v___x_4137_);
lean_ctor_set(v___x_4142_, 1, v___x_4139_);
lean_ctor_set(v___x_4142_, 2, v___x_4141_);
v___x_4143_ = lean_array_push(v_a_4130_, v___x_4142_);
v_init_4120_ = v___x_4143_;
v_x_4121_ = v_r_4126_;
goto _start;
}
}
}
else
{
lean_object* v___x_4147_; lean_object* v___x_4148_; 
lean_dec_ref(v_fst_4119_);
v___x_4147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4147_, 0, v_init_4120_);
v___x_4148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4148_, 0, v___x_4147_);
return v___x_4148_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg___boxed(lean_object* v_fst_4149_, lean_object* v_init_4150_, lean_object* v_x_4151_, lean_object* v___y_4152_){
_start:
{
lean_object* v_res_4153_; 
v_res_4153_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4149_, v_init_4150_, v_x_4151_);
return v_res_4153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(lean_object* v___x_4154_, lean_object* v_as_4155_, size_t v_sz_4156_, size_t v_i_4157_, lean_object* v_b_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_){
_start:
{
lean_object* v_a_4163_; uint8_t v___x_4167_; 
v___x_4167_ = lean_usize_dec_lt(v_i_4157_, v_sz_4156_);
if (v___x_4167_ == 0)
{
lean_object* v___x_4168_; 
lean_dec(v___x_4154_);
v___x_4168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4168_, 0, v_b_4158_);
return v___x_4168_;
}
else
{
lean_object* v_a_4169_; lean_object* v_snd_4170_; lean_object* v_fst_4171_; lean_object* v_size_4172_; lean_object* v_buckets_4173_; lean_object* v___x_4174_; lean_object* v___y_4176_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; uint8_t v___x_4213_; 
v_a_4169_ = lean_array_uget_borrowed(v_as_4155_, v_i_4157_);
v_snd_4170_ = lean_ctor_get(v_a_4169_, 1);
v_fst_4171_ = lean_ctor_get(v_a_4169_, 0);
v_size_4172_ = lean_ctor_get(v_snd_4170_, 0);
v_buckets_4173_ = lean_ctor_get(v_snd_4170_, 1);
v___x_4174_ = lean_box(1);
v___x_4210_ = lean_mk_empty_array_with_capacity(v_size_4172_);
v___x_4211_ = lean_unsigned_to_nat(0u);
v___x_4212_ = lean_array_get_size(v_buckets_4173_);
v___x_4213_ = lean_nat_dec_lt(v___x_4211_, v___x_4212_);
if (v___x_4213_ == 0)
{
v___y_4176_ = v___x_4210_;
goto v___jp_4175_;
}
else
{
size_t v___x_4214_; size_t v___x_4215_; lean_object* v___x_4216_; 
v___x_4214_ = ((size_t)0ULL);
v___x_4215_ = lean_usize_of_nat(v___x_4212_);
v___x_4216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_buckets_4173_, v___x_4214_, v___x_4215_, v___x_4210_);
v___y_4176_ = v___x_4216_;
goto v___jp_4175_;
}
v___jp_4175_:
{
size_t v_sz_4177_; size_t v___x_4178_; lean_object* v___x_4179_; 
v_sz_4177_ = lean_array_size(v___y_4176_);
v___x_4178_ = ((size_t)0ULL);
lean_inc(v___x_4154_);
v___x_4179_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(v___x_4154_, v___y_4176_, v_sz_4177_, v___x_4178_, v___x_4174_, v___y_4159_, v___y_4160_);
lean_dec_ref(v___y_4176_);
if (lean_obj_tag(v___x_4179_) == 0)
{
lean_object* v_a_4180_; lean_object* v___x_4181_; 
v_a_4180_ = lean_ctor_get(v___x_4179_, 0);
lean_inc(v_a_4180_);
lean_dec_ref_known(v___x_4179_, 1);
lean_inc(v_fst_4171_);
v___x_4181_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4171_, v_b_4158_, v_a_4180_);
if (lean_obj_tag(v___x_4181_) == 0)
{
lean_object* v_a_4182_; lean_object* v_a_4183_; 
v_a_4182_ = lean_ctor_get(v___x_4181_, 0);
lean_inc(v_a_4182_);
lean_dec_ref_known(v___x_4181_, 1);
v_a_4183_ = lean_ctor_get(v_a_4182_, 0);
lean_inc(v_a_4183_);
lean_dec(v_a_4182_);
v_a_4163_ = v_a_4183_;
goto v___jp_4162_;
}
else
{
if (lean_obj_tag(v___x_4181_) == 0)
{
lean_object* v_a_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4193_; 
v_a_4184_ = lean_ctor_get(v___x_4181_, 0);
v_isSharedCheck_4193_ = !lean_is_exclusive(v___x_4181_);
if (v_isSharedCheck_4193_ == 0)
{
v___x_4186_ = v___x_4181_;
v_isShared_4187_ = v_isSharedCheck_4193_;
goto v_resetjp_4185_;
}
else
{
lean_inc(v_a_4184_);
lean_dec(v___x_4181_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4193_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
if (lean_obj_tag(v_a_4184_) == 0)
{
lean_object* v_a_4188_; lean_object* v___x_4190_; 
lean_dec(v___x_4154_);
v_a_4188_ = lean_ctor_get(v_a_4184_, 0);
lean_inc(v_a_4188_);
lean_dec_ref_known(v_a_4184_, 1);
if (v_isShared_4187_ == 0)
{
lean_ctor_set_tag(v___x_4186_, 0);
lean_ctor_set(v___x_4186_, 0, v_a_4188_);
v___x_4190_ = v___x_4186_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v_a_4188_);
v___x_4190_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
return v___x_4190_;
}
}
else
{
lean_object* v_a_4192_; 
lean_del_object(v___x_4186_);
v_a_4192_ = lean_ctor_get(v_a_4184_, 0);
lean_inc(v_a_4192_);
lean_dec_ref_known(v_a_4184_, 1);
v_a_4163_ = v_a_4192_;
goto v___jp_4162_;
}
}
}
else
{
lean_object* v_a_4194_; lean_object* v___x_4196_; uint8_t v_isShared_4197_; uint8_t v_isSharedCheck_4201_; 
lean_dec(v___x_4154_);
v_a_4194_ = lean_ctor_get(v___x_4181_, 0);
v_isSharedCheck_4201_ = !lean_is_exclusive(v___x_4181_);
if (v_isSharedCheck_4201_ == 0)
{
v___x_4196_ = v___x_4181_;
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
else
{
lean_inc(v_a_4194_);
lean_dec(v___x_4181_);
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
else
{
lean_object* v_a_4202_; lean_object* v___x_4204_; uint8_t v_isShared_4205_; uint8_t v_isSharedCheck_4209_; 
lean_dec_ref(v_b_4158_);
lean_dec(v___x_4154_);
v_a_4202_ = lean_ctor_get(v___x_4179_, 0);
v_isSharedCheck_4209_ = !lean_is_exclusive(v___x_4179_);
if (v_isSharedCheck_4209_ == 0)
{
v___x_4204_ = v___x_4179_;
v_isShared_4205_ = v_isSharedCheck_4209_;
goto v_resetjp_4203_;
}
else
{
lean_inc(v_a_4202_);
lean_dec(v___x_4179_);
v___x_4204_ = lean_box(0);
v_isShared_4205_ = v_isSharedCheck_4209_;
goto v_resetjp_4203_;
}
v_resetjp_4203_:
{
lean_object* v___x_4207_; 
if (v_isShared_4205_ == 0)
{
v___x_4207_ = v___x_4204_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v_a_4202_);
v___x_4207_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
return v___x_4207_;
}
}
}
}
}
v___jp_4162_:
{
size_t v___x_4164_; size_t v___x_4165_; 
v___x_4164_ = ((size_t)1ULL);
v___x_4165_ = lean_usize_add(v_i_4157_, v___x_4164_);
v_i_4157_ = v___x_4165_;
v_b_4158_ = v_a_4163_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9___boxed(lean_object* v___x_4217_, lean_object* v_as_4218_, lean_object* v_sz_4219_, lean_object* v_i_4220_, lean_object* v_b_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_){
_start:
{
size_t v_sz_boxed_4225_; size_t v_i_boxed_4226_; lean_object* v_res_4227_; 
v_sz_boxed_4225_ = lean_unbox_usize(v_sz_4219_);
lean_dec(v_sz_4219_);
v_i_boxed_4226_ = lean_unbox_usize(v_i_4220_);
lean_dec(v_i_4220_);
v_res_4227_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(v___x_4217_, v_as_4218_, v_sz_boxed_4225_, v_i_boxed_4226_, v_b_4221_, v___y_4222_, v___y_4223_);
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4222_);
lean_dec_ref(v_as_4218_);
return v_res_4227_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5(void){
_start:
{
lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; 
v___x_4234_ = l_Lean_maxRecDepth;
v___x_4235_ = l_Lean_Options_empty;
v___x_4236_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(v___x_4235_, v___x_4234_);
return v___x_4236_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(lean_object* v_args_4237_, lean_object* v_linterOpts_4238_, lean_object* v_sp_4239_, lean_object* v_env_4240_, lean_object* v_mod_4241_){
_start:
{
lean_object* v_a_4244_; lean_object* v_msg_4248_; lean_object* v_a_4253_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; uint16_t v___x_4278_; uint8_t v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; uint8_t v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v_a_4294_; lean_object* v___y_4298_; uint8_t v___y_4301_; lean_object* v___y_4302_; uint8_t v___y_4303_; lean_object* v___y_4304_; lean_object* v___y_4305_; lean_object* v___y_4306_; lean_object* v___y_4307_; uint8_t v___y_4308_; uint8_t v___y_4378_; lean_object* v___y_4379_; lean_object* v___y_4380_; lean_object* v___y_4381_; lean_object* v___y_4382_; uint8_t v___y_4383_; uint8_t v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v___y_4397_; lean_object* v_fileName_4423_; lean_object* v_fileMap_4424_; lean_object* v_currNamespace_4425_; lean_object* v_openDecls_4426_; lean_object* v_initHeartbeats_4427_; lean_object* v_maxHeartbeats_4428_; lean_object* v_quotContext_4429_; lean_object* v_currMacroScope_4430_; lean_object* v_cancelTk_x3f_4431_; lean_object* v_inheritedTraceOptions_4432_; lean_object* v_currRecDepth_4433_; lean_object* v_ref_4434_; uint8_t v_suppressElabErrors_4435_; uint8_t v_isRecordingDeps_4436_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; uint8_t v___y_4458_; lean_object* v_env_4479_; uint8_t v___x_4480_; uint8_t v___x_4481_; 
v___x_4267_ = l_Lean_Name_getRoot(v_mod_4241_);
v___x_4268_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_4269_ = l_Lean_instInhabitedFileMap_default;
v___x_4270_ = l_Lean_Options_empty;
v___x_4271_ = lean_box(0);
v___x_4272_ = lean_box(0);
v___x_4273_ = lean_unsigned_to_nat(0u);
v___x_4274_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5);
v___x_4275_ = l_Lean_firstFrontendMacroScope;
v___x_4276_ = lean_box(0);
v___x_4277_ = lean_box(0);
v___x_4278_ = lean_uint16_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_4279_ = 0;
v___x_4280_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7);
v___x_4281_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10));
v___x_4282_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11));
v___x_4283_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14);
v___x_4284_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_4285_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___closed__0));
v___x_4286_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18);
v___x_4287_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_4288_ = 1;
v___x_4289_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
v___x_4290_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4290_, 0, v_env_4240_);
lean_ctor_set(v___x_4290_, 1, v___x_4280_);
lean_ctor_set(v___x_4290_, 2, v___x_4281_);
lean_ctor_set(v___x_4290_, 3, v___x_4282_);
lean_ctor_set(v___x_4290_, 4, v___x_4283_);
lean_ctor_set(v___x_4290_, 5, v___x_4284_);
lean_ctor_set(v___x_4290_, 6, v___x_4286_);
lean_ctor_set(v___x_4290_, 7, v___x_4287_);
lean_ctor_set(v___x_4290_, 8, v___x_4289_);
lean_ctor_set(v___x_4290_, 9, v___x_4285_);
v___x_4291_ = lean_io_get_num_heartbeats();
v___x_4292_ = lean_st_mk_ref(v___x_4290_);
v___x_4454_ = l_Lean_inheritedTraceOptions;
v___x_4455_ = lean_st_ref_get(v___x_4454_);
v___x_4456_ = lean_st_ref_get(v___x_4292_);
v_env_4479_ = lean_ctor_get(v___x_4456_, 0);
lean_inc_ref(v_env_4479_);
lean_dec(v___x_4456_);
v___x_4480_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4479_);
lean_dec_ref(v_env_4479_);
v___x_4481_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22);
if (v___x_4481_ == 0)
{
if (v___x_4480_ == 0)
{
v___y_4458_ = v___x_4288_;
goto v___jp_4457_;
}
else
{
v_fileName_4423_ = v___x_4268_;
v_fileMap_4424_ = v___x_4269_;
v_currNamespace_4425_ = v___x_4271_;
v_openDecls_4426_ = v___x_4272_;
v_initHeartbeats_4427_ = v___x_4291_;
v_maxHeartbeats_4428_ = v___x_4274_;
v_quotContext_4429_ = v___x_4271_;
v_currMacroScope_4430_ = v___x_4275_;
v_cancelTk_x3f_4431_ = v___x_4276_;
v_inheritedTraceOptions_4432_ = v___x_4455_;
v_currRecDepth_4433_ = v___x_4273_;
v_ref_4434_ = v___x_4277_;
v_suppressElabErrors_4435_ = v___x_4279_;
v_isRecordingDeps_4436_ = v___x_4279_;
goto v___jp_4422_;
}
}
else
{
if (v___x_4480_ == 0)
{
v_fileName_4423_ = v___x_4268_;
v_fileMap_4424_ = v___x_4269_;
v_currNamespace_4425_ = v___x_4271_;
v_openDecls_4426_ = v___x_4272_;
v_initHeartbeats_4427_ = v___x_4291_;
v_maxHeartbeats_4428_ = v___x_4274_;
v_quotContext_4429_ = v___x_4271_;
v_currMacroScope_4430_ = v___x_4275_;
v_cancelTk_x3f_4431_ = v___x_4276_;
v_inheritedTraceOptions_4432_ = v___x_4455_;
v_currRecDepth_4433_ = v___x_4273_;
v_ref_4434_ = v___x_4277_;
v_suppressElabErrors_4435_ = v___x_4279_;
v_isRecordingDeps_4436_ = v___x_4279_;
goto v___jp_4422_;
}
else
{
v___y_4458_ = v___x_4279_;
goto v___jp_4457_;
}
}
v___jp_4243_:
{
lean_object* v___x_4245_; lean_object* v___x_4246_; 
v___x_4245_ = lean_mk_io_user_error(v_a_4244_);
v___x_4246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4246_, 0, v___x_4245_);
return v___x_4246_;
}
v___jp_4247_:
{
lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; 
v___x_4249_ = l_Lean_MessageData_toString(v_msg_4248_);
v___x_4250_ = lean_mk_io_user_error(v___x_4249_);
v___x_4251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4251_, 0, v___x_4250_);
return v___x_4251_;
}
v___jp_4252_:
{
if (lean_obj_tag(v_a_4253_) == 0)
{
lean_object* v_msg_4254_; 
v_msg_4254_ = lean_ctor_get(v_a_4253_, 1);
lean_inc_ref(v_msg_4254_);
lean_dec_ref_known(v_a_4253_, 2);
v_msg_4248_ = v_msg_4254_;
goto v___jp_4247_;
}
else
{
lean_object* v_id_4255_; lean_object* v___x_4256_; 
v_id_4255_ = lean_ctor_get(v_a_4253_, 0);
lean_inc(v_id_4255_);
lean_dec_ref_known(v_a_4253_, 2);
v___x_4256_ = l_Lean_InternalExceptionId_getName(v_id_4255_);
if (lean_obj_tag(v___x_4256_) == 0)
{
lean_object* v_a_4257_; lean_object* v___x_4258_; uint8_t v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; 
lean_dec(v_id_4255_);
v_a_4257_ = lean_ctor_get(v___x_4256_, 0);
lean_inc(v_a_4257_);
lean_dec_ref_known(v___x_4256_, 1);
v___x_4258_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_4259_ = 1;
v___x_4260_ = l_Lean_Name_toString(v_a_4257_, v___x_4259_);
v___x_4261_ = lean_string_append(v___x_4258_, v___x_4260_);
lean_dec_ref(v___x_4260_);
v_a_4244_ = v___x_4261_;
goto v___jp_4243_;
}
else
{
lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; 
lean_dec_ref_known(v___x_4256_, 1);
v___x_4262_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_4263_ = l_Nat_reprFast(v_id_4255_);
v___x_4264_ = lean_string_append(v___x_4262_, v___x_4263_);
lean_dec_ref(v___x_4263_);
v___x_4265_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_4266_ = lean_string_append(v___x_4264_, v___x_4265_);
v_a_4244_ = v___x_4266_;
goto v___jp_4243_;
}
}
}
v___jp_4293_:
{
lean_object* v___x_4295_; lean_object* v___x_4296_; 
v___x_4295_ = lean_st_ref_get(v___x_4292_);
lean_dec(v___x_4292_);
lean_dec(v___x_4295_);
v___x_4296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4296_, 0, v_a_4294_);
return v___x_4296_;
}
v___jp_4297_:
{
lean_object* v_a_4299_; 
v_a_4299_ = lean_ctor_get(v___y_4298_, 0);
lean_inc(v_a_4299_);
lean_dec_ref(v___y_4298_);
v_a_4294_ = v_a_4299_;
goto v___jp_4293_;
}
v___jp_4300_:
{
switch(v___y_4301_)
{
case 0:
{
lean_dec(v_sp_4239_);
if (v___y_4308_ == 0)
{
lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; 
lean_dec_ref(v___y_4306_);
lean_dec_ref(v___y_4304_);
lean_dec_ref(v___y_4302_);
v___x_4309_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__0));
v___x_4310_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4241_, v___x_4288_);
v___x_4311_ = lean_string_append(v___x_4309_, v___x_4310_);
lean_dec_ref(v___x_4310_);
v___x_4312_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__1));
v___x_4313_ = lean_string_append(v___x_4311_, v___x_4312_);
v___x_4314_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_4313_);
if (lean_obj_tag(v___x_4314_) == 0)
{
lean_object* v_a_4315_; lean_object* v___x_4316_; 
v_a_4315_ = lean_ctor_get(v___x_4314_, 0);
lean_inc(v_a_4315_);
lean_dec_ref_known(v___x_4314_, 1);
v___x_4316_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_4308_, v_a_4315_, v___y_4307_, v___y_4305_);
lean_dec(v___y_4305_);
lean_dec_ref(v___y_4307_);
v___y_4298_ = v___x_4316_;
goto v___jp_4297_;
}
else
{
lean_object* v_a_4317_; lean_object* v___x_4319_; uint8_t v_isShared_4320_; uint8_t v_isSharedCheck_4326_; 
lean_dec_ref(v___y_4307_);
lean_dec(v___y_4305_);
lean_dec(v___x_4292_);
v_a_4317_ = lean_ctor_get(v___x_4314_, 0);
v_isSharedCheck_4326_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4326_ == 0)
{
v___x_4319_ = v___x_4314_;
v_isShared_4320_ = v_isSharedCheck_4326_;
goto v_resetjp_4318_;
}
else
{
lean_inc(v_a_4317_);
lean_dec(v___x_4314_);
v___x_4319_ = lean_box(0);
v_isShared_4320_ = v_isSharedCheck_4326_;
goto v_resetjp_4318_;
}
v_resetjp_4318_:
{
lean_object* v___x_4321_; lean_object* v___x_4323_; 
v___x_4321_ = lean_io_error_to_string(v_a_4317_);
if (v_isShared_4320_ == 0)
{
lean_ctor_set_tag(v___x_4319_, 3);
lean_ctor_set(v___x_4319_, 0, v___x_4321_);
v___x_4323_ = v___x_4319_;
goto v_reusejp_4322_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v___x_4321_);
v___x_4323_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4322_;
}
v_reusejp_4322_:
{
lean_object* v___x_4324_; 
v___x_4324_ = l_Lean_MessageData_ofFormat(v___x_4323_);
v_msg_4248_ = v___x_4324_;
goto v___jp_4247_;
}
}
}
}
else
{
lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; 
v___x_4327_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__2));
v___x_4328_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4241_, v___y_4308_);
v___x_4329_ = lean_string_append(v___x_4327_, v___x_4328_);
lean_dec_ref(v___x_4328_);
v___x_4330_ = lean_array_get_size(v___y_4306_);
lean_dec_ref(v___y_4306_);
v___x_4331_ = l_Lean_Linter_EnvLinter_formatLinterResults(v___y_4304_, v___y_4302_, v___x_4288_, v___x_4329_, v___x_4330_, v___x_4288_, v___y_4307_, v___y_4305_);
lean_dec_ref(v___y_4302_);
if (lean_obj_tag(v___x_4331_) == 0)
{
lean_object* v_a_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; 
v_a_4332_ = lean_ctor_get(v___x_4331_, 0);
lean_inc(v_a_4332_);
lean_dec_ref_known(v___x_4331_, 1);
v___x_4333_ = l_Lean_MessageData_toString(v_a_4332_);
v___x_4334_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_4333_);
if (lean_obj_tag(v___x_4334_) == 0)
{
lean_object* v_a_4335_; lean_object* v___x_4336_; 
v_a_4335_ = lean_ctor_get(v___x_4334_, 0);
lean_inc(v_a_4335_);
lean_dec_ref_known(v___x_4334_, 1);
v___x_4336_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_4308_, v_a_4335_, v___y_4307_, v___y_4305_);
lean_dec(v___y_4305_);
lean_dec_ref(v___y_4307_);
v___y_4298_ = v___x_4336_;
goto v___jp_4297_;
}
else
{
lean_object* v_a_4337_; lean_object* v___x_4339_; uint8_t v_isShared_4340_; uint8_t v_isSharedCheck_4346_; 
lean_dec_ref(v___y_4307_);
lean_dec(v___y_4305_);
lean_dec(v___x_4292_);
v_a_4337_ = lean_ctor_get(v___x_4334_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4334_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4339_ = v___x_4334_;
v_isShared_4340_ = v_isSharedCheck_4346_;
goto v_resetjp_4338_;
}
else
{
lean_inc(v_a_4337_);
lean_dec(v___x_4334_);
v___x_4339_ = lean_box(0);
v_isShared_4340_ = v_isSharedCheck_4346_;
goto v_resetjp_4338_;
}
v_resetjp_4338_:
{
lean_object* v___x_4341_; lean_object* v___x_4343_; 
v___x_4341_ = lean_io_error_to_string(v_a_4337_);
if (v_isShared_4340_ == 0)
{
lean_ctor_set_tag(v___x_4339_, 3);
lean_ctor_set(v___x_4339_, 0, v___x_4341_);
v___x_4343_ = v___x_4339_;
goto v_reusejp_4342_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v___x_4341_);
v___x_4343_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4342_;
}
v_reusejp_4342_:
{
lean_object* v___x_4344_; 
v___x_4344_ = l_Lean_MessageData_ofFormat(v___x_4343_);
v_msg_4248_ = v___x_4344_;
goto v___jp_4247_;
}
}
}
}
else
{
lean_object* v_a_4347_; 
lean_dec_ref(v___y_4307_);
lean_dec(v___y_4305_);
lean_dec(v___x_4292_);
v_a_4347_ = lean_ctor_get(v___x_4331_, 0);
lean_inc(v_a_4347_);
lean_dec_ref_known(v___x_4331_, 1);
v_a_4253_ = v_a_4347_;
goto v___jp_4252_;
}
}
}
case 1:
{
lean_object* v___x_4348_; lean_object* v_env_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; size_t v_sz_4353_; size_t v___x_4354_; lean_object* v___x_4355_; 
lean_dec_ref(v___y_4306_);
lean_dec_ref(v___y_4302_);
lean_dec(v_mod_4241_);
v___x_4348_ = lean_st_ref_get(v___y_4305_);
v_env_4349_ = lean_ctor_get(v___x_4348_, 0);
lean_inc_ref(v_env_4349_);
lean_dec(v___x_4348_);
v___x_4350_ = l_Lean_Environment_mainModule(v_env_4349_);
lean_dec_ref(v_env_4349_);
v___x_4351_ = lean_box(v___y_4303_);
v___x_4352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4352_, 0, v___x_4285_);
lean_ctor_set(v___x_4352_, 1, v___x_4351_);
v_sz_4353_ = lean_array_size(v___y_4304_);
v___x_4354_ = ((size_t)0ULL);
v___x_4355_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(v_sp_4239_, v___x_4350_, v___y_4304_, v_sz_4353_, v___x_4354_, v___x_4352_, v___y_4307_, v___y_4305_);
lean_dec(v___y_4305_);
lean_dec_ref(v___y_4307_);
lean_dec_ref(v___y_4304_);
if (lean_obj_tag(v___x_4355_) == 0)
{
lean_object* v_a_4356_; lean_object* v_fst_4357_; lean_object* v_snd_4358_; lean_object* v___x_4359_; uint8_t v___x_4360_; 
v_a_4356_ = lean_ctor_get(v___x_4355_, 0);
lean_inc(v_a_4356_);
lean_dec_ref_known(v___x_4355_, 1);
v_fst_4357_ = lean_ctor_get(v_a_4356_, 0);
lean_inc(v_fst_4357_);
v_snd_4358_ = lean_ctor_get(v_a_4356_, 1);
lean_inc(v_snd_4358_);
lean_dec(v_a_4356_);
v___x_4359_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_4359_, 0, v_fst_4357_);
v___x_4360_ = lean_unbox(v_snd_4358_);
lean_dec(v_snd_4358_);
lean_ctor_set_uint8(v___x_4359_, sizeof(void*)*1, v___x_4360_);
v_a_4294_ = v___x_4359_;
goto v___jp_4293_;
}
else
{
lean_object* v_a_4361_; 
lean_dec(v___x_4292_);
v_a_4361_ = lean_ctor_get(v___x_4355_, 0);
lean_inc(v_a_4361_);
lean_dec_ref_known(v___x_4355_, 1);
v_a_4253_ = v_a_4361_;
goto v___jp_4252_;
}
}
default: 
{
lean_object* v___x_4362_; lean_object* v_env_4363_; lean_object* v___x_4364_; size_t v_sz_4365_; size_t v___x_4366_; lean_object* v___x_4367_; 
lean_dec_ref(v___y_4306_);
lean_dec_ref(v___y_4302_);
lean_dec(v_mod_4241_);
lean_dec(v_sp_4239_);
v___x_4362_ = lean_st_ref_get(v___y_4305_);
v_env_4363_ = lean_ctor_get(v___x_4362_, 0);
lean_inc_ref(v_env_4363_);
lean_dec(v___x_4362_);
v___x_4364_ = l_Lean_Environment_mainModule(v_env_4363_);
lean_dec_ref(v_env_4363_);
v_sz_4365_ = lean_array_size(v___y_4304_);
v___x_4366_ = ((size_t)0ULL);
v___x_4367_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(v___x_4364_, v___y_4304_, v_sz_4365_, v___x_4366_, v___x_4285_, v___y_4307_, v___y_4305_);
lean_dec(v___y_4305_);
lean_dec_ref(v___y_4307_);
lean_dec_ref(v___y_4304_);
if (lean_obj_tag(v___x_4367_) == 0)
{
lean_object* v_a_4368_; lean_object* v___x_4370_; uint8_t v_isShared_4371_; uint8_t v_isSharedCheck_4375_; 
v_a_4368_ = lean_ctor_get(v___x_4367_, 0);
v_isSharedCheck_4375_ = !lean_is_exclusive(v___x_4367_);
if (v_isSharedCheck_4375_ == 0)
{
v___x_4370_ = v___x_4367_;
v_isShared_4371_ = v_isSharedCheck_4375_;
goto v_resetjp_4369_;
}
else
{
lean_inc(v_a_4368_);
lean_dec(v___x_4367_);
v___x_4370_ = lean_box(0);
v_isShared_4371_ = v_isSharedCheck_4375_;
goto v_resetjp_4369_;
}
v_resetjp_4369_:
{
lean_object* v___x_4373_; 
if (v_isShared_4371_ == 0)
{
lean_ctor_set_tag(v___x_4370_, 2);
v___x_4373_ = v___x_4370_;
goto v_reusejp_4372_;
}
else
{
lean_object* v_reuseFailAlloc_4374_; 
v_reuseFailAlloc_4374_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4374_, 0, v_a_4368_);
v___x_4373_ = v_reuseFailAlloc_4374_;
goto v_reusejp_4372_;
}
v_reusejp_4372_:
{
v_a_4294_ = v___x_4373_;
goto v___jp_4293_;
}
}
}
else
{
lean_object* v_a_4376_; 
lean_dec(v___x_4292_);
v_a_4376_ = lean_ctor_get(v___x_4367_, 0);
lean_inc(v_a_4376_);
lean_dec_ref_known(v___x_4367_, 1);
v_a_4253_ = v_a_4376_;
goto v___jp_4252_;
}
}
}
}
v___jp_4377_:
{
lean_object* v___x_4384_; 
lean_inc_ref(v___y_4382_);
v___x_4384_ = l_Lean_Linter_EnvLinter_lintCore(v___y_4379_, v___y_4382_, v___y_4381_, v___y_4380_);
if (lean_obj_tag(v___x_4384_) == 0)
{
lean_object* v_a_4385_; lean_object* v___x_4386_; uint8_t v___x_4387_; 
v_a_4385_ = lean_ctor_get(v___x_4384_, 0);
lean_inc(v_a_4385_);
lean_dec_ref_known(v___x_4384_, 1);
v___x_4386_ = lean_array_get_size(v_a_4385_);
v___x_4387_ = lean_nat_dec_lt(v___x_4273_, v___x_4386_);
if (v___x_4387_ == 0)
{
v___y_4301_ = v___y_4378_;
v___y_4302_ = v___y_4379_;
v___y_4303_ = v___y_4383_;
v___y_4304_ = v_a_4385_;
v___y_4305_ = v___y_4380_;
v___y_4306_ = v___y_4382_;
v___y_4307_ = v___y_4381_;
v___y_4308_ = v___x_4387_;
goto v___jp_4300_;
}
else
{
if (v___x_4387_ == 0)
{
v___y_4301_ = v___y_4378_;
v___y_4302_ = v___y_4379_;
v___y_4303_ = v___y_4383_;
v___y_4304_ = v_a_4385_;
v___y_4305_ = v___y_4380_;
v___y_4306_ = v___y_4382_;
v___y_4307_ = v___y_4381_;
v___y_4308_ = v___x_4387_;
goto v___jp_4300_;
}
else
{
size_t v___x_4388_; size_t v___x_4389_; uint8_t v___x_4390_; 
v___x_4388_ = ((size_t)0ULL);
v___x_4389_ = lean_usize_of_nat(v___x_4386_);
v___x_4390_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(v___y_4383_, v_a_4385_, v___x_4388_, v___x_4389_);
v___y_4301_ = v___y_4378_;
v___y_4302_ = v___y_4379_;
v___y_4303_ = v___y_4383_;
v___y_4304_ = v_a_4385_;
v___y_4305_ = v___y_4380_;
v___y_4306_ = v___y_4382_;
v___y_4307_ = v___y_4381_;
v___y_4308_ = v___x_4390_;
goto v___jp_4300_;
}
}
}
else
{
lean_object* v_a_4391_; 
lean_dec_ref(v___y_4382_);
lean_dec_ref(v___y_4381_);
lean_dec(v___y_4380_);
lean_dec_ref(v___y_4379_);
lean_dec(v___x_4292_);
lean_dec(v_mod_4241_);
lean_dec(v_sp_4239_);
v_a_4391_ = lean_ctor_get(v___x_4384_, 0);
lean_inc(v_a_4391_);
lean_dec_ref_known(v___x_4384_, 1);
v_a_4253_ = v_a_4391_;
goto v___jp_4252_;
}
}
v___jp_4392_:
{
lean_object* v___x_4398_; 
v___x_4398_ = l_Lean_Linter_EnvLinter_getEnvLinters(v___y_4397_, v___y_4396_, v___y_4395_);
lean_dec(v___y_4397_);
if (lean_obj_tag(v___x_4398_) == 0)
{
lean_object* v_a_4399_; lean_object* v___x_4400_; uint8_t v___x_4401_; 
v_a_4399_ = lean_ctor_get(v___x_4398_, 0);
lean_inc(v_a_4399_);
lean_dec_ref_known(v___x_4398_, 1);
v___x_4400_ = lean_array_get_size(v_a_4399_);
v___x_4401_ = lean_nat_dec_eq(v___x_4400_, v___x_4273_);
if (v___x_4401_ == 0)
{
v___y_4378_ = v___y_4393_;
v___y_4379_ = v___y_4394_;
v___y_4380_ = v___y_4395_;
v___y_4381_ = v___y_4396_;
v___y_4382_ = v_a_4399_;
v___y_4383_ = v___x_4401_;
goto v___jp_4377_;
}
else
{
uint8_t v___x_4402_; uint8_t v___x_4403_; 
v___x_4402_ = 0;
v___x_4403_ = l_Lake_BuiltinLint_instBEqMode_beq(v___y_4393_, v___x_4402_);
if (v___x_4403_ == 0)
{
v___y_4378_ = v___y_4393_;
v___y_4379_ = v___y_4394_;
v___y_4380_ = v___y_4395_;
v___y_4381_ = v___y_4396_;
v___y_4382_ = v_a_4399_;
v___y_4383_ = v___x_4403_;
goto v___jp_4377_;
}
else
{
lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; 
lean_dec(v_a_4399_);
lean_dec_ref(v___y_4396_);
lean_dec(v___y_4395_);
lean_dec_ref(v___y_4394_);
lean_dec(v_sp_4239_);
v___x_4404_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__3));
v___x_4405_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4241_, v___x_4403_);
v___x_4406_ = lean_string_append(v___x_4404_, v___x_4405_);
lean_dec_ref(v___x_4405_);
v___x_4407_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__1));
v___x_4408_ = lean_string_append(v___x_4406_, v___x_4407_);
v___x_4409_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_4408_);
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_object* v___x_4410_; 
lean_dec_ref_known(v___x_4409_, 1);
v___x_4410_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__4));
v_a_4294_ = v___x_4410_;
goto v___jp_4293_;
}
else
{
lean_object* v_a_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4420_; 
lean_dec(v___x_4292_);
v_a_4411_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4420_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4420_ == 0)
{
v___x_4413_ = v___x_4409_;
v_isShared_4414_ = v_isSharedCheck_4420_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_a_4411_);
lean_dec(v___x_4409_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4420_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4415_; lean_object* v___x_4417_; 
v___x_4415_ = lean_io_error_to_string(v_a_4411_);
if (v_isShared_4414_ == 0)
{
lean_ctor_set_tag(v___x_4413_, 3);
lean_ctor_set(v___x_4413_, 0, v___x_4415_);
v___x_4417_ = v___x_4413_;
goto v_reusejp_4416_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v___x_4415_);
v___x_4417_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4416_;
}
v_reusejp_4416_:
{
lean_object* v___x_4418_; 
v___x_4418_ = l_Lean_MessageData_ofFormat(v___x_4417_);
v_msg_4248_ = v___x_4418_;
goto v___jp_4247_;
}
}
}
}
}
}
else
{
lean_object* v_a_4421_; 
lean_dec_ref(v___y_4396_);
lean_dec(v___y_4395_);
lean_dec_ref(v___y_4394_);
lean_dec(v___x_4292_);
lean_dec(v_mod_4241_);
lean_dec(v_sp_4239_);
v_a_4421_ = lean_ctor_get(v___x_4398_, 0);
lean_inc(v_a_4421_);
lean_dec_ref_known(v___x_4398_, 1);
v_a_4253_ = v_a_4421_;
goto v___jp_4252_;
}
}
v___jp_4422_:
{
lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; 
v___x_4437_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5);
lean_inc(v_currMacroScope_4430_);
lean_inc(v_quotContext_4429_);
lean_inc(v_maxHeartbeats_4428_);
lean_inc(v_openDecls_4426_);
lean_inc(v_currNamespace_4425_);
lean_inc_ref(v_fileMap_4424_);
lean_inc_ref(v_fileName_4423_);
v___x_4438_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4438_, 0, v_fileName_4423_);
lean_ctor_set(v___x_4438_, 1, v_fileMap_4424_);
lean_ctor_set(v___x_4438_, 2, v___x_4270_);
lean_ctor_set(v___x_4438_, 3, v___x_4437_);
lean_ctor_set(v___x_4438_, 4, v_currNamespace_4425_);
lean_ctor_set(v___x_4438_, 5, v_openDecls_4426_);
lean_ctor_set(v___x_4438_, 6, v_initHeartbeats_4427_);
lean_ctor_set(v___x_4438_, 7, v_maxHeartbeats_4428_);
lean_ctor_set(v___x_4438_, 8, v_quotContext_4429_);
lean_ctor_set(v___x_4438_, 9, v_currMacroScope_4430_);
lean_ctor_set(v___x_4438_, 10, v_cancelTk_x3f_4431_);
lean_ctor_set(v___x_4438_, 11, v_inheritedTraceOptions_4432_);
lean_inc(v_ref_4434_);
v___x_4439_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_4439_, 0, v___x_4438_);
lean_ctor_set(v___x_4439_, 1, v_currRecDepth_4433_);
lean_ctor_set(v___x_4439_, 2, v_ref_4434_);
lean_ctor_set_uint16(v___x_4439_, sizeof(void*)*3, v___x_4278_);
lean_ctor_set_uint8(v___x_4439_, sizeof(void*)*3 + 2, v_suppressElabErrors_4435_);
lean_ctor_set_uint8(v___x_4439_, sizeof(void*)*3 + 3, v_isRecordingDeps_4436_);
v___x_4440_ = l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(v___x_4267_, v___x_4292_);
lean_dec(v___x_4267_);
if (lean_obj_tag(v___x_4440_) == 0)
{
uint8_t v_lintOnly_4441_; 
v_lintOnly_4441_ = lean_ctor_get_uint8(v_args_4237_, sizeof(void*)*4);
if (v_lintOnly_4441_ == 0)
{
lean_object* v_a_4442_; uint8_t v_mode_4443_; 
lean_dec_ref(v_linterOpts_4238_);
v_a_4442_ = lean_ctor_get(v___x_4440_, 0);
lean_inc(v_a_4442_);
lean_dec_ref_known(v___x_4440_, 1);
v_mode_4443_ = lean_ctor_get_uint8(v_args_4237_, sizeof(void*)*4 + 1);
lean_inc(v___x_4292_);
v___y_4393_ = v_mode_4443_;
v___y_4394_ = v_a_4442_;
v___y_4395_ = v___x_4292_;
v___y_4396_ = v___x_4439_;
v___y_4397_ = v___x_4276_;
goto v___jp_4392_;
}
else
{
lean_object* v_a_4444_; lean_object* v___x_4446_; uint8_t v_isShared_4447_; uint8_t v_isSharedCheck_4452_; 
v_a_4444_ = lean_ctor_get(v___x_4440_, 0);
v_isSharedCheck_4452_ = !lean_is_exclusive(v___x_4440_);
if (v_isSharedCheck_4452_ == 0)
{
v___x_4446_ = v___x_4440_;
v_isShared_4447_ = v_isSharedCheck_4452_;
goto v_resetjp_4445_;
}
else
{
lean_inc(v_a_4444_);
lean_dec(v___x_4440_);
v___x_4446_ = lean_box(0);
v_isShared_4447_ = v_isSharedCheck_4452_;
goto v_resetjp_4445_;
}
v_resetjp_4445_:
{
uint8_t v_mode_4448_; lean_object* v___x_4450_; 
v_mode_4448_ = lean_ctor_get_uint8(v_args_4237_, sizeof(void*)*4 + 1);
if (v_isShared_4447_ == 0)
{
lean_ctor_set_tag(v___x_4446_, 1);
lean_ctor_set(v___x_4446_, 0, v_linterOpts_4238_);
v___x_4450_ = v___x_4446_;
goto v_reusejp_4449_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v_linterOpts_4238_);
v___x_4450_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4449_;
}
v_reusejp_4449_:
{
lean_inc(v___x_4292_);
v___y_4393_ = v_mode_4448_;
v___y_4394_ = v_a_4444_;
v___y_4395_ = v___x_4292_;
v___y_4396_ = v___x_4439_;
v___y_4397_ = v___x_4450_;
goto v___jp_4392_;
}
}
}
}
else
{
lean_object* v_a_4453_; 
lean_dec_ref_known(v___x_4439_, 3);
lean_dec(v___x_4292_);
lean_dec(v_mod_4241_);
lean_dec(v_sp_4239_);
lean_dec_ref(v_linterOpts_4238_);
v_a_4453_ = lean_ctor_get(v___x_4440_, 0);
lean_inc(v_a_4453_);
lean_dec_ref_known(v___x_4440_, 1);
v_a_4253_ = v_a_4453_;
goto v___jp_4252_;
}
}
v___jp_4457_:
{
lean_object* v___x_4459_; lean_object* v_env_4460_; lean_object* v_nextMacroScope_4461_; lean_object* v_ngen_4462_; lean_object* v_auxDeclNGen_4463_; lean_object* v_traceState_4464_; lean_object* v_recordedDeps_4465_; lean_object* v_messages_4466_; lean_object* v_infoState_4467_; lean_object* v_snapshotTasks_4468_; lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4477_; 
v___x_4459_ = lean_st_ref_take(v___x_4292_);
v_env_4460_ = lean_ctor_get(v___x_4459_, 0);
v_nextMacroScope_4461_ = lean_ctor_get(v___x_4459_, 1);
v_ngen_4462_ = lean_ctor_get(v___x_4459_, 2);
v_auxDeclNGen_4463_ = lean_ctor_get(v___x_4459_, 3);
v_traceState_4464_ = lean_ctor_get(v___x_4459_, 4);
v_recordedDeps_4465_ = lean_ctor_get(v___x_4459_, 6);
v_messages_4466_ = lean_ctor_get(v___x_4459_, 7);
v_infoState_4467_ = lean_ctor_get(v___x_4459_, 8);
v_snapshotTasks_4468_ = lean_ctor_get(v___x_4459_, 9);
v_isSharedCheck_4477_ = !lean_is_exclusive(v___x_4459_);
if (v_isSharedCheck_4477_ == 0)
{
lean_object* v_unused_4478_; 
v_unused_4478_ = lean_ctor_get(v___x_4459_, 5);
lean_dec(v_unused_4478_);
v___x_4470_ = v___x_4459_;
v_isShared_4471_ = v_isSharedCheck_4477_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_snapshotTasks_4468_);
lean_inc(v_infoState_4467_);
lean_inc(v_messages_4466_);
lean_inc(v_recordedDeps_4465_);
lean_inc(v_traceState_4464_);
lean_inc(v_auxDeclNGen_4463_);
lean_inc(v_ngen_4462_);
lean_inc(v_nextMacroScope_4461_);
lean_inc(v_env_4460_);
lean_dec(v___x_4459_);
v___x_4470_ = lean_box(0);
v_isShared_4471_ = v_isSharedCheck_4477_;
goto v_resetjp_4469_;
}
v_resetjp_4469_:
{
lean_object* v___x_4472_; lean_object* v___x_4474_; 
v___x_4472_ = l_Lean_Kernel_enableDiag(v_env_4460_, v___y_4458_);
if (v_isShared_4471_ == 0)
{
lean_ctor_set(v___x_4470_, 5, v___x_4284_);
lean_ctor_set(v___x_4470_, 0, v___x_4472_);
v___x_4474_ = v___x_4470_;
goto v_reusejp_4473_;
}
else
{
lean_object* v_reuseFailAlloc_4476_; 
v_reuseFailAlloc_4476_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4476_, 0, v___x_4472_);
lean_ctor_set(v_reuseFailAlloc_4476_, 1, v_nextMacroScope_4461_);
lean_ctor_set(v_reuseFailAlloc_4476_, 2, v_ngen_4462_);
lean_ctor_set(v_reuseFailAlloc_4476_, 3, v_auxDeclNGen_4463_);
lean_ctor_set(v_reuseFailAlloc_4476_, 4, v_traceState_4464_);
lean_ctor_set(v_reuseFailAlloc_4476_, 5, v___x_4284_);
lean_ctor_set(v_reuseFailAlloc_4476_, 6, v_recordedDeps_4465_);
lean_ctor_set(v_reuseFailAlloc_4476_, 7, v_messages_4466_);
lean_ctor_set(v_reuseFailAlloc_4476_, 8, v_infoState_4467_);
lean_ctor_set(v_reuseFailAlloc_4476_, 9, v_snapshotTasks_4468_);
v___x_4474_ = v_reuseFailAlloc_4476_;
goto v_reusejp_4473_;
}
v_reusejp_4473_:
{
lean_object* v___x_4475_; 
v___x_4475_ = lean_st_ref_put(v___x_4292_, v___x_4474_);
v_fileName_4423_ = v___x_4268_;
v_fileMap_4424_ = v___x_4269_;
v_currNamespace_4425_ = v___x_4271_;
v_openDecls_4426_ = v___x_4272_;
v_initHeartbeats_4427_ = v___x_4291_;
v_maxHeartbeats_4428_ = v___x_4274_;
v_quotContext_4429_ = v___x_4271_;
v_currMacroScope_4430_ = v___x_4275_;
v_cancelTk_x3f_4431_ = v___x_4276_;
v_inheritedTraceOptions_4432_ = v___x_4455_;
v_currRecDepth_4433_ = v___x_4273_;
v_ref_4434_ = v___x_4277_;
v_suppressElabErrors_4435_ = v___x_4279_;
v_isRecordingDeps_4436_ = v___x_4279_;
goto v___jp_4422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___boxed(lean_object* v_args_4482_, lean_object* v_linterOpts_4483_, lean_object* v_sp_4484_, lean_object* v_env_4485_, lean_object* v_mod_4486_, lean_object* v_a_4487_){
_start:
{
lean_object* v_res_4488_; 
v_res_4488_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(v_args_4482_, v_linterOpts_4483_, v_sp_4484_, v_env_4485_, v_mod_4486_);
lean_dec_ref(v_args_4482_);
return v_res_4488_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5(lean_object* v_00_u03b4_4489_, lean_object* v_t_4490_, lean_object* v_k_4491_, lean_object* v_fallback_4492_){
_start:
{
lean_object* v___x_4493_; 
v___x_4493_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_t_4490_, v_k_4491_, v_fallback_4492_);
return v___x_4493_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___boxed(lean_object* v_00_u03b4_4494_, lean_object* v_t_4495_, lean_object* v_k_4496_, lean_object* v_fallback_4497_){
_start:
{
lean_object* v_res_4498_; 
v_res_4498_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5(v_00_u03b4_4494_, v_t_4495_, v_k_4496_, v_fallback_4497_);
lean_dec(v_fallback_4497_);
lean_dec_ref(v_k_4496_);
lean_dec(v_t_4495_);
return v_res_4498_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6(lean_object* v_00_u03b2_4499_, lean_object* v_k_4500_, lean_object* v_v_4501_, lean_object* v_t_4502_, lean_object* v_hl_4503_){
_start:
{
lean_object* v___x_4504_; 
v___x_4504_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_4500_, v_v_4501_, v_t_4502_);
return v___x_4504_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8(lean_object* v_fst_4505_, lean_object* v_init_4506_, lean_object* v_x_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_){
_start:
{
lean_object* v___x_4511_; 
v___x_4511_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4505_, v_init_4506_, v_x_4507_);
return v___x_4511_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___boxed(lean_object* v_fst_4512_, lean_object* v_init_4513_, lean_object* v_x_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_){
_start:
{
lean_object* v_res_4518_; 
v_res_4518_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8(v_fst_4512_, v_init_4513_, v_x_4514_, v___y_4515_, v___y_4516_);
lean_dec(v___y_4516_);
lean_dec_ref(v___y_4515_);
return v_res_4518_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4519_, lean_object* v_constName_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_){
_start:
{
lean_object* v___x_4524_; 
v___x_4524_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_4520_, v___y_4521_, v___y_4522_);
return v___x_4524_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_4525_, lean_object* v_constName_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_){
_start:
{
lean_object* v_res_4530_; 
v_res_4530_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1(v_00_u03b1_4525_, v_constName_4526_, v___y_4527_, v___y_4528_);
lean_dec(v___y_4528_);
lean_dec_ref(v___y_4527_);
return v_res_4530_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12(lean_object* v_00_u03b1_4531_, lean_object* v_ref_4532_, lean_object* v_constName_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_){
_start:
{
lean_object* v___x_4537_; 
v___x_4537_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_4532_, v_constName_4533_, v___y_4534_, v___y_4535_);
return v___x_4537_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___boxed(lean_object* v_00_u03b1_4538_, lean_object* v_ref_4539_, lean_object* v_constName_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12(v_00_u03b1_4538_, v_ref_4539_, v_constName_4540_, v___y_4541_, v___y_4542_);
lean_dec(v___y_4542_);
lean_dec_ref(v___y_4541_);
lean_dec(v_ref_4539_);
return v_res_4544_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13(lean_object* v_00_u03b1_4545_, lean_object* v_ref_4546_, lean_object* v_msg_4547_, lean_object* v_declHint_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_){
_start:
{
lean_object* v___x_4552_; 
v___x_4552_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_4546_, v_msg_4547_, v_declHint_4548_, v___y_4549_, v___y_4550_);
return v___x_4552_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___boxed(lean_object* v_00_u03b1_4553_, lean_object* v_ref_4554_, lean_object* v_msg_4555_, lean_object* v_declHint_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_){
_start:
{
lean_object* v_res_4560_; 
v_res_4560_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13(v_00_u03b1_4553_, v_ref_4554_, v_msg_4555_, v_declHint_4556_, v___y_4557_, v___y_4558_);
lean_dec(v___y_4558_);
lean_dec_ref(v___y_4557_);
lean_dec(v_ref_4554_);
return v_res_4560_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15(lean_object* v_msg_4561_, lean_object* v_declHint_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_){
_start:
{
lean_object* v___x_4566_; 
v___x_4566_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_4561_, v_declHint_4562_, v___y_4564_);
return v___x_4566_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___boxed(lean_object* v_msg_4567_, lean_object* v_declHint_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_){
_start:
{
lean_object* v_res_4572_; 
v_res_4572_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15(v_msg_4567_, v_declHint_4568_, v___y_4569_, v___y_4570_);
lean_dec(v___y_4570_);
lean_dec_ref(v___y_4569_);
return v_res_4572_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15(lean_object* v_00_u03b1_4573_, lean_object* v_ref_4574_, lean_object* v_msg_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_){
_start:
{
lean_object* v___x_4579_; 
v___x_4579_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_4574_, v_msg_4575_, v___y_4576_, v___y_4577_);
return v___x_4579_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___boxed(lean_object* v_00_u03b1_4580_, lean_object* v_ref_4581_, lean_object* v_msg_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_){
_start:
{
lean_object* v_res_4586_; 
v_res_4586_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15(v_00_u03b1_4580_, v_ref_4581_, v_msg_4582_, v___y_4583_, v___y_4584_);
lean_dec(v___y_4584_);
lean_dec_ref(v___y_4583_);
lean_dec(v_ref_4581_);
return v_res_4586_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17(lean_object* v_00_u03b1_4587_, lean_object* v_msg_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_){
_start:
{
lean_object* v___x_4592_; 
v___x_4592_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_4588_, v___y_4589_, v___y_4590_);
return v___x_4592_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___boxed(lean_object* v_00_u03b1_4593_, lean_object* v_msg_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_){
_start:
{
lean_object* v_res_4598_; 
v_res_4598_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17(v_00_u03b1_4593_, v_msg_4594_, v___y_4595_, v___y_4596_);
lean_dec(v___y_4596_);
lean_dec_ref(v___y_4595_);
return v_res_4598_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(lean_object* v_s_4599_){
_start:
{
lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; uint32_t v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; 
v___x_4601_ = l_Std_Format_defWidth;
v___x_4602_ = lean_unsigned_to_nat(0u);
v___x_4603_ = l_Std_Format_pretty(v_s_4599_, v___x_4601_, v___x_4602_, v___x_4602_);
v___x_4604_ = 10;
v___x_4605_ = lean_string_push(v___x_4603_, v___x_4604_);
v___x_4606_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(v___x_4605_);
return v___x_4606_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0___boxed(lean_object* v_s_4607_, lean_object* v_a_4608_){
_start:
{
lean_object* v_res_4609_; 
v_res_4609_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(v_s_4607_);
return v_res_4609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(lean_object* v_as_4610_, size_t v_sz_4611_, size_t v_i_4612_, lean_object* v_b_4613_, lean_object* v___y_4614_){
_start:
{
uint8_t v___x_4616_; 
v___x_4616_ = lean_usize_dec_lt(v_i_4612_, v_sz_4611_);
if (v___x_4616_ == 0)
{
lean_object* v___x_4617_; 
v___x_4617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4617_, 0, v_b_4613_);
return v___x_4617_;
}
else
{
lean_object* v___x_4618_; lean_object* v_a_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v_ref_4622_; lean_object* v___x_4623_; 
v___x_4618_ = lean_box(0);
v_a_4619_ = lean_array_uget_borrowed(v_as_4610_, v_i_4612_);
v___x_4620_ = lean_box(0);
lean_inc(v_a_4619_);
v___x_4621_ = l_Lean_MessageData_format(v_a_4619_, v___x_4620_);
v_ref_4622_ = lean_ctor_get(v___y_4614_, 2);
v___x_4623_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(v___x_4621_);
if (lean_obj_tag(v___x_4623_) == 0)
{
size_t v___x_4624_; size_t v___x_4625_; 
lean_dec_ref_known(v___x_4623_, 1);
v___x_4624_ = ((size_t)1ULL);
v___x_4625_ = lean_usize_add(v_i_4612_, v___x_4624_);
v_i_4612_ = v___x_4625_;
v_b_4613_ = v___x_4618_;
goto _start;
}
else
{
lean_object* v_a_4627_; lean_object* v___x_4629_; uint8_t v_isShared_4630_; uint8_t v_isSharedCheck_4638_; 
v_a_4627_ = lean_ctor_get(v___x_4623_, 0);
v_isSharedCheck_4638_ = !lean_is_exclusive(v___x_4623_);
if (v_isSharedCheck_4638_ == 0)
{
v___x_4629_ = v___x_4623_;
v_isShared_4630_ = v_isSharedCheck_4638_;
goto v_resetjp_4628_;
}
else
{
lean_inc(v_a_4627_);
lean_dec(v___x_4623_);
v___x_4629_ = lean_box(0);
v_isShared_4630_ = v_isSharedCheck_4638_;
goto v_resetjp_4628_;
}
v_resetjp_4628_:
{
lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4636_; 
v___x_4631_ = lean_io_error_to_string(v_a_4627_);
v___x_4632_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4632_, 0, v___x_4631_);
v___x_4633_ = l_Lean_MessageData_ofFormat(v___x_4632_);
lean_inc(v_ref_4622_);
v___x_4634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4634_, 0, v_ref_4622_);
lean_ctor_set(v___x_4634_, 1, v___x_4633_);
if (v_isShared_4630_ == 0)
{
lean_ctor_set(v___x_4629_, 0, v___x_4634_);
v___x_4636_ = v___x_4629_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4637_; 
v_reuseFailAlloc_4637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4637_, 0, v___x_4634_);
v___x_4636_ = v_reuseFailAlloc_4637_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
return v___x_4636_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg___boxed(lean_object* v_as_4639_, lean_object* v_sz_4640_, lean_object* v_i_4641_, lean_object* v_b_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_){
_start:
{
size_t v_sz_boxed_4645_; size_t v_i_boxed_4646_; lean_object* v_res_4647_; 
v_sz_boxed_4645_ = lean_unbox_usize(v_sz_4640_);
lean_dec(v_sz_4640_);
v_i_boxed_4646_ = lean_unbox_usize(v_i_4641_);
lean_dec(v_i_4641_);
v_res_4647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(v_as_4639_, v_sz_boxed_4645_, v_i_boxed_4646_, v_b_4642_, v___y_4643_);
lean_dec_ref(v___y_4643_);
lean_dec_ref(v_as_4639_);
return v_res_4647_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(lean_object* v_errors_4648_, lean_object* v_entries_4649_, lean_object* v_____r_4650_, uint8_t v_anyFailed_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_){
_start:
{
lean_object* v___x_4655_; size_t v_sz_4656_; size_t v___x_4657_; lean_object* v___x_4658_; 
v___x_4655_ = lean_box(0);
v_sz_4656_ = lean_array_size(v_errors_4648_);
v___x_4657_ = ((size_t)0ULL);
v___x_4658_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(v_errors_4648_, v_sz_4656_, v___x_4657_, v___x_4655_, v___y_4652_);
if (lean_obj_tag(v___x_4658_) == 0)
{
lean_object* v___x_4660_; uint8_t v_isShared_4661_; uint8_t v_isSharedCheck_4667_; 
v_isSharedCheck_4667_ = !lean_is_exclusive(v___x_4658_);
if (v_isSharedCheck_4667_ == 0)
{
lean_object* v_unused_4668_; 
v_unused_4668_ = lean_ctor_get(v___x_4658_, 0);
lean_dec(v_unused_4668_);
v___x_4660_ = v___x_4658_;
v_isShared_4661_ = v_isSharedCheck_4667_;
goto v_resetjp_4659_;
}
else
{
lean_dec(v___x_4658_);
v___x_4660_ = lean_box(0);
v_isShared_4661_ = v_isSharedCheck_4667_;
goto v_resetjp_4659_;
}
v_resetjp_4659_:
{
lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4665_; 
v___x_4662_ = lean_box(v_anyFailed_4651_);
v___x_4663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4663_, 0, v_entries_4649_);
lean_ctor_set(v___x_4663_, 1, v___x_4662_);
if (v_isShared_4661_ == 0)
{
lean_ctor_set(v___x_4660_, 0, v___x_4663_);
v___x_4665_ = v___x_4660_;
goto v_reusejp_4664_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v___x_4663_);
v___x_4665_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4664_;
}
v_reusejp_4664_:
{
return v___x_4665_;
}
}
}
else
{
lean_object* v_a_4669_; lean_object* v___x_4671_; uint8_t v_isShared_4672_; uint8_t v_isSharedCheck_4676_; 
lean_dec_ref(v_entries_4649_);
v_a_4669_ = lean_ctor_get(v___x_4658_, 0);
v_isSharedCheck_4676_ = !lean_is_exclusive(v___x_4658_);
if (v_isSharedCheck_4676_ == 0)
{
v___x_4671_ = v___x_4658_;
v_isShared_4672_ = v_isSharedCheck_4676_;
goto v_resetjp_4670_;
}
else
{
lean_inc(v_a_4669_);
lean_dec(v___x_4658_);
v___x_4671_ = lean_box(0);
v_isShared_4672_ = v_isSharedCheck_4676_;
goto v_resetjp_4670_;
}
v_resetjp_4670_:
{
lean_object* v___x_4674_; 
if (v_isShared_4672_ == 0)
{
v___x_4674_ = v___x_4671_;
goto v_reusejp_4673_;
}
else
{
lean_object* v_reuseFailAlloc_4675_; 
v_reuseFailAlloc_4675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4675_, 0, v_a_4669_);
v___x_4674_ = v_reuseFailAlloc_4675_;
goto v_reusejp_4673_;
}
v_reusejp_4673_:
{
return v___x_4674_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0___boxed(lean_object* v_errors_4677_, lean_object* v_entries_4678_, lean_object* v_____r_4679_, lean_object* v_anyFailed_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_){
_start:
{
uint8_t v_anyFailed_boxed_4684_; lean_object* v_res_4685_; 
v_anyFailed_boxed_4684_ = lean_unbox(v_anyFailed_4680_);
v_res_4685_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(v_errors_4677_, v_entries_4678_, v_____r_4679_, v_anyFailed_boxed_4684_, v___y_4681_, v___y_4682_);
lean_dec(v___y_4682_);
lean_dec_ref(v___y_4681_);
lean_dec_ref(v_errors_4677_);
return v_res_4685_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(lean_object* v_sp_4686_, lean_object* v_env_4687_, lean_object* v_mod_4688_){
_start:
{
lean_object* v_a_4691_; lean_object* v_a_4695_; uint8_t v_anyFailed_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; uint16_t v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; uint8_t v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___y_4740_; lean_object* v_fileName_4756_; lean_object* v_fileMap_4757_; lean_object* v_currNamespace_4758_; lean_object* v_openDecls_4759_; lean_object* v_initHeartbeats_4760_; lean_object* v_maxHeartbeats_4761_; lean_object* v_quotContext_4762_; lean_object* v_currMacroScope_4763_; lean_object* v_cancelTk_x3f_4764_; lean_object* v_inheritedTraceOptions_4765_; lean_object* v_currRecDepth_4766_; lean_object* v_ref_4767_; uint8_t v_suppressElabErrors_4768_; uint8_t v_isRecordingDeps_4769_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; uint8_t v___y_4792_; lean_object* v_env_4813_; uint8_t v___x_4814_; uint8_t v___x_4815_; 
v_anyFailed_4712_ = 0;
v___x_4713_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_4714_ = l_Lean_instInhabitedFileMap_default;
v___x_4715_ = l_Lean_Options_empty;
v___x_4716_ = lean_box(0);
v___x_4717_ = lean_box(0);
v___x_4718_ = lean_unsigned_to_nat(0u);
v___x_4719_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5);
v___x_4720_ = l_Lean_firstFrontendMacroScope;
v___x_4721_ = lean_box(0);
v___x_4722_ = lean_box(0);
v___x_4723_ = lean_uint16_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_4724_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7);
v___x_4725_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10));
v___x_4726_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11));
v___x_4727_ = lean_unsigned_to_nat(32u);
v___x_4728_ = lean_mk_empty_array_with_capacity(v___x_4727_);
lean_dec_ref(v___x_4728_);
v___x_4729_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14);
v___x_4730_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_4731_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___closed__0));
v___x_4732_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18);
v___x_4733_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_4734_ = 1;
v___x_4735_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
v___x_4736_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4736_, 0, v_env_4687_);
lean_ctor_set(v___x_4736_, 1, v___x_4724_);
lean_ctor_set(v___x_4736_, 2, v___x_4725_);
lean_ctor_set(v___x_4736_, 3, v___x_4726_);
lean_ctor_set(v___x_4736_, 4, v___x_4729_);
lean_ctor_set(v___x_4736_, 5, v___x_4730_);
lean_ctor_set(v___x_4736_, 6, v___x_4732_);
lean_ctor_set(v___x_4736_, 7, v___x_4733_);
lean_ctor_set(v___x_4736_, 8, v___x_4735_);
lean_ctor_set(v___x_4736_, 9, v___x_4731_);
v___x_4737_ = lean_io_get_num_heartbeats();
v___x_4738_ = lean_st_mk_ref(v___x_4736_);
v___x_4788_ = l_Lean_inheritedTraceOptions;
v___x_4789_ = lean_st_ref_get(v___x_4788_);
v___x_4790_ = lean_st_ref_get(v___x_4738_);
v_env_4813_ = lean_ctor_get(v___x_4790_, 0);
lean_inc_ref(v_env_4813_);
lean_dec(v___x_4790_);
v___x_4814_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4813_);
lean_dec_ref(v_env_4813_);
v___x_4815_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22);
if (v___x_4815_ == 0)
{
if (v___x_4814_ == 0)
{
v___y_4792_ = v___x_4734_;
goto v___jp_4791_;
}
else
{
v_fileName_4756_ = v___x_4713_;
v_fileMap_4757_ = v___x_4714_;
v_currNamespace_4758_ = v___x_4716_;
v_openDecls_4759_ = v___x_4717_;
v_initHeartbeats_4760_ = v___x_4737_;
v_maxHeartbeats_4761_ = v___x_4719_;
v_quotContext_4762_ = v___x_4716_;
v_currMacroScope_4763_ = v___x_4720_;
v_cancelTk_x3f_4764_ = v___x_4721_;
v_inheritedTraceOptions_4765_ = v___x_4789_;
v_currRecDepth_4766_ = v___x_4718_;
v_ref_4767_ = v___x_4722_;
v_suppressElabErrors_4768_ = v_anyFailed_4712_;
v_isRecordingDeps_4769_ = v_anyFailed_4712_;
goto v___jp_4755_;
}
}
else
{
if (v___x_4814_ == 0)
{
v_fileName_4756_ = v___x_4713_;
v_fileMap_4757_ = v___x_4714_;
v_currNamespace_4758_ = v___x_4716_;
v_openDecls_4759_ = v___x_4717_;
v_initHeartbeats_4760_ = v___x_4737_;
v_maxHeartbeats_4761_ = v___x_4719_;
v_quotContext_4762_ = v___x_4716_;
v_currMacroScope_4763_ = v___x_4720_;
v_cancelTk_x3f_4764_ = v___x_4721_;
v_inheritedTraceOptions_4765_ = v___x_4789_;
v_currRecDepth_4766_ = v___x_4718_;
v_ref_4767_ = v___x_4722_;
v_suppressElabErrors_4768_ = v_anyFailed_4712_;
v_isRecordingDeps_4769_ = v_anyFailed_4712_;
goto v___jp_4755_;
}
else
{
v___y_4792_ = v_anyFailed_4712_;
goto v___jp_4791_;
}
}
v___jp_4690_:
{
lean_object* v___x_4692_; lean_object* v___x_4693_; 
v___x_4692_ = lean_mk_io_user_error(v_a_4691_);
v___x_4693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4693_, 0, v___x_4692_);
return v___x_4693_;
}
v___jp_4694_:
{
if (lean_obj_tag(v_a_4695_) == 0)
{
lean_object* v_msg_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; 
v_msg_4696_ = lean_ctor_get(v_a_4695_, 1);
lean_inc_ref(v_msg_4696_);
lean_dec_ref_known(v_a_4695_, 2);
v___x_4697_ = l_Lean_MessageData_toString(v_msg_4696_);
v___x_4698_ = lean_mk_io_user_error(v___x_4697_);
v___x_4699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4699_, 0, v___x_4698_);
return v___x_4699_;
}
else
{
lean_object* v_id_4700_; lean_object* v___x_4701_; 
v_id_4700_ = lean_ctor_get(v_a_4695_, 0);
lean_inc(v_id_4700_);
lean_dec_ref_known(v_a_4695_, 2);
v___x_4701_ = l_Lean_InternalExceptionId_getName(v_id_4700_);
if (lean_obj_tag(v___x_4701_) == 0)
{
lean_object* v_a_4702_; lean_object* v___x_4703_; uint8_t v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; 
lean_dec(v_id_4700_);
v_a_4702_ = lean_ctor_get(v___x_4701_, 0);
lean_inc(v_a_4702_);
lean_dec_ref_known(v___x_4701_, 1);
v___x_4703_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_4704_ = 1;
v___x_4705_ = l_Lean_Name_toString(v_a_4702_, v___x_4704_);
v___x_4706_ = lean_string_append(v___x_4703_, v___x_4705_);
lean_dec_ref(v___x_4705_);
v_a_4691_ = v___x_4706_;
goto v___jp_4690_;
}
else
{
lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; 
lean_dec_ref_known(v___x_4701_, 1);
v___x_4707_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_4708_ = l_Nat_reprFast(v_id_4700_);
v___x_4709_ = lean_string_append(v___x_4707_, v___x_4708_);
lean_dec_ref(v___x_4708_);
v___x_4710_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_4711_ = lean_string_append(v___x_4709_, v___x_4710_);
v_a_4691_ = v___x_4711_;
goto v___jp_4690_;
}
}
}
v___jp_4739_:
{
if (lean_obj_tag(v___y_4740_) == 0)
{
lean_object* v_a_4741_; lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4753_; 
v_a_4741_ = lean_ctor_get(v___y_4740_, 0);
v_isSharedCheck_4753_ = !lean_is_exclusive(v___y_4740_);
if (v_isSharedCheck_4753_ == 0)
{
v___x_4743_ = v___y_4740_;
v_isShared_4744_ = v_isSharedCheck_4753_;
goto v_resetjp_4742_;
}
else
{
lean_inc(v_a_4741_);
lean_dec(v___y_4740_);
v___x_4743_ = lean_box(0);
v_isShared_4744_ = v_isSharedCheck_4753_;
goto v_resetjp_4742_;
}
v_resetjp_4742_:
{
lean_object* v___x_4745_; lean_object* v_fst_4746_; lean_object* v_snd_4747_; lean_object* v___x_4748_; uint8_t v___x_4749_; lean_object* v___x_4751_; 
v___x_4745_ = lean_st_ref_get(v___x_4738_);
lean_dec(v___x_4738_);
lean_dec(v___x_4745_);
v_fst_4746_ = lean_ctor_get(v_a_4741_, 0);
lean_inc(v_fst_4746_);
v_snd_4747_ = lean_ctor_get(v_a_4741_, 1);
lean_inc(v_snd_4747_);
lean_dec(v_a_4741_);
v___x_4748_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4748_, 0, v_fst_4746_);
v___x_4749_ = lean_unbox(v_snd_4747_);
lean_dec(v_snd_4747_);
lean_ctor_set_uint8(v___x_4748_, sizeof(void*)*1, v___x_4749_);
if (v_isShared_4744_ == 0)
{
lean_ctor_set(v___x_4743_, 0, v___x_4748_);
v___x_4751_ = v___x_4743_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4752_, 0, v___x_4748_);
v___x_4751_ = v_reuseFailAlloc_4752_;
goto v_reusejp_4750_;
}
v_reusejp_4750_:
{
return v___x_4751_;
}
}
}
else
{
lean_object* v_a_4754_; 
lean_dec(v___x_4738_);
v_a_4754_ = lean_ctor_get(v___y_4740_, 0);
lean_inc(v_a_4754_);
lean_dec_ref_known(v___y_4740_, 1);
v_a_4695_ = v_a_4754_;
goto v___jp_4694_;
}
}
v___jp_4755_:
{
lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; 
v___x_4770_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5);
lean_inc(v_cancelTk_x3f_4764_);
lean_inc(v_currMacroScope_4763_);
lean_inc(v_quotContext_4762_);
lean_inc(v_maxHeartbeats_4761_);
lean_inc(v_openDecls_4759_);
lean_inc(v_currNamespace_4758_);
lean_inc_ref(v_fileMap_4757_);
lean_inc_ref(v_fileName_4756_);
v___x_4771_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4771_, 0, v_fileName_4756_);
lean_ctor_set(v___x_4771_, 1, v_fileMap_4757_);
lean_ctor_set(v___x_4771_, 2, v___x_4715_);
lean_ctor_set(v___x_4771_, 3, v___x_4770_);
lean_ctor_set(v___x_4771_, 4, v_currNamespace_4758_);
lean_ctor_set(v___x_4771_, 5, v_openDecls_4759_);
lean_ctor_set(v___x_4771_, 6, v_initHeartbeats_4760_);
lean_ctor_set(v___x_4771_, 7, v_maxHeartbeats_4761_);
lean_ctor_set(v___x_4771_, 8, v_quotContext_4762_);
lean_ctor_set(v___x_4771_, 9, v_currMacroScope_4763_);
lean_ctor_set(v___x_4771_, 10, v_cancelTk_x3f_4764_);
lean_ctor_set(v___x_4771_, 11, v_inheritedTraceOptions_4765_);
lean_inc(v_ref_4767_);
v___x_4772_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_4772_, 0, v___x_4771_);
lean_ctor_set(v___x_4772_, 1, v_currRecDepth_4766_);
lean_ctor_set(v___x_4772_, 2, v_ref_4767_);
lean_ctor_set_uint16(v___x_4772_, sizeof(void*)*3, v___x_4723_);
lean_ctor_set_uint8(v___x_4772_, sizeof(void*)*3 + 2, v_suppressElabErrors_4768_);
lean_ctor_set_uint8(v___x_4772_, sizeof(void*)*3 + 3, v_isRecordingDeps_4769_);
v___x_4773_ = l_Lean_Linter_CodeQuality_getPackageChecks(v___x_4772_, v___x_4738_);
if (lean_obj_tag(v___x_4773_) == 0)
{
lean_object* v_a_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; 
v_a_4774_ = lean_ctor_get(v___x_4773_, 0);
lean_inc(v_a_4774_);
lean_dec_ref_known(v___x_4773_, 1);
v___x_4775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4775_, 0, v_sp_4686_);
lean_ctor_set(v___x_4775_, 1, v_mod_4688_);
v___x_4776_ = l_Lean_Linter_CodeQuality_runPackageChecks(v_a_4774_, v___x_4775_, v___x_4772_, v___x_4738_);
if (lean_obj_tag(v___x_4776_) == 0)
{
lean_object* v_a_4777_; lean_object* v_entries_4778_; lean_object* v_errors_4779_; lean_object* v___x_4780_; uint8_t v___x_4781_; 
v_a_4777_ = lean_ctor_get(v___x_4776_, 0);
lean_inc(v_a_4777_);
lean_dec_ref_known(v___x_4776_, 1);
v_entries_4778_ = lean_ctor_get(v_a_4777_, 0);
lean_inc_ref(v_entries_4778_);
v_errors_4779_ = lean_ctor_get(v_a_4777_, 1);
lean_inc_ref(v_errors_4779_);
lean_dec(v_a_4777_);
v___x_4780_ = lean_array_get_size(v_errors_4779_);
v___x_4781_ = lean_nat_dec_eq(v___x_4780_, v___x_4718_);
if (v___x_4781_ == 0)
{
lean_object* v___x_4782_; lean_object* v___x_4783_; 
v___x_4782_ = lean_box(0);
v___x_4783_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(v_errors_4779_, v_entries_4778_, v___x_4782_, v___x_4734_, v___x_4772_, v___x_4738_);
lean_dec_ref_known(v___x_4772_, 3);
lean_dec_ref(v_errors_4779_);
v___y_4740_ = v___x_4783_;
goto v___jp_4739_;
}
else
{
lean_object* v___x_4784_; lean_object* v___x_4785_; 
v___x_4784_ = lean_box(0);
v___x_4785_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(v_errors_4779_, v_entries_4778_, v___x_4784_, v_anyFailed_4712_, v___x_4772_, v___x_4738_);
lean_dec_ref_known(v___x_4772_, 3);
lean_dec_ref(v_errors_4779_);
v___y_4740_ = v___x_4785_;
goto v___jp_4739_;
}
}
else
{
lean_object* v_a_4786_; 
lean_dec_ref_known(v___x_4772_, 3);
lean_dec(v___x_4738_);
v_a_4786_ = lean_ctor_get(v___x_4776_, 0);
lean_inc(v_a_4786_);
lean_dec_ref_known(v___x_4776_, 1);
v_a_4695_ = v_a_4786_;
goto v___jp_4694_;
}
}
else
{
lean_object* v_a_4787_; 
lean_dec_ref_known(v___x_4772_, 3);
lean_dec(v___x_4738_);
lean_dec(v_mod_4688_);
lean_dec(v_sp_4686_);
v_a_4787_ = lean_ctor_get(v___x_4773_, 0);
lean_inc(v_a_4787_);
lean_dec_ref_known(v___x_4773_, 1);
v_a_4695_ = v_a_4787_;
goto v___jp_4694_;
}
}
v___jp_4791_:
{
lean_object* v___x_4793_; lean_object* v_env_4794_; lean_object* v_nextMacroScope_4795_; lean_object* v_ngen_4796_; lean_object* v_auxDeclNGen_4797_; lean_object* v_traceState_4798_; lean_object* v_recordedDeps_4799_; lean_object* v_messages_4800_; lean_object* v_infoState_4801_; lean_object* v_snapshotTasks_4802_; lean_object* v___x_4804_; uint8_t v_isShared_4805_; uint8_t v_isSharedCheck_4811_; 
v___x_4793_ = lean_st_ref_take(v___x_4738_);
v_env_4794_ = lean_ctor_get(v___x_4793_, 0);
v_nextMacroScope_4795_ = lean_ctor_get(v___x_4793_, 1);
v_ngen_4796_ = lean_ctor_get(v___x_4793_, 2);
v_auxDeclNGen_4797_ = lean_ctor_get(v___x_4793_, 3);
v_traceState_4798_ = lean_ctor_get(v___x_4793_, 4);
v_recordedDeps_4799_ = lean_ctor_get(v___x_4793_, 6);
v_messages_4800_ = lean_ctor_get(v___x_4793_, 7);
v_infoState_4801_ = lean_ctor_get(v___x_4793_, 8);
v_snapshotTasks_4802_ = lean_ctor_get(v___x_4793_, 9);
v_isSharedCheck_4811_ = !lean_is_exclusive(v___x_4793_);
if (v_isSharedCheck_4811_ == 0)
{
lean_object* v_unused_4812_; 
v_unused_4812_ = lean_ctor_get(v___x_4793_, 5);
lean_dec(v_unused_4812_);
v___x_4804_ = v___x_4793_;
v_isShared_4805_ = v_isSharedCheck_4811_;
goto v_resetjp_4803_;
}
else
{
lean_inc(v_snapshotTasks_4802_);
lean_inc(v_infoState_4801_);
lean_inc(v_messages_4800_);
lean_inc(v_recordedDeps_4799_);
lean_inc(v_traceState_4798_);
lean_inc(v_auxDeclNGen_4797_);
lean_inc(v_ngen_4796_);
lean_inc(v_nextMacroScope_4795_);
lean_inc(v_env_4794_);
lean_dec(v___x_4793_);
v___x_4804_ = lean_box(0);
v_isShared_4805_ = v_isSharedCheck_4811_;
goto v_resetjp_4803_;
}
v_resetjp_4803_:
{
lean_object* v___x_4806_; lean_object* v___x_4808_; 
v___x_4806_ = l_Lean_Kernel_enableDiag(v_env_4794_, v___y_4792_);
if (v_isShared_4805_ == 0)
{
lean_ctor_set(v___x_4804_, 5, v___x_4730_);
lean_ctor_set(v___x_4804_, 0, v___x_4806_);
v___x_4808_ = v___x_4804_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4810_; 
v_reuseFailAlloc_4810_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4810_, 0, v___x_4806_);
lean_ctor_set(v_reuseFailAlloc_4810_, 1, v_nextMacroScope_4795_);
lean_ctor_set(v_reuseFailAlloc_4810_, 2, v_ngen_4796_);
lean_ctor_set(v_reuseFailAlloc_4810_, 3, v_auxDeclNGen_4797_);
lean_ctor_set(v_reuseFailAlloc_4810_, 4, v_traceState_4798_);
lean_ctor_set(v_reuseFailAlloc_4810_, 5, v___x_4730_);
lean_ctor_set(v_reuseFailAlloc_4810_, 6, v_recordedDeps_4799_);
lean_ctor_set(v_reuseFailAlloc_4810_, 7, v_messages_4800_);
lean_ctor_set(v_reuseFailAlloc_4810_, 8, v_infoState_4801_);
lean_ctor_set(v_reuseFailAlloc_4810_, 9, v_snapshotTasks_4802_);
v___x_4808_ = v_reuseFailAlloc_4810_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
lean_object* v___x_4809_; 
v___x_4809_ = lean_st_ref_put(v___x_4738_, v___x_4808_);
v_fileName_4756_ = v___x_4713_;
v_fileMap_4757_ = v___x_4714_;
v_currNamespace_4758_ = v___x_4716_;
v_openDecls_4759_ = v___x_4717_;
v_initHeartbeats_4760_ = v___x_4737_;
v_maxHeartbeats_4761_ = v___x_4719_;
v_quotContext_4762_ = v___x_4716_;
v_currMacroScope_4763_ = v___x_4720_;
v_cancelTk_x3f_4764_ = v___x_4721_;
v_inheritedTraceOptions_4765_ = v___x_4789_;
v_currRecDepth_4766_ = v___x_4718_;
v_ref_4767_ = v___x_4722_;
v_suppressElabErrors_4768_ = v_anyFailed_4712_;
v_isRecordingDeps_4769_ = v_anyFailed_4712_;
goto v___jp_4755_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___boxed(lean_object* v_sp_4816_, lean_object* v_env_4817_, lean_object* v_mod_4818_, lean_object* v_a_4819_){
_start:
{
lean_object* v_res_4820_; 
v_res_4820_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(v_sp_4816_, v_env_4817_, v_mod_4818_);
return v_res_4820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1(lean_object* v_as_4821_, size_t v_sz_4822_, size_t v_i_4823_, lean_object* v_b_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_){
_start:
{
lean_object* v___x_4828_; 
v___x_4828_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(v_as_4821_, v_sz_4822_, v_i_4823_, v_b_4824_, v___y_4825_);
return v___x_4828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___boxed(lean_object* v_as_4829_, lean_object* v_sz_4830_, lean_object* v_i_4831_, lean_object* v_b_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_){
_start:
{
size_t v_sz_boxed_4836_; size_t v_i_boxed_4837_; lean_object* v_res_4838_; 
v_sz_boxed_4836_ = lean_unbox_usize(v_sz_4830_);
lean_dec(v_sz_4830_);
v_i_boxed_4837_ = lean_unbox_usize(v_i_4831_);
lean_dec(v_i_4831_);
v_res_4838_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1(v_as_4829_, v_sz_boxed_4836_, v_i_boxed_4837_, v_b_4832_, v___y_4833_, v___y_4834_);
lean_dec(v___y_4834_);
lean_dec_ref(v___y_4833_);
lean_dec_ref(v_as_4829_);
return v_res_4838_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1(){
_start:
{
lean_object* v___x_4840_; 
v___x_4840_ = lean_enable_initializer_execution();
return v___x_4840_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1___boxed(lean_object* v_a_4841_){
_start:
{
lean_object* v_res_4842_; 
v_res_4842_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1();
return v_res_4842_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(lean_object* v_region_4843_){
_start:
{
lean_object* v___x_4845_; 
v___x_4845_ = lean_compacted_region_free(v_region_4843_);
return v___x_4845_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4___boxed(lean_object* v_region_4846_, lean_object* v_a_4847_){
_start:
{
lean_object* v_res_4848_; 
v_res_4848_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(v_region_4846_);
return v_res_4848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(lean_object* v_o_4852_, lean_object* v_k_4853_, uint8_t v_v_4854_){
_start:
{
lean_object* v_map_4855_; uint8_t v_hasTrace_4856_; lean_object* v___x_4858_; uint8_t v_isShared_4859_; uint8_t v_isSharedCheck_4870_; 
v_map_4855_ = lean_ctor_get(v_o_4852_, 0);
v_hasTrace_4856_ = lean_ctor_get_uint8(v_o_4852_, sizeof(void*)*1);
v_isSharedCheck_4870_ = !lean_is_exclusive(v_o_4852_);
if (v_isSharedCheck_4870_ == 0)
{
v___x_4858_ = v_o_4852_;
v_isShared_4859_ = v_isSharedCheck_4870_;
goto v_resetjp_4857_;
}
else
{
lean_inc(v_map_4855_);
lean_dec(v_o_4852_);
v___x_4858_ = lean_box(0);
v_isShared_4859_ = v_isSharedCheck_4870_;
goto v_resetjp_4857_;
}
v_resetjp_4857_:
{
lean_object* v___x_4860_; lean_object* v___x_4861_; 
v___x_4860_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4860_, 0, v_v_4854_);
lean_inc(v_k_4853_);
v___x_4861_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4853_, v___x_4860_, v_map_4855_);
if (v_hasTrace_4856_ == 0)
{
lean_object* v___x_4862_; uint8_t v___x_4863_; lean_object* v___x_4865_; 
v___x_4862_ = ((lean_object*)(l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___closed__1));
v___x_4863_ = l_Lean_Name_isPrefixOf(v___x_4862_, v_k_4853_);
lean_dec(v_k_4853_);
if (v_isShared_4859_ == 0)
{
lean_ctor_set(v___x_4858_, 0, v___x_4861_);
v___x_4865_ = v___x_4858_;
goto v_reusejp_4864_;
}
else
{
lean_object* v_reuseFailAlloc_4866_; 
v_reuseFailAlloc_4866_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4866_, 0, v___x_4861_);
v___x_4865_ = v_reuseFailAlloc_4866_;
goto v_reusejp_4864_;
}
v_reusejp_4864_:
{
lean_ctor_set_uint8(v___x_4865_, sizeof(void*)*1, v___x_4863_);
return v___x_4865_;
}
}
else
{
lean_object* v___x_4868_; 
lean_dec(v_k_4853_);
if (v_isShared_4859_ == 0)
{
lean_ctor_set(v___x_4858_, 0, v___x_4861_);
v___x_4868_ = v___x_4858_;
goto v_reusejp_4867_;
}
else
{
lean_object* v_reuseFailAlloc_4869_; 
v_reuseFailAlloc_4869_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4869_, 0, v___x_4861_);
lean_ctor_set_uint8(v_reuseFailAlloc_4869_, sizeof(void*)*1, v_hasTrace_4856_);
v___x_4868_ = v_reuseFailAlloc_4869_;
goto v_reusejp_4867_;
}
v_reusejp_4867_:
{
return v___x_4868_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___boxed(lean_object* v_o_4871_, lean_object* v_k_4872_, lean_object* v_v_4873_){
_start:
{
uint8_t v_v_boxed_4874_; lean_object* v_res_4875_; 
v_v_boxed_4874_ = lean_unbox(v_v_4873_);
v_res_4875_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_o_4871_, v_k_4872_, v_v_boxed_4874_);
return v_res_4875_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__4(lean_object* v_s_4876_){
_start:
{
lean_object* v___x_4878_; lean_object* v___x_4879_; uint32_t v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; 
v___x_4878_ = lean_unsigned_to_nat(80u);
v___x_4879_ = l_Lean_Json_pretty(v_s_4876_, v___x_4878_);
v___x_4880_ = 10;
v___x_4881_ = lean_string_push(v___x_4879_, v___x_4880_);
v___x_4882_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_4881_);
return v___x_4882_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__4___boxed(lean_object* v_s_4883_, lean_object* v_a_4884_){
_start:
{
lean_object* v_res_4885_; 
v_res_4885_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__4(v_s_4883_);
return v_res_4885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(lean_object* v_as_4886_, size_t v_sz_4887_, size_t v_i_4888_, lean_object* v_b_4889_){
_start:
{
uint8_t v___x_4891_; 
v___x_4891_ = lean_usize_dec_lt(v_i_4888_, v_sz_4887_);
if (v___x_4891_ == 0)
{
lean_object* v___x_4892_; 
v___x_4892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4892_, 0, v_b_4889_);
return v___x_4892_;
}
else
{
lean_object* v___x_4893_; lean_object* v_a_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; 
v___x_4893_ = lean_box(0);
v_a_4894_ = lean_array_uget_borrowed(v_as_4886_, v_i_4888_);
lean_inc(v_a_4894_);
v___x_4895_ = l_Lean_Linter_CodeQuality_instToJsonEntry_toJson(v_a_4894_);
v___x_4896_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__4(v___x_4895_);
if (lean_obj_tag(v___x_4896_) == 0)
{
size_t v___x_4897_; size_t v___x_4898_; 
lean_dec_ref_known(v___x_4896_, 1);
v___x_4897_ = ((size_t)1ULL);
v___x_4898_ = lean_usize_add(v_i_4888_, v___x_4897_);
v_i_4888_ = v___x_4898_;
v_b_4889_ = v___x_4893_;
goto _start;
}
else
{
return v___x_4896_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___boxed(lean_object* v_as_4900_, lean_object* v_sz_4901_, lean_object* v_i_4902_, lean_object* v_b_4903_, lean_object* v___y_4904_){
_start:
{
size_t v_sz_boxed_4905_; size_t v_i_boxed_4906_; lean_object* v_res_4907_; 
v_sz_boxed_4905_ = lean_unbox_usize(v_sz_4901_);
lean_dec(v_sz_4901_);
v_i_boxed_4906_ = lean_unbox_usize(v_i_4902_);
lean_dec(v_i_4902_);
v_res_4907_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(v_as_4900_, v_sz_boxed_4905_, v_i_boxed_4906_, v_b_4903_);
lean_dec_ref(v_as_4900_);
return v_res_4907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(lean_object* v___x_4908_, size_t v_sz_4909_, size_t v_i_4910_, lean_object* v_bs_4911_){
_start:
{
uint8_t v_anyUnlocated_4912_; 
v_anyUnlocated_4912_ = lean_usize_dec_lt(v_i_4910_, v_sz_4909_);
if (v_anyUnlocated_4912_ == 0)
{
return v_bs_4911_;
}
else
{
lean_object* v___x_4913_; uint8_t v_anyFailed_4914_; lean_object* v_v_4915_; lean_object* v_bs_x27_4916_; lean_object* v___x_4917_; size_t v___x_4918_; size_t v___x_4919_; lean_object* v___x_4920_; 
v___x_4913_ = lean_unsigned_to_nat(0u);
v_anyFailed_4914_ = lean_nat_dec_eq(v___x_4908_, v___x_4913_);
v_v_4915_ = lean_array_uget(v_bs_4911_, v_i_4910_);
v_bs_x27_4916_ = lean_array_uset(v_bs_4911_, v_i_4910_, v___x_4913_);
v___x_4917_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_4917_, 0, v_v_4915_);
lean_ctor_set_uint8(v___x_4917_, sizeof(void*)*1, v_anyFailed_4914_);
lean_ctor_set_uint8(v___x_4917_, sizeof(void*)*1 + 1, v_anyUnlocated_4912_);
lean_ctor_set_uint8(v___x_4917_, sizeof(void*)*1 + 2, v_anyFailed_4914_);
v___x_4918_ = ((size_t)1ULL);
v___x_4919_ = lean_usize_add(v_i_4910_, v___x_4918_);
v___x_4920_ = lean_array_uset(v_bs_x27_4916_, v_i_4910_, v___x_4917_);
v_i_4910_ = v___x_4919_;
v_bs_4911_ = v___x_4920_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1___boxed(lean_object* v___x_4922_, lean_object* v_sz_4923_, lean_object* v_i_4924_, lean_object* v_bs_4925_){
_start:
{
size_t v_sz_boxed_4926_; size_t v_i_boxed_4927_; lean_object* v_res_4928_; 
v_sz_boxed_4926_ = lean_unbox_usize(v_sz_4923_);
lean_dec(v_sz_4923_);
v_i_boxed_4927_ = lean_unbox_usize(v_i_4924_);
lean_dec(v_i_4924_);
v_res_4928_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(v___x_4922_, v_sz_boxed_4926_, v_i_boxed_4927_, v_bs_4925_);
lean_dec(v___x_4922_);
return v_res_4928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(lean_object* v_as_4929_, size_t v_i_4930_, size_t v_stop_4931_, lean_object* v_b_4932_){
_start:
{
uint8_t v___x_4933_; 
v___x_4933_ = lean_usize_dec_eq(v_i_4930_, v_stop_4931_);
if (v___x_4933_ == 0)
{
lean_object* v___x_4934_; lean_object* v_fst_4935_; lean_object* v_snd_4936_; uint8_t v___x_4937_; lean_object* v___x_4938_; size_t v___x_4939_; size_t v___x_4940_; 
v___x_4934_ = lean_array_uget_borrowed(v_as_4929_, v_i_4930_);
v_fst_4935_ = lean_ctor_get(v___x_4934_, 0);
v_snd_4936_ = lean_ctor_get(v___x_4934_, 1);
v___x_4937_ = lean_unbox(v_snd_4936_);
lean_inc(v_fst_4935_);
v___x_4938_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_b_4932_, v_fst_4935_, v___x_4937_);
v___x_4939_ = ((size_t)1ULL);
v___x_4940_ = lean_usize_add(v_i_4930_, v___x_4939_);
v_i_4930_ = v___x_4940_;
v_b_4932_ = v___x_4938_;
goto _start;
}
else
{
return v_b_4932_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2___boxed(lean_object* v_as_4942_, lean_object* v_i_4943_, lean_object* v_stop_4944_, lean_object* v_b_4945_){
_start:
{
size_t v_i_boxed_4946_; size_t v_stop_boxed_4947_; lean_object* v_res_4948_; 
v_i_boxed_4946_ = lean_unbox_usize(v_i_4943_);
lean_dec(v_i_4943_);
v_stop_boxed_4947_ = lean_unbox_usize(v_stop_4944_);
lean_dec(v_stop_4944_);
v_res_4948_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(v_as_4942_, v_i_boxed_4946_, v_stop_boxed_4947_, v_b_4945_);
lean_dec_ref(v_as_4942_);
return v_res_4948_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(lean_object* v___x_4958_, lean_object* v_checkImports_4959_, lean_object* v_args_4960_, lean_object* v___x_4961_, lean_object* v_as_4962_, size_t v_sz_4963_, size_t v_i_4964_, lean_object* v_b_4965_){
_start:
{
lean_object* v_a_4968_; lean_object* v___x_4972_; uint8_t v_anyFailed_4973_; uint8_t v_anyUnlocated_4974_; lean_object* v___x_4975_; lean_object* v_envLinterModule_4976_; uint8_t v___x_4977_; 
v___x_4972_ = lean_unsigned_to_nat(0u);
v_anyFailed_4973_ = lean_nat_dec_eq(v___x_4958_, v___x_4972_);
v_anyUnlocated_4974_ = 1;
v___x_4975_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__3));
v_envLinterModule_4976_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_envLinterModule_4976_, 0, v___x_4975_);
lean_ctor_set_uint8(v_envLinterModule_4976_, sizeof(void*)*1, v_anyFailed_4973_);
lean_ctor_set_uint8(v_envLinterModule_4976_, sizeof(void*)*1 + 1, v_anyUnlocated_4974_);
lean_ctor_set_uint8(v_envLinterModule_4976_, sizeof(void*)*1 + 2, v_anyFailed_4973_);
v___x_4977_ = lean_usize_dec_lt(v_i_4964_, v_sz_4963_);
if (v___x_4977_ == 0)
{
lean_object* v___x_4978_; 
lean_dec_ref_known(v_envLinterModule_4976_, 1);
lean_dec(v___x_4961_);
v___x_4978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4978_, 0, v_b_4965_);
return v___x_4978_;
}
else
{
lean_object* v_snd_4979_; lean_object* v_snd_4980_; lean_object* v_snd_4981_; lean_object* v_snd_4982_; lean_object* v_fst_4983_; lean_object* v___x_4985_; uint8_t v_isShared_4986_; uint8_t v_isSharedCheck_5296_; 
v_snd_4979_ = lean_ctor_get(v_b_4965_, 1);
lean_inc(v_snd_4979_);
v_snd_4980_ = lean_ctor_get(v_snd_4979_, 1);
lean_inc(v_snd_4980_);
v_snd_4981_ = lean_ctor_get(v_snd_4980_, 1);
lean_inc(v_snd_4981_);
v_snd_4982_ = lean_ctor_get(v_snd_4981_, 1);
lean_inc(v_snd_4982_);
v_fst_4983_ = lean_ctor_get(v_b_4965_, 0);
v_isSharedCheck_5296_ = !lean_is_exclusive(v_b_4965_);
if (v_isSharedCheck_5296_ == 0)
{
lean_object* v_unused_5297_; 
v_unused_5297_ = lean_ctor_get(v_b_4965_, 1);
lean_dec(v_unused_5297_);
v___x_4985_ = v_b_4965_;
v_isShared_4986_ = v_isSharedCheck_5296_;
goto v_resetjp_4984_;
}
else
{
lean_inc(v_fst_4983_);
lean_dec(v_b_4965_);
v___x_4985_ = lean_box(0);
v_isShared_4986_ = v_isSharedCheck_5296_;
goto v_resetjp_4984_;
}
v_resetjp_4984_:
{
lean_object* v_fst_4987_; lean_object* v___x_4989_; uint8_t v_isShared_4990_; uint8_t v_isSharedCheck_5294_; 
v_fst_4987_ = lean_ctor_get(v_snd_4979_, 0);
v_isSharedCheck_5294_ = !lean_is_exclusive(v_snd_4979_);
if (v_isSharedCheck_5294_ == 0)
{
lean_object* v_unused_5295_; 
v_unused_5295_ = lean_ctor_get(v_snd_4979_, 1);
lean_dec(v_unused_5295_);
v___x_4989_ = v_snd_4979_;
v_isShared_4990_ = v_isSharedCheck_5294_;
goto v_resetjp_4988_;
}
else
{
lean_inc(v_fst_4987_);
lean_dec(v_snd_4979_);
v___x_4989_ = lean_box(0);
v_isShared_4990_ = v_isSharedCheck_5294_;
goto v_resetjp_4988_;
}
v_resetjp_4988_:
{
lean_object* v_fst_4991_; lean_object* v___x_4993_; uint8_t v_isShared_4994_; uint8_t v_isSharedCheck_5292_; 
v_fst_4991_ = lean_ctor_get(v_snd_4980_, 0);
v_isSharedCheck_5292_ = !lean_is_exclusive(v_snd_4980_);
if (v_isSharedCheck_5292_ == 0)
{
lean_object* v_unused_5293_; 
v_unused_5293_ = lean_ctor_get(v_snd_4980_, 1);
lean_dec(v_unused_5293_);
v___x_4993_ = v_snd_4980_;
v_isShared_4994_ = v_isSharedCheck_5292_;
goto v_resetjp_4992_;
}
else
{
lean_inc(v_fst_4991_);
lean_dec(v_snd_4980_);
v___x_4993_ = lean_box(0);
v_isShared_4994_ = v_isSharedCheck_5292_;
goto v_resetjp_4992_;
}
v_resetjp_4992_:
{
lean_object* v_fst_4995_; lean_object* v___x_4997_; uint8_t v_isShared_4998_; uint8_t v_isSharedCheck_5290_; 
v_fst_4995_ = lean_ctor_get(v_snd_4981_, 0);
v_isSharedCheck_5290_ = !lean_is_exclusive(v_snd_4981_);
if (v_isSharedCheck_5290_ == 0)
{
lean_object* v_unused_5291_; 
v_unused_5291_ = lean_ctor_get(v_snd_4981_, 1);
lean_dec(v_unused_5291_);
v___x_4997_ = v_snd_4981_;
v_isShared_4998_ = v_isSharedCheck_5290_;
goto v_resetjp_4996_;
}
else
{
lean_inc(v_fst_4995_);
lean_dec(v_snd_4981_);
v___x_4997_ = lean_box(0);
v_isShared_4998_ = v_isSharedCheck_5290_;
goto v_resetjp_4996_;
}
v_resetjp_4996_:
{
lean_object* v_fst_4999_; lean_object* v_snd_5000_; lean_object* v___x_5002_; uint8_t v_isShared_5003_; uint8_t v_isSharedCheck_5289_; 
v_fst_4999_ = lean_ctor_get(v_snd_4982_, 0);
v_snd_5000_ = lean_ctor_get(v_snd_4982_, 1);
v_isSharedCheck_5289_ = !lean_is_exclusive(v_snd_4982_);
if (v_isSharedCheck_5289_ == 0)
{
v___x_5002_ = v_snd_4982_;
v_isShared_5003_ = v_isSharedCheck_5289_;
goto v_resetjp_5001_;
}
else
{
lean_inc(v_snd_5000_);
lean_inc(v_fst_4999_);
lean_dec(v_snd_4982_);
v___x_5002_ = lean_box(0);
v_isShared_5003_ = v_isSharedCheck_5289_;
goto v_resetjp_5001_;
}
v_resetjp_5001_:
{
lean_object* v___x_5004_; lean_object* v_a_5005_; lean_object* v___y_5007_; lean_object* v___y_5008_; uint8_t v_anyFailed_5009_; uint8_t v_anyUnlocated_5010_; lean_object* v_records_5011_; lean_object* v_codeQualityEntries_5012_; lean_object* v___y_5159_; lean_object* v___y_5160_; uint8_t v_anyFailed_5161_; uint8_t v_anyUnlocated_5162_; lean_object* v_records_5163_; lean_object* v_codeQualityEntries_5164_; lean_object* v___y_5182_; lean_object* v___y_5183_; lean_object* v___x_5222_; lean_object* v___x_5223_; 
v___x_5004_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v_a_5005_ = lean_array_uget_borrowed(v_as_4962_, v_i_4964_);
v___x_5222_ = lean_enable_initializer_execution();
lean_inc(v_a_5005_);
v___x_5223_ = l_Lean_findOLean(v_a_5005_);
if (lean_obj_tag(v___x_5223_) == 0)
{
lean_object* v_a_5224_; lean_object* v___x_5225_; 
v_a_5224_ = lean_ctor_get(v___x_5223_, 0);
lean_inc(v_a_5224_);
lean_dec_ref_known(v___x_5223_, 1);
v___x_5225_ = l_Lean_readModuleData(v_a_5224_);
lean_dec(v_a_5224_);
if (lean_obj_tag(v___x_5225_) == 0)
{
lean_object* v_a_5226_; lean_object* v_fst_5227_; lean_object* v_snd_5228_; uint8_t v___x_5229_; uint8_t v___y_5231_; 
v_a_5226_ = lean_ctor_get(v___x_5225_, 0);
lean_inc(v_a_5226_);
lean_dec_ref_known(v___x_5225_, 1);
v_fst_5227_ = lean_ctor_get(v_a_5226_, 0);
lean_inc(v_fst_5227_);
v_snd_5228_ = lean_ctor_get(v_a_5226_, 1);
lean_inc(v_snd_5228_);
lean_dec(v_a_5226_);
v___x_5229_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(v_fst_5227_);
lean_dec(v_fst_5227_);
if (v___x_5229_ == 0)
{
uint8_t v___x_5271_; 
v___x_5271_ = 2;
v___y_5231_ = v___x_5271_;
goto v___jp_5230_;
}
else
{
uint8_t v___x_5272_; 
v___x_5272_ = 1;
v___y_5231_ = v___x_5272_;
goto v___jp_5230_;
}
v___jp_5230_:
{
lean_object* v___x_5232_; 
v___x_5232_ = lean_compacted_region_free(v_snd_5228_);
if (lean_obj_tag(v___x_5232_) == 0)
{
lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; uint32_t v___x_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; lean_object* v___x_5243_; 
lean_dec_ref_known(v___x_5232_, 1);
lean_inc(v_a_5005_);
v___x_5233_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_5233_, 0, v_a_5005_);
lean_ctor_set_uint8(v___x_5233_, sizeof(void*)*1, v_anyFailed_4973_);
lean_ctor_set_uint8(v___x_5233_, sizeof(void*)*1 + 1, v_anyUnlocated_4974_);
lean_ctor_set_uint8(v___x_5233_, sizeof(void*)*1 + 2, v_anyFailed_4973_);
v___x_5234_ = lean_unsigned_to_nat(2u);
v___x_5235_ = lean_mk_empty_array_with_capacity(v___x_5234_);
v___x_5236_ = lean_array_push(v___x_5235_, v___x_5233_);
v___x_5237_ = lean_array_push(v___x_5236_, v_envLinterModule_4976_);
v___x_5238_ = l_Array_append___redArg(v___x_5237_, v_checkImports_4959_);
v___x_5239_ = l_Lean_Options_empty;
v___x_5240_ = 1024;
v___x_5241_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__4));
v___x_5242_ = lean_box(1);
v___x_5243_ = l_Lean_importModules(v___x_5238_, v___x_5239_, v___x_5240_, v___x_5241_, v_anyFailed_4973_, v_anyUnlocated_4974_, v___y_5231_, v___x_5242_);
if (lean_obj_tag(v___x_5243_) == 0)
{
lean_object* v_a_5244_; lean_object* v_linterOverrides_5245_; lean_object* v___x_5246_; uint8_t v___x_5247_; 
v_a_5244_ = lean_ctor_get(v___x_5243_, 0);
lean_inc(v_a_5244_);
lean_dec_ref_known(v___x_5243_, 1);
v_linterOverrides_5245_ = lean_ctor_get(v_args_4960_, 0);
v___x_5246_ = lean_array_get_size(v_linterOverrides_5245_);
v___x_5247_ = lean_nat_dec_lt(v___x_4972_, v___x_5246_);
if (v___x_5247_ == 0)
{
v___y_5182_ = v_a_5244_;
v___y_5183_ = v___x_5239_;
goto v___jp_5181_;
}
else
{
uint8_t v___x_5248_; 
v___x_5248_ = lean_nat_dec_le(v___x_5246_, v___x_5246_);
if (v___x_5248_ == 0)
{
if (v___x_5247_ == 0)
{
v___y_5182_ = v_a_5244_;
v___y_5183_ = v___x_5239_;
goto v___jp_5181_;
}
else
{
size_t v___x_5249_; size_t v___x_5250_; lean_object* v___x_5251_; 
v___x_5249_ = ((size_t)0ULL);
v___x_5250_ = lean_usize_of_nat(v___x_5246_);
v___x_5251_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(v_linterOverrides_5245_, v___x_5249_, v___x_5250_, v___x_5239_);
v___y_5182_ = v_a_5244_;
v___y_5183_ = v___x_5251_;
goto v___jp_5181_;
}
}
else
{
size_t v___x_5252_; size_t v___x_5253_; lean_object* v___x_5254_; 
v___x_5252_ = ((size_t)0ULL);
v___x_5253_ = lean_usize_of_nat(v___x_5246_);
v___x_5254_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(v_linterOverrides_5245_, v___x_5252_, v___x_5253_, v___x_5239_);
v___y_5182_ = v_a_5244_;
v___y_5183_ = v___x_5254_;
goto v___jp_5181_;
}
}
}
else
{
lean_object* v_a_5255_; lean_object* v___x_5257_; uint8_t v_isShared_5258_; uint8_t v_isSharedCheck_5262_; 
lean_del_object(v___x_5002_);
lean_dec(v_snd_5000_);
lean_dec(v_fst_4999_);
lean_del_object(v___x_4997_);
lean_dec(v_fst_4995_);
lean_del_object(v___x_4993_);
lean_dec(v_fst_4991_);
lean_del_object(v___x_4989_);
lean_dec(v_fst_4987_);
lean_del_object(v___x_4985_);
lean_dec(v_fst_4983_);
lean_dec(v___x_4961_);
v_a_5255_ = lean_ctor_get(v___x_5243_, 0);
v_isSharedCheck_5262_ = !lean_is_exclusive(v___x_5243_);
if (v_isSharedCheck_5262_ == 0)
{
v___x_5257_ = v___x_5243_;
v_isShared_5258_ = v_isSharedCheck_5262_;
goto v_resetjp_5256_;
}
else
{
lean_inc(v_a_5255_);
lean_dec(v___x_5243_);
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
else
{
lean_object* v_a_5263_; lean_object* v___x_5265_; uint8_t v_isShared_5266_; uint8_t v_isSharedCheck_5270_; 
lean_del_object(v___x_5002_);
lean_dec(v_snd_5000_);
lean_dec(v_fst_4999_);
lean_del_object(v___x_4997_);
lean_dec(v_fst_4995_);
lean_del_object(v___x_4993_);
lean_dec(v_fst_4991_);
lean_del_object(v___x_4989_);
lean_dec(v_fst_4987_);
lean_del_object(v___x_4985_);
lean_dec(v_fst_4983_);
lean_dec_ref_known(v_envLinterModule_4976_, 1);
lean_dec(v___x_4961_);
v_a_5263_ = lean_ctor_get(v___x_5232_, 0);
v_isSharedCheck_5270_ = !lean_is_exclusive(v___x_5232_);
if (v_isSharedCheck_5270_ == 0)
{
v___x_5265_ = v___x_5232_;
v_isShared_5266_ = v_isSharedCheck_5270_;
goto v_resetjp_5264_;
}
else
{
lean_inc(v_a_5263_);
lean_dec(v___x_5232_);
v___x_5265_ = lean_box(0);
v_isShared_5266_ = v_isSharedCheck_5270_;
goto v_resetjp_5264_;
}
v_resetjp_5264_:
{
lean_object* v___x_5268_; 
if (v_isShared_5266_ == 0)
{
v___x_5268_ = v___x_5265_;
goto v_reusejp_5267_;
}
else
{
lean_object* v_reuseFailAlloc_5269_; 
v_reuseFailAlloc_5269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5269_, 0, v_a_5263_);
v___x_5268_ = v_reuseFailAlloc_5269_;
goto v_reusejp_5267_;
}
v_reusejp_5267_:
{
return v___x_5268_;
}
}
}
}
}
else
{
lean_object* v_a_5273_; lean_object* v___x_5275_; uint8_t v_isShared_5276_; uint8_t v_isSharedCheck_5280_; 
lean_del_object(v___x_5002_);
lean_dec(v_snd_5000_);
lean_dec(v_fst_4999_);
lean_del_object(v___x_4997_);
lean_dec(v_fst_4995_);
lean_del_object(v___x_4993_);
lean_dec(v_fst_4991_);
lean_del_object(v___x_4989_);
lean_dec(v_fst_4987_);
lean_del_object(v___x_4985_);
lean_dec(v_fst_4983_);
lean_dec_ref_known(v_envLinterModule_4976_, 1);
lean_dec(v___x_4961_);
v_a_5273_ = lean_ctor_get(v___x_5225_, 0);
v_isSharedCheck_5280_ = !lean_is_exclusive(v___x_5225_);
if (v_isSharedCheck_5280_ == 0)
{
v___x_5275_ = v___x_5225_;
v_isShared_5276_ = v_isSharedCheck_5280_;
goto v_resetjp_5274_;
}
else
{
lean_inc(v_a_5273_);
lean_dec(v___x_5225_);
v___x_5275_ = lean_box(0);
v_isShared_5276_ = v_isSharedCheck_5280_;
goto v_resetjp_5274_;
}
v_resetjp_5274_:
{
lean_object* v___x_5278_; 
if (v_isShared_5276_ == 0)
{
v___x_5278_ = v___x_5275_;
goto v_reusejp_5277_;
}
else
{
lean_object* v_reuseFailAlloc_5279_; 
v_reuseFailAlloc_5279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5279_, 0, v_a_5273_);
v___x_5278_ = v_reuseFailAlloc_5279_;
goto v_reusejp_5277_;
}
v_reusejp_5277_:
{
return v___x_5278_;
}
}
}
}
else
{
lean_object* v_a_5281_; lean_object* v___x_5283_; uint8_t v_isShared_5284_; uint8_t v_isSharedCheck_5288_; 
lean_del_object(v___x_5002_);
lean_dec(v_snd_5000_);
lean_dec(v_fst_4999_);
lean_del_object(v___x_4997_);
lean_dec(v_fst_4995_);
lean_del_object(v___x_4993_);
lean_dec(v_fst_4991_);
lean_del_object(v___x_4989_);
lean_dec(v_fst_4987_);
lean_del_object(v___x_4985_);
lean_dec(v_fst_4983_);
lean_dec_ref_known(v_envLinterModule_4976_, 1);
lean_dec(v___x_4961_);
v_a_5281_ = lean_ctor_get(v___x_5223_, 0);
v_isSharedCheck_5288_ = !lean_is_exclusive(v___x_5223_);
if (v_isSharedCheck_5288_ == 0)
{
v___x_5283_ = v___x_5223_;
v_isShared_5284_ = v_isSharedCheck_5288_;
goto v_resetjp_5282_;
}
else
{
lean_inc(v_a_5281_);
lean_dec(v___x_5223_);
v___x_5283_ = lean_box(0);
v_isShared_5284_ = v_isSharedCheck_5288_;
goto v_resetjp_5282_;
}
v_resetjp_5282_:
{
lean_object* v___x_5286_; 
if (v_isShared_5284_ == 0)
{
v___x_5286_ = v___x_5283_;
goto v_reusejp_5285_;
}
else
{
lean_object* v_reuseFailAlloc_5287_; 
v_reuseFailAlloc_5287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5287_, 0, v_a_5281_);
v___x_5286_ = v_reuseFailAlloc_5287_;
goto v_reusejp_5285_;
}
v_reusejp_5285_:
{
return v___x_5286_;
}
}
}
v___jp_5006_:
{
uint8_t v_mode_5013_; uint8_t v___x_5014_; uint8_t v___x_5015_; 
v_mode_5013_ = lean_ctor_get_uint8(v_args_4960_, sizeof(void*)*4 + 1);
v___x_5014_ = 2;
v___x_5015_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_5013_, v___x_5014_);
if (v___x_5015_ == 0)
{
lean_object* v___x_5016_; lean_object* v___x_5017_; 
v___x_5016_ = l_Lean_Name_getRoot(v_a_5005_);
lean_inc(v___x_4961_);
v___x_5017_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(v_args_4960_, v___y_5007_, v___x_4961_, v___y_5008_, v___x_5016_, v_fst_4999_);
lean_dec_ref(v___y_5007_);
if (lean_obj_tag(v___x_5017_) == 0)
{
lean_object* v_a_5018_; lean_object* v_outcome_5019_; 
v_a_5018_ = lean_ctor_get(v___x_5017_, 0);
lean_inc(v_a_5018_);
lean_dec_ref_known(v___x_5017_, 1);
v_outcome_5019_ = lean_ctor_get(v_a_5018_, 0);
if (lean_obj_tag(v_outcome_5019_) == 0)
{
uint8_t v_failed_5020_; 
v_failed_5020_ = lean_ctor_get_uint8(v_outcome_5019_, 0);
if (v_failed_5020_ == 0)
{
lean_object* v_checkedModules_5021_; lean_object* v___x_5023_; 
v_checkedModules_5021_ = lean_ctor_get(v_a_5018_, 1);
lean_inc(v_checkedModules_5021_);
lean_dec(v_a_5018_);
if (v_isShared_5003_ == 0)
{
lean_ctor_set(v___x_5002_, 0, v_checkedModules_5021_);
v___x_5023_ = v___x_5002_;
goto v_reusejp_5022_;
}
else
{
lean_object* v_reuseFailAlloc_5038_; 
v_reuseFailAlloc_5038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5038_, 0, v_checkedModules_5021_);
lean_ctor_set(v_reuseFailAlloc_5038_, 1, v_snd_5000_);
v___x_5023_ = v_reuseFailAlloc_5038_;
goto v_reusejp_5022_;
}
v_reusejp_5022_:
{
lean_object* v___x_5025_; 
if (v_isShared_4998_ == 0)
{
lean_ctor_set(v___x_4997_, 1, v___x_5023_);
lean_ctor_set(v___x_4997_, 0, v_codeQualityEntries_5012_);
v___x_5025_ = v___x_4997_;
goto v_reusejp_5024_;
}
else
{
lean_object* v_reuseFailAlloc_5037_; 
v_reuseFailAlloc_5037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5037_, 0, v_codeQualityEntries_5012_);
lean_ctor_set(v_reuseFailAlloc_5037_, 1, v___x_5023_);
v___x_5025_ = v_reuseFailAlloc_5037_;
goto v_reusejp_5024_;
}
v_reusejp_5024_:
{
lean_object* v___x_5027_; 
if (v_isShared_4994_ == 0)
{
lean_ctor_set(v___x_4993_, 1, v___x_5025_);
lean_ctor_set(v___x_4993_, 0, v_records_5011_);
v___x_5027_ = v___x_4993_;
goto v_reusejp_5026_;
}
else
{
lean_object* v_reuseFailAlloc_5036_; 
v_reuseFailAlloc_5036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5036_, 0, v_records_5011_);
lean_ctor_set(v_reuseFailAlloc_5036_, 1, v___x_5025_);
v___x_5027_ = v_reuseFailAlloc_5036_;
goto v_reusejp_5026_;
}
v_reusejp_5026_:
{
lean_object* v___x_5028_; lean_object* v___x_5030_; 
v___x_5028_ = lean_box(v_anyUnlocated_5010_);
if (v_isShared_4990_ == 0)
{
lean_ctor_set(v___x_4989_, 1, v___x_5027_);
lean_ctor_set(v___x_4989_, 0, v___x_5028_);
v___x_5030_ = v___x_4989_;
goto v_reusejp_5029_;
}
else
{
lean_object* v_reuseFailAlloc_5035_; 
v_reuseFailAlloc_5035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5035_, 0, v___x_5028_);
lean_ctor_set(v_reuseFailAlloc_5035_, 1, v___x_5027_);
v___x_5030_ = v_reuseFailAlloc_5035_;
goto v_reusejp_5029_;
}
v_reusejp_5029_:
{
lean_object* v___x_5031_; lean_object* v___x_5033_; 
v___x_5031_ = lean_box(v_anyFailed_5009_);
if (v_isShared_4986_ == 0)
{
lean_ctor_set(v___x_4985_, 1, v___x_5030_);
lean_ctor_set(v___x_4985_, 0, v___x_5031_);
v___x_5033_ = v___x_4985_;
goto v_reusejp_5032_;
}
else
{
lean_object* v_reuseFailAlloc_5034_; 
v_reuseFailAlloc_5034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5034_, 0, v___x_5031_);
lean_ctor_set(v_reuseFailAlloc_5034_, 1, v___x_5030_);
v___x_5033_ = v_reuseFailAlloc_5034_;
goto v_reusejp_5032_;
}
v_reusejp_5032_:
{
v_a_4968_ = v___x_5033_;
goto v___jp_4967_;
}
}
}
}
}
}
else
{
lean_object* v_checkedModules_5039_; lean_object* v___x_5041_; 
v_checkedModules_5039_ = lean_ctor_get(v_a_5018_, 1);
lean_inc(v_checkedModules_5039_);
lean_dec(v_a_5018_);
if (v_isShared_5003_ == 0)
{
lean_ctor_set(v___x_5002_, 0, v_checkedModules_5039_);
v___x_5041_ = v___x_5002_;
goto v_reusejp_5040_;
}
else
{
lean_object* v_reuseFailAlloc_5056_; 
v_reuseFailAlloc_5056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5056_, 0, v_checkedModules_5039_);
lean_ctor_set(v_reuseFailAlloc_5056_, 1, v_snd_5000_);
v___x_5041_ = v_reuseFailAlloc_5056_;
goto v_reusejp_5040_;
}
v_reusejp_5040_:
{
lean_object* v___x_5043_; 
if (v_isShared_4998_ == 0)
{
lean_ctor_set(v___x_4997_, 1, v___x_5041_);
lean_ctor_set(v___x_4997_, 0, v_codeQualityEntries_5012_);
v___x_5043_ = v___x_4997_;
goto v_reusejp_5042_;
}
else
{
lean_object* v_reuseFailAlloc_5055_; 
v_reuseFailAlloc_5055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5055_, 0, v_codeQualityEntries_5012_);
lean_ctor_set(v_reuseFailAlloc_5055_, 1, v___x_5041_);
v___x_5043_ = v_reuseFailAlloc_5055_;
goto v_reusejp_5042_;
}
v_reusejp_5042_:
{
lean_object* v___x_5045_; 
if (v_isShared_4994_ == 0)
{
lean_ctor_set(v___x_4993_, 1, v___x_5043_);
lean_ctor_set(v___x_4993_, 0, v_records_5011_);
v___x_5045_ = v___x_4993_;
goto v_reusejp_5044_;
}
else
{
lean_object* v_reuseFailAlloc_5054_; 
v_reuseFailAlloc_5054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5054_, 0, v_records_5011_);
lean_ctor_set(v_reuseFailAlloc_5054_, 1, v___x_5043_);
v___x_5045_ = v_reuseFailAlloc_5054_;
goto v_reusejp_5044_;
}
v_reusejp_5044_:
{
lean_object* v___x_5046_; lean_object* v___x_5048_; 
v___x_5046_ = lean_box(v_anyUnlocated_5010_);
if (v_isShared_4990_ == 0)
{
lean_ctor_set(v___x_4989_, 1, v___x_5045_);
lean_ctor_set(v___x_4989_, 0, v___x_5046_);
v___x_5048_ = v___x_4989_;
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
v___x_5049_ = lean_box(v_anyUnlocated_4974_);
if (v_isShared_4986_ == 0)
{
lean_ctor_set(v___x_4985_, 1, v___x_5048_);
lean_ctor_set(v___x_4985_, 0, v___x_5049_);
v___x_5051_ = v___x_4985_;
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
v_a_4968_ = v___x_5051_;
goto v___jp_4967_;
}
}
}
}
}
}
}
else
{
lean_object* v_checkedModules_5057_; lean_object* v_records_5058_; uint8_t v_unlocated_5059_; lean_object* v___x_5060_; 
lean_inc_ref(v_outcome_5019_);
v_checkedModules_5057_ = lean_ctor_get(v_a_5018_, 1);
lean_inc(v_checkedModules_5057_);
lean_dec(v_a_5018_);
v_records_5058_ = lean_ctor_get(v_outcome_5019_, 0);
lean_inc_ref(v_records_5058_);
v_unlocated_5059_ = lean_ctor_get_uint8(v_outcome_5019_, sizeof(void*)*1);
lean_dec_ref_known(v_outcome_5019_, 1);
v___x_5060_ = l_Array_append___redArg(v_records_5011_, v_records_5058_);
lean_dec_ref(v_records_5058_);
if (v_unlocated_5059_ == 0)
{
lean_object* v___x_5062_; 
if (v_isShared_5003_ == 0)
{
lean_ctor_set(v___x_5002_, 0, v_checkedModules_5057_);
v___x_5062_ = v___x_5002_;
goto v_reusejp_5061_;
}
else
{
lean_object* v_reuseFailAlloc_5077_; 
v_reuseFailAlloc_5077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5077_, 0, v_checkedModules_5057_);
lean_ctor_set(v_reuseFailAlloc_5077_, 1, v_snd_5000_);
v___x_5062_ = v_reuseFailAlloc_5077_;
goto v_reusejp_5061_;
}
v_reusejp_5061_:
{
lean_object* v___x_5064_; 
if (v_isShared_4998_ == 0)
{
lean_ctor_set(v___x_4997_, 1, v___x_5062_);
lean_ctor_set(v___x_4997_, 0, v_codeQualityEntries_5012_);
v___x_5064_ = v___x_4997_;
goto v_reusejp_5063_;
}
else
{
lean_object* v_reuseFailAlloc_5076_; 
v_reuseFailAlloc_5076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5076_, 0, v_codeQualityEntries_5012_);
lean_ctor_set(v_reuseFailAlloc_5076_, 1, v___x_5062_);
v___x_5064_ = v_reuseFailAlloc_5076_;
goto v_reusejp_5063_;
}
v_reusejp_5063_:
{
lean_object* v___x_5066_; 
if (v_isShared_4994_ == 0)
{
lean_ctor_set(v___x_4993_, 1, v___x_5064_);
lean_ctor_set(v___x_4993_, 0, v___x_5060_);
v___x_5066_ = v___x_4993_;
goto v_reusejp_5065_;
}
else
{
lean_object* v_reuseFailAlloc_5075_; 
v_reuseFailAlloc_5075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5075_, 0, v___x_5060_);
lean_ctor_set(v_reuseFailAlloc_5075_, 1, v___x_5064_);
v___x_5066_ = v_reuseFailAlloc_5075_;
goto v_reusejp_5065_;
}
v_reusejp_5065_:
{
lean_object* v___x_5067_; lean_object* v___x_5069_; 
v___x_5067_ = lean_box(v_anyUnlocated_5010_);
if (v_isShared_4990_ == 0)
{
lean_ctor_set(v___x_4989_, 1, v___x_5066_);
lean_ctor_set(v___x_4989_, 0, v___x_5067_);
v___x_5069_ = v___x_4989_;
goto v_reusejp_5068_;
}
else
{
lean_object* v_reuseFailAlloc_5074_; 
v_reuseFailAlloc_5074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5074_, 0, v___x_5067_);
lean_ctor_set(v_reuseFailAlloc_5074_, 1, v___x_5066_);
v___x_5069_ = v_reuseFailAlloc_5074_;
goto v_reusejp_5068_;
}
v_reusejp_5068_:
{
lean_object* v___x_5070_; lean_object* v___x_5072_; 
v___x_5070_ = lean_box(v_anyFailed_5009_);
if (v_isShared_4986_ == 0)
{
lean_ctor_set(v___x_4985_, 1, v___x_5069_);
lean_ctor_set(v___x_4985_, 0, v___x_5070_);
v___x_5072_ = v___x_4985_;
goto v_reusejp_5071_;
}
else
{
lean_object* v_reuseFailAlloc_5073_; 
v_reuseFailAlloc_5073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5073_, 0, v___x_5070_);
lean_ctor_set(v_reuseFailAlloc_5073_, 1, v___x_5069_);
v___x_5072_ = v_reuseFailAlloc_5073_;
goto v_reusejp_5071_;
}
v_reusejp_5071_:
{
v_a_4968_ = v___x_5072_;
goto v___jp_4967_;
}
}
}
}
}
}
else
{
lean_object* v___x_5079_; 
if (v_isShared_5003_ == 0)
{
lean_ctor_set(v___x_5002_, 0, v_checkedModules_5057_);
v___x_5079_ = v___x_5002_;
goto v_reusejp_5078_;
}
else
{
lean_object* v_reuseFailAlloc_5094_; 
v_reuseFailAlloc_5094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5094_, 0, v_checkedModules_5057_);
lean_ctor_set(v_reuseFailAlloc_5094_, 1, v_snd_5000_);
v___x_5079_ = v_reuseFailAlloc_5094_;
goto v_reusejp_5078_;
}
v_reusejp_5078_:
{
lean_object* v___x_5081_; 
if (v_isShared_4998_ == 0)
{
lean_ctor_set(v___x_4997_, 1, v___x_5079_);
lean_ctor_set(v___x_4997_, 0, v_codeQualityEntries_5012_);
v___x_5081_ = v___x_4997_;
goto v_reusejp_5080_;
}
else
{
lean_object* v_reuseFailAlloc_5093_; 
v_reuseFailAlloc_5093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5093_, 0, v_codeQualityEntries_5012_);
lean_ctor_set(v_reuseFailAlloc_5093_, 1, v___x_5079_);
v___x_5081_ = v_reuseFailAlloc_5093_;
goto v_reusejp_5080_;
}
v_reusejp_5080_:
{
lean_object* v___x_5083_; 
if (v_isShared_4994_ == 0)
{
lean_ctor_set(v___x_4993_, 1, v___x_5081_);
lean_ctor_set(v___x_4993_, 0, v___x_5060_);
v___x_5083_ = v___x_4993_;
goto v_reusejp_5082_;
}
else
{
lean_object* v_reuseFailAlloc_5092_; 
v_reuseFailAlloc_5092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5092_, 0, v___x_5060_);
lean_ctor_set(v_reuseFailAlloc_5092_, 1, v___x_5081_);
v___x_5083_ = v_reuseFailAlloc_5092_;
goto v_reusejp_5082_;
}
v_reusejp_5082_:
{
lean_object* v___x_5084_; lean_object* v___x_5086_; 
v___x_5084_ = lean_box(v_anyUnlocated_4974_);
if (v_isShared_4990_ == 0)
{
lean_ctor_set(v___x_4989_, 1, v___x_5083_);
lean_ctor_set(v___x_4989_, 0, v___x_5084_);
v___x_5086_ = v___x_4989_;
goto v_reusejp_5085_;
}
else
{
lean_object* v_reuseFailAlloc_5091_; 
v_reuseFailAlloc_5091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5091_, 0, v___x_5084_);
lean_ctor_set(v_reuseFailAlloc_5091_, 1, v___x_5083_);
v___x_5086_ = v_reuseFailAlloc_5091_;
goto v_reusejp_5085_;
}
v_reusejp_5085_:
{
lean_object* v___x_5087_; lean_object* v___x_5089_; 
v___x_5087_ = lean_box(v_anyFailed_5009_);
if (v_isShared_4986_ == 0)
{
lean_ctor_set(v___x_4985_, 1, v___x_5086_);
lean_ctor_set(v___x_4985_, 0, v___x_5087_);
v___x_5089_ = v___x_4985_;
goto v_reusejp_5088_;
}
else
{
lean_object* v_reuseFailAlloc_5090_; 
v_reuseFailAlloc_5090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5090_, 0, v___x_5087_);
lean_ctor_set(v_reuseFailAlloc_5090_, 1, v___x_5086_);
v___x_5089_ = v_reuseFailAlloc_5090_;
goto v_reusejp_5088_;
}
v_reusejp_5088_:
{
v_a_4968_ = v___x_5089_;
goto v___jp_4967_;
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
lean_object* v_a_5095_; lean_object* v___x_5097_; uint8_t v_isShared_5098_; uint8_t v_isSharedCheck_5102_; 
lean_dec_ref(v_codeQualityEntries_5012_);
lean_dec_ref(v_records_5011_);
lean_del_object(v___x_5002_);
lean_dec(v_snd_5000_);
lean_del_object(v___x_4997_);
lean_del_object(v___x_4993_);
lean_del_object(v___x_4989_);
lean_del_object(v___x_4985_);
lean_dec(v___x_4961_);
v_a_5095_ = lean_ctor_get(v___x_5017_, 0);
v_isSharedCheck_5102_ = !lean_is_exclusive(v___x_5017_);
if (v_isSharedCheck_5102_ == 0)
{
v___x_5097_ = v___x_5017_;
v_isShared_5098_ = v_isSharedCheck_5102_;
goto v_resetjp_5096_;
}
else
{
lean_inc(v_a_5095_);
lean_dec(v___x_5017_);
v___x_5097_ = lean_box(0);
v_isShared_5098_ = v_isSharedCheck_5102_;
goto v_resetjp_5096_;
}
v_resetjp_5096_:
{
lean_object* v___x_5100_; 
if (v_isShared_5098_ == 0)
{
v___x_5100_ = v___x_5097_;
goto v_reusejp_5099_;
}
else
{
lean_object* v_reuseFailAlloc_5101_; 
v_reuseFailAlloc_5101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5101_, 0, v_a_5095_);
v___x_5100_ = v_reuseFailAlloc_5101_;
goto v_reusejp_5099_;
}
v_reusejp_5099_:
{
return v___x_5100_;
}
}
}
}
else
{
lean_object* v___x_5103_; lean_object* v_fst_5104_; lean_object* v_snd_5105_; lean_object* v___x_5107_; uint8_t v_isShared_5108_; uint8_t v_isSharedCheck_5157_; 
lean_del_object(v___x_4985_);
v___x_5103_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality(v_args_4960_, v___y_5007_, v___y_5008_, v_a_5005_, v_snd_5000_);
lean_dec_ref(v___y_5007_);
v_fst_5104_ = lean_ctor_get(v___x_5103_, 0);
v_snd_5105_ = lean_ctor_get(v___x_5103_, 1);
v_isSharedCheck_5157_ = !lean_is_exclusive(v___x_5103_);
if (v_isSharedCheck_5157_ == 0)
{
v___x_5107_ = v___x_5103_;
v_isShared_5108_ = v_isSharedCheck_5157_;
goto v_resetjp_5106_;
}
else
{
lean_inc(v_snd_5105_);
lean_inc(v_fst_5104_);
lean_dec(v___x_5103_);
v___x_5107_ = lean_box(0);
v_isShared_5108_ = v_isSharedCheck_5157_;
goto v_resetjp_5106_;
}
v_resetjp_5106_:
{
lean_object* v___x_5109_; lean_object* v___x_5110_; 
v___x_5109_ = l_Array_append___redArg(v_codeQualityEntries_5012_, v_fst_5104_);
lean_dec(v_fst_5104_);
lean_inc(v_a_5005_);
lean_inc(v___x_4961_);
v___x_5110_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(v___x_4961_, v___y_5008_, v_a_5005_);
if (lean_obj_tag(v___x_5110_) == 0)
{
lean_object* v_a_5111_; lean_object* v_entries_5112_; uint8_t v_failed_5113_; lean_object* v___x_5114_; 
v_a_5111_ = lean_ctor_get(v___x_5110_, 0);
lean_inc(v_a_5111_);
lean_dec_ref_known(v___x_5110_, 1);
v_entries_5112_ = lean_ctor_get(v_a_5111_, 0);
lean_inc_ref(v_entries_5112_);
v_failed_5113_ = lean_ctor_get_uint8(v_a_5111_, sizeof(void*)*1);
lean_dec(v_a_5111_);
v___x_5114_ = l_Array_append___redArg(v___x_5109_, v_entries_5112_);
lean_dec_ref(v_entries_5112_);
if (v_failed_5113_ == 0)
{
lean_object* v___x_5116_; 
if (v_isShared_5108_ == 0)
{
lean_ctor_set(v___x_5107_, 0, v_fst_4999_);
v___x_5116_ = v___x_5107_;
goto v_reusejp_5115_;
}
else
{
lean_object* v_reuseFailAlloc_5131_; 
v_reuseFailAlloc_5131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5131_, 0, v_fst_4999_);
lean_ctor_set(v_reuseFailAlloc_5131_, 1, v_snd_5105_);
v___x_5116_ = v_reuseFailAlloc_5131_;
goto v_reusejp_5115_;
}
v_reusejp_5115_:
{
lean_object* v___x_5118_; 
if (v_isShared_5003_ == 0)
{
lean_ctor_set(v___x_5002_, 1, v___x_5116_);
lean_ctor_set(v___x_5002_, 0, v___x_5114_);
v___x_5118_ = v___x_5002_;
goto v_reusejp_5117_;
}
else
{
lean_object* v_reuseFailAlloc_5130_; 
v_reuseFailAlloc_5130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5130_, 0, v___x_5114_);
lean_ctor_set(v_reuseFailAlloc_5130_, 1, v___x_5116_);
v___x_5118_ = v_reuseFailAlloc_5130_;
goto v_reusejp_5117_;
}
v_reusejp_5117_:
{
lean_object* v___x_5120_; 
if (v_isShared_4998_ == 0)
{
lean_ctor_set(v___x_4997_, 1, v___x_5118_);
lean_ctor_set(v___x_4997_, 0, v_records_5011_);
v___x_5120_ = v___x_4997_;
goto v_reusejp_5119_;
}
else
{
lean_object* v_reuseFailAlloc_5129_; 
v_reuseFailAlloc_5129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5129_, 0, v_records_5011_);
lean_ctor_set(v_reuseFailAlloc_5129_, 1, v___x_5118_);
v___x_5120_ = v_reuseFailAlloc_5129_;
goto v_reusejp_5119_;
}
v_reusejp_5119_:
{
lean_object* v___x_5121_; lean_object* v___x_5123_; 
v___x_5121_ = lean_box(v_anyUnlocated_5010_);
if (v_isShared_4994_ == 0)
{
lean_ctor_set(v___x_4993_, 1, v___x_5120_);
lean_ctor_set(v___x_4993_, 0, v___x_5121_);
v___x_5123_ = v___x_4993_;
goto v_reusejp_5122_;
}
else
{
lean_object* v_reuseFailAlloc_5128_; 
v_reuseFailAlloc_5128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5128_, 0, v___x_5121_);
lean_ctor_set(v_reuseFailAlloc_5128_, 1, v___x_5120_);
v___x_5123_ = v_reuseFailAlloc_5128_;
goto v_reusejp_5122_;
}
v_reusejp_5122_:
{
lean_object* v___x_5124_; lean_object* v___x_5126_; 
v___x_5124_ = lean_box(v_anyFailed_5009_);
if (v_isShared_4990_ == 0)
{
lean_ctor_set(v___x_4989_, 1, v___x_5123_);
lean_ctor_set(v___x_4989_, 0, v___x_5124_);
v___x_5126_ = v___x_4989_;
goto v_reusejp_5125_;
}
else
{
lean_object* v_reuseFailAlloc_5127_; 
v_reuseFailAlloc_5127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5127_, 0, v___x_5124_);
lean_ctor_set(v_reuseFailAlloc_5127_, 1, v___x_5123_);
v___x_5126_ = v_reuseFailAlloc_5127_;
goto v_reusejp_5125_;
}
v_reusejp_5125_:
{
v_a_4968_ = v___x_5126_;
goto v___jp_4967_;
}
}
}
}
}
}
else
{
lean_object* v___x_5133_; 
if (v_isShared_5108_ == 0)
{
lean_ctor_set(v___x_5107_, 0, v_fst_4999_);
v___x_5133_ = v___x_5107_;
goto v_reusejp_5132_;
}
else
{
lean_object* v_reuseFailAlloc_5148_; 
v_reuseFailAlloc_5148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5148_, 0, v_fst_4999_);
lean_ctor_set(v_reuseFailAlloc_5148_, 1, v_snd_5105_);
v___x_5133_ = v_reuseFailAlloc_5148_;
goto v_reusejp_5132_;
}
v_reusejp_5132_:
{
lean_object* v___x_5135_; 
if (v_isShared_5003_ == 0)
{
lean_ctor_set(v___x_5002_, 1, v___x_5133_);
lean_ctor_set(v___x_5002_, 0, v___x_5114_);
v___x_5135_ = v___x_5002_;
goto v_reusejp_5134_;
}
else
{
lean_object* v_reuseFailAlloc_5147_; 
v_reuseFailAlloc_5147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5147_, 0, v___x_5114_);
lean_ctor_set(v_reuseFailAlloc_5147_, 1, v___x_5133_);
v___x_5135_ = v_reuseFailAlloc_5147_;
goto v_reusejp_5134_;
}
v_reusejp_5134_:
{
lean_object* v___x_5137_; 
if (v_isShared_4998_ == 0)
{
lean_ctor_set(v___x_4997_, 1, v___x_5135_);
lean_ctor_set(v___x_4997_, 0, v_records_5011_);
v___x_5137_ = v___x_4997_;
goto v_reusejp_5136_;
}
else
{
lean_object* v_reuseFailAlloc_5146_; 
v_reuseFailAlloc_5146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5146_, 0, v_records_5011_);
lean_ctor_set(v_reuseFailAlloc_5146_, 1, v___x_5135_);
v___x_5137_ = v_reuseFailAlloc_5146_;
goto v_reusejp_5136_;
}
v_reusejp_5136_:
{
lean_object* v___x_5138_; lean_object* v___x_5140_; 
v___x_5138_ = lean_box(v_anyUnlocated_5010_);
if (v_isShared_4994_ == 0)
{
lean_ctor_set(v___x_4993_, 1, v___x_5137_);
lean_ctor_set(v___x_4993_, 0, v___x_5138_);
v___x_5140_ = v___x_4993_;
goto v_reusejp_5139_;
}
else
{
lean_object* v_reuseFailAlloc_5145_; 
v_reuseFailAlloc_5145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5145_, 0, v___x_5138_);
lean_ctor_set(v_reuseFailAlloc_5145_, 1, v___x_5137_);
v___x_5140_ = v_reuseFailAlloc_5145_;
goto v_reusejp_5139_;
}
v_reusejp_5139_:
{
lean_object* v___x_5141_; lean_object* v___x_5143_; 
v___x_5141_ = lean_box(v_anyUnlocated_4974_);
if (v_isShared_4990_ == 0)
{
lean_ctor_set(v___x_4989_, 1, v___x_5140_);
lean_ctor_set(v___x_4989_, 0, v___x_5141_);
v___x_5143_ = v___x_4989_;
goto v_reusejp_5142_;
}
else
{
lean_object* v_reuseFailAlloc_5144_; 
v_reuseFailAlloc_5144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5144_, 0, v___x_5141_);
lean_ctor_set(v_reuseFailAlloc_5144_, 1, v___x_5140_);
v___x_5143_ = v_reuseFailAlloc_5144_;
goto v_reusejp_5142_;
}
v_reusejp_5142_:
{
v_a_4968_ = v___x_5143_;
goto v___jp_4967_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5149_; lean_object* v___x_5151_; uint8_t v_isShared_5152_; uint8_t v_isSharedCheck_5156_; 
lean_dec_ref(v___x_5109_);
lean_del_object(v___x_5107_);
lean_dec(v_snd_5105_);
lean_dec_ref(v_records_5011_);
lean_del_object(v___x_5002_);
lean_dec(v_fst_4999_);
lean_del_object(v___x_4997_);
lean_del_object(v___x_4993_);
lean_del_object(v___x_4989_);
lean_dec(v___x_4961_);
v_a_5149_ = lean_ctor_get(v___x_5110_, 0);
v_isSharedCheck_5156_ = !lean_is_exclusive(v___x_5110_);
if (v_isSharedCheck_5156_ == 0)
{
v___x_5151_ = v___x_5110_;
v_isShared_5152_ = v_isSharedCheck_5156_;
goto v_resetjp_5150_;
}
else
{
lean_inc(v_a_5149_);
lean_dec(v___x_5110_);
v___x_5151_ = lean_box(0);
v_isShared_5152_ = v_isSharedCheck_5156_;
goto v_resetjp_5150_;
}
v_resetjp_5150_:
{
lean_object* v___x_5154_; 
if (v_isShared_5152_ == 0)
{
v___x_5154_ = v___x_5151_;
goto v_reusejp_5153_;
}
else
{
lean_object* v_reuseFailAlloc_5155_; 
v_reuseFailAlloc_5155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5155_, 0, v_a_5149_);
v___x_5154_ = v_reuseFailAlloc_5155_;
goto v_reusejp_5153_;
}
v_reusejp_5153_:
{
return v___x_5154_;
}
}
}
}
}
}
v___jp_5158_:
{
lean_object* v___x_5165_; 
lean_inc(v_a_5005_);
lean_inc_ref(v___y_5160_);
lean_inc(v___x_4961_);
lean_inc_ref(v___y_5159_);
v___x_5165_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(v_args_4960_, v___y_5159_, v___x_4961_, v___y_5160_, v_a_5005_);
if (lean_obj_tag(v___x_5165_) == 0)
{
lean_object* v_a_5166_; 
v_a_5166_ = lean_ctor_get(v___x_5165_, 0);
lean_inc(v_a_5166_);
lean_dec_ref_known(v___x_5165_, 1);
switch(lean_obj_tag(v_a_5166_))
{
case 0:
{
uint8_t v_failed_5167_; 
v_failed_5167_ = lean_ctor_get_uint8(v_a_5166_, 0);
lean_dec_ref_known(v_a_5166_, 0);
if (v_failed_5167_ == 0)
{
v___y_5007_ = v___y_5159_;
v___y_5008_ = v___y_5160_;
v_anyFailed_5009_ = v_anyFailed_5161_;
v_anyUnlocated_5010_ = v_anyUnlocated_5162_;
v_records_5011_ = v_records_5163_;
v_codeQualityEntries_5012_ = v_codeQualityEntries_5164_;
goto v___jp_5006_;
}
else
{
v___y_5007_ = v___y_5159_;
v___y_5008_ = v___y_5160_;
v_anyFailed_5009_ = v_anyUnlocated_4974_;
v_anyUnlocated_5010_ = v_anyUnlocated_5162_;
v_records_5011_ = v_records_5163_;
v_codeQualityEntries_5012_ = v_codeQualityEntries_5164_;
goto v___jp_5006_;
}
}
case 1:
{
lean_object* v_records_5168_; uint8_t v_unlocated_5169_; lean_object* v___x_5170_; 
v_records_5168_ = lean_ctor_get(v_a_5166_, 0);
lean_inc_ref(v_records_5168_);
v_unlocated_5169_ = lean_ctor_get_uint8(v_a_5166_, sizeof(void*)*1);
lean_dec_ref_known(v_a_5166_, 1);
v___x_5170_ = l_Array_append___redArg(v_records_5163_, v_records_5168_);
lean_dec_ref(v_records_5168_);
if (v_unlocated_5169_ == 0)
{
v___y_5007_ = v___y_5159_;
v___y_5008_ = v___y_5160_;
v_anyFailed_5009_ = v_anyFailed_5161_;
v_anyUnlocated_5010_ = v_anyUnlocated_5162_;
v_records_5011_ = v___x_5170_;
v_codeQualityEntries_5012_ = v_codeQualityEntries_5164_;
goto v___jp_5006_;
}
else
{
v___y_5007_ = v___y_5159_;
v___y_5008_ = v___y_5160_;
v_anyFailed_5009_ = v_anyFailed_5161_;
v_anyUnlocated_5010_ = v_anyUnlocated_4974_;
v_records_5011_ = v___x_5170_;
v_codeQualityEntries_5012_ = v_codeQualityEntries_5164_;
goto v___jp_5006_;
}
}
default: 
{
lean_object* v_entries_5171_; lean_object* v___x_5172_; 
v_entries_5171_ = lean_ctor_get(v_a_5166_, 0);
lean_inc_ref(v_entries_5171_);
lean_dec_ref_known(v_a_5166_, 1);
v___x_5172_ = l_Array_append___redArg(v_codeQualityEntries_5164_, v_entries_5171_);
lean_dec_ref(v_entries_5171_);
v___y_5007_ = v___y_5159_;
v___y_5008_ = v___y_5160_;
v_anyFailed_5009_ = v_anyFailed_5161_;
v_anyUnlocated_5010_ = v_anyUnlocated_5162_;
v_records_5011_ = v_records_5163_;
v_codeQualityEntries_5012_ = v___x_5172_;
goto v___jp_5006_;
}
}
}
else
{
lean_object* v_a_5173_; lean_object* v___x_5175_; uint8_t v_isShared_5176_; uint8_t v_isSharedCheck_5180_; 
lean_dec_ref(v_codeQualityEntries_5164_);
lean_dec_ref(v_records_5163_);
lean_dec_ref(v___y_5160_);
lean_dec_ref(v___y_5159_);
lean_del_object(v___x_5002_);
lean_dec(v_snd_5000_);
lean_dec(v_fst_4999_);
lean_del_object(v___x_4997_);
lean_del_object(v___x_4993_);
lean_del_object(v___x_4989_);
lean_del_object(v___x_4985_);
lean_dec(v___x_4961_);
v_a_5173_ = lean_ctor_get(v___x_5165_, 0);
v_isSharedCheck_5180_ = !lean_is_exclusive(v___x_5165_);
if (v_isSharedCheck_5180_ == 0)
{
v___x_5175_ = v___x_5165_;
v_isShared_5176_ = v_isSharedCheck_5180_;
goto v_resetjp_5174_;
}
else
{
lean_inc(v_a_5173_);
lean_dec(v___x_5165_);
v___x_5175_ = lean_box(0);
v_isShared_5176_ = v_isSharedCheck_5180_;
goto v_resetjp_5174_;
}
v_resetjp_5174_:
{
lean_object* v___x_5178_; 
if (v_isShared_5176_ == 0)
{
v___x_5178_ = v___x_5175_;
goto v_reusejp_5177_;
}
else
{
lean_object* v_reuseFailAlloc_5179_; 
v_reuseFailAlloc_5179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5179_, 0, v_a_5173_);
v___x_5178_ = v_reuseFailAlloc_5179_;
goto v_reusejp_5177_;
}
v_reusejp_5177_:
{
return v___x_5178_;
}
}
}
}
v___jp_5181_:
{
lean_object* v___x_5184_; lean_object* v_toEnvExtension_5185_; lean_object* v_asyncMode_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v_merged_5189_; lean_object* v___x_5191_; uint8_t v_isShared_5192_; uint8_t v_isSharedCheck_5220_; 
v___x_5184_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_5185_ = lean_ctor_get(v___x_5184_, 0);
v_asyncMode_5186_ = lean_ctor_get(v_toEnvExtension_5185_, 2);
v___x_5187_ = lean_box(0);
lean_inc_ref(v___y_5182_);
v___x_5188_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_5004_, v___x_5184_, v___y_5182_, v_asyncMode_5186_, v___x_5187_, v_anyFailed_4973_);
v_merged_5189_ = lean_ctor_get(v___x_5188_, 0);
v_isSharedCheck_5220_ = !lean_is_exclusive(v___x_5188_);
if (v_isSharedCheck_5220_ == 0)
{
lean_object* v_unused_5221_; 
v_unused_5221_ = lean_ctor_get(v___x_5188_, 1);
lean_dec(v_unused_5221_);
v___x_5191_ = v___x_5188_;
v_isShared_5192_ = v_isSharedCheck_5220_;
goto v_resetjp_5190_;
}
else
{
lean_inc(v_merged_5189_);
lean_dec(v___x_5188_);
v___x_5191_ = lean_box(0);
v_isShared_5192_ = v_isSharedCheck_5220_;
goto v_resetjp_5190_;
}
v_resetjp_5190_:
{
lean_object* v___x_5194_; 
if (v_isShared_5192_ == 0)
{
lean_ctor_set(v___x_5191_, 1, v_merged_5189_);
lean_ctor_set(v___x_5191_, 0, v___y_5183_);
v___x_5194_ = v___x_5191_;
goto v_reusejp_5193_;
}
else
{
lean_object* v_reuseFailAlloc_5219_; 
v_reuseFailAlloc_5219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5219_, 0, v___y_5183_);
lean_ctor_set(v_reuseFailAlloc_5219_, 1, v_merged_5189_);
v___x_5194_ = v_reuseFailAlloc_5219_;
goto v_reusejp_5193_;
}
v_reusejp_5193_:
{
lean_object* v___x_5195_; 
v___x_5195_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(v_args_4960_, v___x_5194_, v___y_5182_, v_a_5005_);
if (lean_obj_tag(v___x_5195_) == 0)
{
lean_object* v_a_5196_; 
v_a_5196_ = lean_ctor_get(v___x_5195_, 0);
lean_inc(v_a_5196_);
lean_dec_ref_known(v___x_5195_, 1);
switch(lean_obj_tag(v_a_5196_))
{
case 0:
{
uint8_t v___x_5197_; 
v___x_5197_ = lean_unbox(v_fst_4983_);
lean_dec(v_fst_4983_);
if (v___x_5197_ == 0)
{
uint8_t v_failed_5198_; uint8_t v___x_5199_; 
v_failed_5198_ = lean_ctor_get_uint8(v_a_5196_, 0);
lean_dec_ref_known(v_a_5196_, 0);
v___x_5199_ = lean_unbox(v_fst_4987_);
lean_dec(v_fst_4987_);
v___y_5159_ = v___x_5194_;
v___y_5160_ = v___y_5182_;
v_anyFailed_5161_ = v_failed_5198_;
v_anyUnlocated_5162_ = v___x_5199_;
v_records_5163_ = v_fst_4991_;
v_codeQualityEntries_5164_ = v_fst_4995_;
goto v___jp_5158_;
}
else
{
uint8_t v___x_5200_; 
lean_dec_ref_known(v_a_5196_, 0);
v___x_5200_ = lean_unbox(v_fst_4987_);
lean_dec(v_fst_4987_);
v___y_5159_ = v___x_5194_;
v___y_5160_ = v___y_5182_;
v_anyFailed_5161_ = v_anyUnlocated_4974_;
v_anyUnlocated_5162_ = v___x_5200_;
v_records_5163_ = v_fst_4991_;
v_codeQualityEntries_5164_ = v_fst_4995_;
goto v___jp_5158_;
}
}
case 1:
{
lean_object* v_records_5201_; uint8_t v_unlocated_5202_; lean_object* v___x_5203_; 
v_records_5201_ = lean_ctor_get(v_a_5196_, 0);
lean_inc_ref(v_records_5201_);
v_unlocated_5202_ = lean_ctor_get_uint8(v_a_5196_, sizeof(void*)*1);
lean_dec_ref_known(v_a_5196_, 1);
v___x_5203_ = l_Array_append___redArg(v_fst_4991_, v_records_5201_);
lean_dec_ref(v_records_5201_);
if (v_unlocated_5202_ == 0)
{
uint8_t v___x_5204_; uint8_t v___x_5205_; 
v___x_5204_ = lean_unbox(v_fst_4983_);
lean_dec(v_fst_4983_);
v___x_5205_ = lean_unbox(v_fst_4987_);
lean_dec(v_fst_4987_);
v___y_5159_ = v___x_5194_;
v___y_5160_ = v___y_5182_;
v_anyFailed_5161_ = v___x_5204_;
v_anyUnlocated_5162_ = v___x_5205_;
v_records_5163_ = v___x_5203_;
v_codeQualityEntries_5164_ = v_fst_4995_;
goto v___jp_5158_;
}
else
{
uint8_t v___x_5206_; 
lean_dec(v_fst_4987_);
v___x_5206_ = lean_unbox(v_fst_4983_);
lean_dec(v_fst_4983_);
v___y_5159_ = v___x_5194_;
v___y_5160_ = v___y_5182_;
v_anyFailed_5161_ = v___x_5206_;
v_anyUnlocated_5162_ = v_anyUnlocated_4974_;
v_records_5163_ = v___x_5203_;
v_codeQualityEntries_5164_ = v_fst_4995_;
goto v___jp_5158_;
}
}
default: 
{
lean_object* v_entries_5207_; lean_object* v___x_5208_; uint8_t v___x_5209_; uint8_t v___x_5210_; 
v_entries_5207_ = lean_ctor_get(v_a_5196_, 0);
lean_inc_ref(v_entries_5207_);
lean_dec_ref_known(v_a_5196_, 1);
v___x_5208_ = l_Array_append___redArg(v_fst_4995_, v_entries_5207_);
lean_dec_ref(v_entries_5207_);
v___x_5209_ = lean_unbox(v_fst_4983_);
lean_dec(v_fst_4983_);
v___x_5210_ = lean_unbox(v_fst_4987_);
lean_dec(v_fst_4987_);
v___y_5159_ = v___x_5194_;
v___y_5160_ = v___y_5182_;
v_anyFailed_5161_ = v___x_5209_;
v_anyUnlocated_5162_ = v___x_5210_;
v_records_5163_ = v_fst_4991_;
v_codeQualityEntries_5164_ = v___x_5208_;
goto v___jp_5158_;
}
}
}
else
{
lean_object* v_a_5211_; lean_object* v___x_5213_; uint8_t v_isShared_5214_; uint8_t v_isSharedCheck_5218_; 
lean_dec_ref(v___x_5194_);
lean_dec_ref(v___y_5182_);
lean_del_object(v___x_5002_);
lean_dec(v_snd_5000_);
lean_dec(v_fst_4999_);
lean_del_object(v___x_4997_);
lean_dec(v_fst_4995_);
lean_del_object(v___x_4993_);
lean_dec(v_fst_4991_);
lean_del_object(v___x_4989_);
lean_dec(v_fst_4987_);
lean_del_object(v___x_4985_);
lean_dec(v_fst_4983_);
lean_dec(v___x_4961_);
v_a_5211_ = lean_ctor_get(v___x_5195_, 0);
v_isSharedCheck_5218_ = !lean_is_exclusive(v___x_5195_);
if (v_isSharedCheck_5218_ == 0)
{
v___x_5213_ = v___x_5195_;
v_isShared_5214_ = v_isSharedCheck_5218_;
goto v_resetjp_5212_;
}
else
{
lean_inc(v_a_5211_);
lean_dec(v___x_5195_);
v___x_5213_ = lean_box(0);
v_isShared_5214_ = v_isSharedCheck_5218_;
goto v_resetjp_5212_;
}
v_resetjp_5212_:
{
lean_object* v___x_5216_; 
if (v_isShared_5214_ == 0)
{
v___x_5216_ = v___x_5213_;
goto v_reusejp_5215_;
}
else
{
lean_object* v_reuseFailAlloc_5217_; 
v_reuseFailAlloc_5217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5217_, 0, v_a_5211_);
v___x_5216_ = v_reuseFailAlloc_5217_;
goto v_reusejp_5215_;
}
v_reusejp_5215_:
{
return v___x_5216_;
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
v___jp_4967_:
{
size_t v___x_4969_; size_t v___x_4970_; 
v___x_4969_ = ((size_t)1ULL);
v___x_4970_ = lean_usize_add(v_i_4964_, v___x_4969_);
v_i_4964_ = v___x_4970_;
v_b_4965_ = v_a_4968_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___boxed(lean_object* v___x_5298_, lean_object* v_checkImports_5299_, lean_object* v_args_5300_, lean_object* v___x_5301_, lean_object* v_as_5302_, lean_object* v_sz_5303_, lean_object* v_i_5304_, lean_object* v_b_5305_, lean_object* v___y_5306_){
_start:
{
size_t v_sz_boxed_5307_; size_t v_i_boxed_5308_; lean_object* v_res_5309_; 
v_sz_boxed_5307_ = lean_unbox_usize(v_sz_5303_);
lean_dec(v_sz_5303_);
v_i_boxed_5308_ = lean_unbox_usize(v_i_5304_);
lean_dec(v_i_5304_);
v_res_5309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(v___x_5298_, v_checkImports_5299_, v_args_5300_, v___x_5301_, v_as_5302_, v_sz_boxed_5307_, v_i_boxed_5308_, v_b_5305_);
lean_dec_ref(v_as_5302_);
lean_dec_ref(v_args_5300_);
lean_dec_ref(v_checkImports_5299_);
lean_dec(v___x_5298_);
return v_res_5309_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__0(void){
_start:
{
lean_object* v___x_5310_; lean_object* v___x_5311_; 
v___x_5310_ = l_Lean_NameSet_empty;
v___x_5311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5311_, 0, v___x_5310_);
lean_ctor_set(v___x_5311_, 1, v___x_5310_);
return v___x_5311_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__1(void){
_start:
{
lean_object* v___x_5312_; lean_object* v___x_5313_; lean_object* v___x_5314_; 
v___x_5312_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__0, &l_Lake_BuiltinLint_run___closed__0_once, _init_l_Lake_BuiltinLint_run___closed__0);
v___x_5313_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_5314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5314_, 0, v___x_5313_);
lean_ctor_set(v___x_5314_, 1, v___x_5312_);
return v___x_5314_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__2(void){
_start:
{
lean_object* v___x_5315_; lean_object* v___x_5316_; lean_object* v___x_5317_; 
v___x_5315_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__1, &l_Lake_BuiltinLint_run___closed__1_once, _init_l_Lake_BuiltinLint_run___closed__1);
v___x_5316_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_5317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5317_, 0, v___x_5316_);
lean_ctor_set(v___x_5317_, 1, v___x_5315_);
return v___x_5317_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__1(void){
_start:
{
uint32_t v___x_5319_; lean_object* v___x_5320_; 
v___x_5319_ = 0;
v___x_5320_ = lean_box_uint32(v___x_5319_);
return v___x_5320_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__2(void){
_start:
{
uint32_t v___x_5321_; lean_object* v___x_5322_; 
v___x_5321_ = 1;
v___x_5322_ = lean_box_uint32(v___x_5321_);
return v___x_5322_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run(lean_object* v_args_5323_){
_start:
{
lean_object* v_mods_5325_; uint8_t v_mode_5326_; lean_object* v_checks_5327_; lean_object* v_srcSearchPath_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; uint8_t v_anyFailed_5331_; 
v_mods_5325_ = lean_ctor_get(v_args_5323_, 1);
lean_inc_ref(v_mods_5325_);
v_mode_5326_ = lean_ctor_get_uint8(v_args_5323_, sizeof(void*)*4 + 1);
v_checks_5327_ = lean_ctor_get(v_args_5323_, 2);
v_srcSearchPath_5328_ = lean_ctor_get(v_args_5323_, 3);
v___x_5329_ = lean_array_get_size(v_mods_5325_);
v___x_5330_ = lean_unsigned_to_nat(0u);
v_anyFailed_5331_ = lean_nat_dec_eq(v___x_5329_, v___x_5330_);
if (v_anyFailed_5331_ == 0)
{
size_t v_sz_5332_; size_t v___x_5333_; lean_object* v_checkImports_5334_; lean_object* v___x_5335_; 
v_sz_5332_ = lean_array_size(v_checks_5327_);
v___x_5333_ = ((size_t)0ULL);
lean_inc_ref(v_checks_5327_);
v_checkImports_5334_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(v___x_5329_, v_sz_5332_, v___x_5333_, v_checks_5327_);
v___x_5335_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_5335_) == 0)
{
lean_object* v_a_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; lean_object* v___x_5339_; lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; size_t v_sz_5343_; lean_object* v___x_5344_; 
v_a_5336_ = lean_ctor_get(v___x_5335_, 0);
lean_inc(v_a_5336_);
lean_dec_ref_known(v___x_5335_, 1);
lean_inc(v_srcSearchPath_5328_);
v___x_5337_ = l_List_appendTR___redArg(v_srcSearchPath_5328_, v_a_5336_);
v___x_5338_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__2, &l_Lake_BuiltinLint_run___closed__2_once, _init_l_Lake_BuiltinLint_run___closed__2);
v___x_5339_ = lean_box(v_anyFailed_5331_);
v___x_5340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5340_, 0, v___x_5339_);
lean_ctor_set(v___x_5340_, 1, v___x_5338_);
v___x_5341_ = lean_box(v_anyFailed_5331_);
v___x_5342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5342_, 0, v___x_5341_);
lean_ctor_set(v___x_5342_, 1, v___x_5340_);
v_sz_5343_ = lean_array_size(v_mods_5325_);
v___x_5344_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(v___x_5329_, v_checkImports_5334_, v_args_5323_, v___x_5337_, v_mods_5325_, v_sz_5343_, v___x_5333_, v___x_5342_);
lean_dec_ref(v_mods_5325_);
lean_dec_ref(v_args_5323_);
lean_dec_ref(v_checkImports_5334_);
if (lean_obj_tag(v___x_5344_) == 0)
{
lean_object* v_a_5345_; lean_object* v___x_5347_; uint8_t v_isShared_5348_; uint8_t v_isSharedCheck_5416_; 
v_a_5345_ = lean_ctor_get(v___x_5344_, 0);
v_isSharedCheck_5416_ = !lean_is_exclusive(v___x_5344_);
if (v_isSharedCheck_5416_ == 0)
{
v___x_5347_ = v___x_5344_;
v_isShared_5348_ = v_isSharedCheck_5416_;
goto v_resetjp_5346_;
}
else
{
lean_inc(v_a_5345_);
lean_dec(v___x_5344_);
v___x_5347_ = lean_box(0);
v_isShared_5348_ = v_isSharedCheck_5416_;
goto v_resetjp_5346_;
}
v_resetjp_5346_:
{
switch(v_mode_5326_)
{
case 0:
{
lean_object* v_fst_5349_; uint8_t v___x_5350_; 
v_fst_5349_ = lean_ctor_get(v_a_5345_, 0);
lean_inc(v_fst_5349_);
lean_dec(v_a_5345_);
v___x_5350_ = lean_unbox(v_fst_5349_);
lean_dec(v_fst_5349_);
if (v___x_5350_ == 0)
{
lean_object* v___x_5351_; lean_object* v___x_5353_; 
v___x_5351_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5348_ == 0)
{
lean_ctor_set(v___x_5347_, 0, v___x_5351_);
v___x_5353_ = v___x_5347_;
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
else
{
lean_object* v___x_5355_; lean_object* v___x_5357_; 
v___x_5355_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5348_ == 0)
{
lean_ctor_set(v___x_5347_, 0, v___x_5355_);
v___x_5357_ = v___x_5347_;
goto v_reusejp_5356_;
}
else
{
lean_object* v_reuseFailAlloc_5358_; 
v_reuseFailAlloc_5358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5358_, 0, v___x_5355_);
v___x_5357_ = v_reuseFailAlloc_5358_;
goto v_reusejp_5356_;
}
v_reusejp_5356_:
{
return v___x_5357_;
}
}
}
case 1:
{
lean_object* v_snd_5359_; lean_object* v_snd_5360_; lean_object* v_fst_5361_; lean_object* v_fst_5362_; lean_object* v___x_5363_; 
v_snd_5359_ = lean_ctor_get(v_a_5345_, 1);
lean_inc(v_snd_5359_);
lean_del_object(v___x_5347_);
lean_dec(v_a_5345_);
v_snd_5360_ = lean_ctor_get(v_snd_5359_, 1);
lean_inc(v_snd_5360_);
v_fst_5361_ = lean_ctor_get(v_snd_5359_, 0);
lean_inc(v_fst_5361_);
lean_dec(v_snd_5359_);
v_fst_5362_ = lean_ctor_get(v_snd_5360_, 0);
lean_inc(v_fst_5362_);
lean_dec(v_snd_5360_);
v___x_5363_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(v_fst_5362_);
lean_dec(v_fst_5362_);
if (lean_obj_tag(v___x_5363_) == 0)
{
lean_object* v___x_5365_; uint8_t v_isShared_5366_; uint8_t v_isSharedCheck_5376_; 
v_isSharedCheck_5376_ = !lean_is_exclusive(v___x_5363_);
if (v_isSharedCheck_5376_ == 0)
{
lean_object* v_unused_5377_; 
v_unused_5377_ = lean_ctor_get(v___x_5363_, 0);
lean_dec(v_unused_5377_);
v___x_5365_ = v___x_5363_;
v_isShared_5366_ = v_isSharedCheck_5376_;
goto v_resetjp_5364_;
}
else
{
lean_dec(v___x_5363_);
v___x_5365_ = lean_box(0);
v_isShared_5366_ = v_isSharedCheck_5376_;
goto v_resetjp_5364_;
}
v_resetjp_5364_:
{
uint8_t v___x_5367_; 
v___x_5367_ = lean_unbox(v_fst_5361_);
lean_dec(v_fst_5361_);
if (v___x_5367_ == 0)
{
lean_object* v___x_5368_; lean_object* v___x_5370_; 
v___x_5368_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5366_ == 0)
{
lean_ctor_set(v___x_5365_, 0, v___x_5368_);
v___x_5370_ = v___x_5365_;
goto v_reusejp_5369_;
}
else
{
lean_object* v_reuseFailAlloc_5371_; 
v_reuseFailAlloc_5371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5371_, 0, v___x_5368_);
v___x_5370_ = v_reuseFailAlloc_5371_;
goto v_reusejp_5369_;
}
v_reusejp_5369_:
{
return v___x_5370_;
}
}
else
{
lean_object* v___x_5372_; lean_object* v___x_5374_; 
v___x_5372_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5366_ == 0)
{
lean_ctor_set(v___x_5365_, 0, v___x_5372_);
v___x_5374_ = v___x_5365_;
goto v_reusejp_5373_;
}
else
{
lean_object* v_reuseFailAlloc_5375_; 
v_reuseFailAlloc_5375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5375_, 0, v___x_5372_);
v___x_5374_ = v_reuseFailAlloc_5375_;
goto v_reusejp_5373_;
}
v_reusejp_5373_:
{
return v___x_5374_;
}
}
}
}
else
{
lean_object* v_a_5378_; lean_object* v___x_5380_; uint8_t v_isShared_5381_; uint8_t v_isSharedCheck_5385_; 
lean_dec(v_fst_5361_);
v_a_5378_ = lean_ctor_get(v___x_5363_, 0);
v_isSharedCheck_5385_ = !lean_is_exclusive(v___x_5363_);
if (v_isSharedCheck_5385_ == 0)
{
v___x_5380_ = v___x_5363_;
v_isShared_5381_ = v_isSharedCheck_5385_;
goto v_resetjp_5379_;
}
else
{
lean_inc(v_a_5378_);
lean_dec(v___x_5363_);
v___x_5380_ = lean_box(0);
v_isShared_5381_ = v_isSharedCheck_5385_;
goto v_resetjp_5379_;
}
v_resetjp_5379_:
{
lean_object* v___x_5383_; 
if (v_isShared_5381_ == 0)
{
v___x_5383_ = v___x_5380_;
goto v_reusejp_5382_;
}
else
{
lean_object* v_reuseFailAlloc_5384_; 
v_reuseFailAlloc_5384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5384_, 0, v_a_5378_);
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
default: 
{
lean_object* v_snd_5386_; lean_object* v_snd_5387_; lean_object* v_snd_5388_; lean_object* v_fst_5389_; lean_object* v_fst_5390_; lean_object* v___x_5391_; size_t v_sz_5392_; lean_object* v___x_5393_; 
v_snd_5386_ = lean_ctor_get(v_a_5345_, 1);
lean_del_object(v___x_5347_);
v_snd_5387_ = lean_ctor_get(v_snd_5386_, 1);
v_snd_5388_ = lean_ctor_get(v_snd_5387_, 1);
lean_inc(v_snd_5388_);
v_fst_5389_ = lean_ctor_get(v_a_5345_, 0);
lean_inc(v_fst_5389_);
lean_dec(v_a_5345_);
v_fst_5390_ = lean_ctor_get(v_snd_5388_, 0);
lean_inc(v_fst_5390_);
lean_dec(v_snd_5388_);
v___x_5391_ = lean_box(0);
v_sz_5392_ = lean_array_size(v_fst_5390_);
v___x_5393_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(v_fst_5390_, v_sz_5392_, v___x_5333_, v___x_5391_);
lean_dec(v_fst_5390_);
if (lean_obj_tag(v___x_5393_) == 0)
{
lean_object* v___x_5395_; uint8_t v_isShared_5396_; uint8_t v_isSharedCheck_5406_; 
v_isSharedCheck_5406_ = !lean_is_exclusive(v___x_5393_);
if (v_isSharedCheck_5406_ == 0)
{
lean_object* v_unused_5407_; 
v_unused_5407_ = lean_ctor_get(v___x_5393_, 0);
lean_dec(v_unused_5407_);
v___x_5395_ = v___x_5393_;
v_isShared_5396_ = v_isSharedCheck_5406_;
goto v_resetjp_5394_;
}
else
{
lean_dec(v___x_5393_);
v___x_5395_ = lean_box(0);
v_isShared_5396_ = v_isSharedCheck_5406_;
goto v_resetjp_5394_;
}
v_resetjp_5394_:
{
uint8_t v___x_5397_; 
v___x_5397_ = lean_unbox(v_fst_5389_);
lean_dec(v_fst_5389_);
if (v___x_5397_ == 0)
{
lean_object* v___x_5398_; lean_object* v___x_5400_; 
v___x_5398_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5396_ == 0)
{
lean_ctor_set(v___x_5395_, 0, v___x_5398_);
v___x_5400_ = v___x_5395_;
goto v_reusejp_5399_;
}
else
{
lean_object* v_reuseFailAlloc_5401_; 
v_reuseFailAlloc_5401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5401_, 0, v___x_5398_);
v___x_5400_ = v_reuseFailAlloc_5401_;
goto v_reusejp_5399_;
}
v_reusejp_5399_:
{
return v___x_5400_;
}
}
else
{
lean_object* v___x_5402_; lean_object* v___x_5404_; 
v___x_5402_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5396_ == 0)
{
lean_ctor_set(v___x_5395_, 0, v___x_5402_);
v___x_5404_ = v___x_5395_;
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
}
else
{
lean_object* v_a_5408_; lean_object* v___x_5410_; uint8_t v_isShared_5411_; uint8_t v_isSharedCheck_5415_; 
lean_dec(v_fst_5389_);
v_a_5408_ = lean_ctor_get(v___x_5393_, 0);
v_isSharedCheck_5415_ = !lean_is_exclusive(v___x_5393_);
if (v_isSharedCheck_5415_ == 0)
{
v___x_5410_ = v___x_5393_;
v_isShared_5411_ = v_isSharedCheck_5415_;
goto v_resetjp_5409_;
}
else
{
lean_inc(v_a_5408_);
lean_dec(v___x_5393_);
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
}
else
{
lean_object* v_a_5417_; lean_object* v___x_5419_; uint8_t v_isShared_5420_; uint8_t v_isSharedCheck_5424_; 
v_a_5417_ = lean_ctor_get(v___x_5344_, 0);
v_isSharedCheck_5424_ = !lean_is_exclusive(v___x_5344_);
if (v_isSharedCheck_5424_ == 0)
{
v___x_5419_ = v___x_5344_;
v_isShared_5420_ = v_isSharedCheck_5424_;
goto v_resetjp_5418_;
}
else
{
lean_inc(v_a_5417_);
lean_dec(v___x_5344_);
v___x_5419_ = lean_box(0);
v_isShared_5420_ = v_isSharedCheck_5424_;
goto v_resetjp_5418_;
}
v_resetjp_5418_:
{
lean_object* v___x_5422_; 
if (v_isShared_5420_ == 0)
{
v___x_5422_ = v___x_5419_;
goto v_reusejp_5421_;
}
else
{
lean_object* v_reuseFailAlloc_5423_; 
v_reuseFailAlloc_5423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5423_, 0, v_a_5417_);
v___x_5422_ = v_reuseFailAlloc_5423_;
goto v_reusejp_5421_;
}
v_reusejp_5421_:
{
return v___x_5422_;
}
}
}
}
else
{
lean_object* v_a_5425_; lean_object* v___x_5427_; uint8_t v_isShared_5428_; uint8_t v_isSharedCheck_5432_; 
lean_dec_ref(v_checkImports_5334_);
lean_dec_ref(v_mods_5325_);
lean_dec_ref(v_args_5323_);
v_a_5425_ = lean_ctor_get(v___x_5335_, 0);
v_isSharedCheck_5432_ = !lean_is_exclusive(v___x_5335_);
if (v_isSharedCheck_5432_ == 0)
{
v___x_5427_ = v___x_5335_;
v_isShared_5428_ = v_isSharedCheck_5432_;
goto v_resetjp_5426_;
}
else
{
lean_inc(v_a_5425_);
lean_dec(v___x_5335_);
v___x_5427_ = lean_box(0);
v_isShared_5428_ = v_isSharedCheck_5432_;
goto v_resetjp_5426_;
}
v_resetjp_5426_:
{
lean_object* v___x_5430_; 
if (v_isShared_5428_ == 0)
{
v___x_5430_ = v___x_5427_;
goto v_reusejp_5429_;
}
else
{
lean_object* v_reuseFailAlloc_5431_; 
v_reuseFailAlloc_5431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5431_, 0, v_a_5425_);
v___x_5430_ = v_reuseFailAlloc_5431_;
goto v_reusejp_5429_;
}
v_reusejp_5429_:
{
return v___x_5430_;
}
}
}
}
else
{
lean_object* v___x_5433_; lean_object* v___x_5434_; 
lean_dec_ref(v_mods_5325_);
lean_dec_ref(v_args_5323_);
v___x_5433_ = ((lean_object*)(l_Lake_BuiltinLint_run___closed__3));
v___x_5434_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_5433_);
if (lean_obj_tag(v___x_5434_) == 0)
{
lean_object* v___x_5436_; uint8_t v_isShared_5437_; uint8_t v_isSharedCheck_5442_; 
v_isSharedCheck_5442_ = !lean_is_exclusive(v___x_5434_);
if (v_isSharedCheck_5442_ == 0)
{
lean_object* v_unused_5443_; 
v_unused_5443_ = lean_ctor_get(v___x_5434_, 0);
lean_dec(v_unused_5443_);
v___x_5436_ = v___x_5434_;
v_isShared_5437_ = v_isSharedCheck_5442_;
goto v_resetjp_5435_;
}
else
{
lean_dec(v___x_5434_);
v___x_5436_ = lean_box(0);
v_isShared_5437_ = v_isSharedCheck_5442_;
goto v_resetjp_5435_;
}
v_resetjp_5435_:
{
lean_object* v___x_5438_; lean_object* v___x_5440_; 
v___x_5438_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5437_ == 0)
{
lean_ctor_set(v___x_5436_, 0, v___x_5438_);
v___x_5440_ = v___x_5436_;
goto v_reusejp_5439_;
}
else
{
lean_object* v_reuseFailAlloc_5441_; 
v_reuseFailAlloc_5441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5441_, 0, v___x_5438_);
v___x_5440_ = v_reuseFailAlloc_5441_;
goto v_reusejp_5439_;
}
v_reusejp_5439_:
{
return v___x_5440_;
}
}
}
else
{
lean_object* v_a_5444_; lean_object* v___x_5446_; uint8_t v_isShared_5447_; uint8_t v_isSharedCheck_5451_; 
v_a_5444_ = lean_ctor_get(v___x_5434_, 0);
v_isSharedCheck_5451_ = !lean_is_exclusive(v___x_5434_);
if (v_isSharedCheck_5451_ == 0)
{
v___x_5446_ = v___x_5434_;
v_isShared_5447_ = v_isSharedCheck_5451_;
goto v_resetjp_5445_;
}
else
{
lean_inc(v_a_5444_);
lean_dec(v___x_5434_);
v___x_5446_ = lean_box(0);
v_isShared_5447_ = v_isSharedCheck_5451_;
goto v_resetjp_5445_;
}
v_resetjp_5445_:
{
lean_object* v___x_5449_; 
if (v_isShared_5447_ == 0)
{
v___x_5449_ = v___x_5446_;
goto v_reusejp_5448_;
}
else
{
lean_object* v_reuseFailAlloc_5450_; 
v_reuseFailAlloc_5450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5450_, 0, v_a_5444_);
v___x_5449_ = v_reuseFailAlloc_5450_;
goto v_reusejp_5448_;
}
v_reusejp_5448_:
{
return v___x_5449_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed(lean_object* v_args_5452_, lean_object* v_a_5453_){
_start:
{
lean_object* v_res_5454_; 
v_res_5454_ = l_Lake_BuiltinLint_run(v_args_5452_);
return v_res_5454_;
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
