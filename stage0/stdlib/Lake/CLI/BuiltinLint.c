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
lean_object* l_Lake_BuiltinLint_Mode_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Lake_BuiltinLint_Mode_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Lake_BuiltinLint_Mode_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lake_BuiltinLint_Mode_ctorIdx___impl(v_x_4__boxed_6_);
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
lean_object* l_Lake_BuiltinLint_Mode_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Lake_BuiltinLint_Mode_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Lake_BuiltinLint_Mode_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Lake_BuiltinLint_Mode_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_report_elim___redArg(lean_object* v_report_24_){
_start:
{
lean_inc(v_report_24_);
return v_report_24_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_report_elim___redArg___boxed(lean_object* v_report_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lake_BuiltinLint_Mode_report_elim___redArg(v_report_25_);
lean_dec(v_report_25_);
return v_res_26_;
}
}
lean_object* l_Lake_BuiltinLint_Mode_report_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_report_30_){
_start:
{
lean_inc(v_report_30_);
return v_report_30_;
}
}
LEAN_EXPORT void l_Lake_BuiltinLint_Mode_report_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_report_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Lake_BuiltinLint_Mode_report_elim(lean_box(0), v_t_28_, lean_box(0), v_report_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_report_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_report_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Lake_BuiltinLint_Mode_report_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_report_35_);
lean_dec(v_report_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_recordExceptions_elim___redArg(lean_object* v_recordExceptions_38_){
_start:
{
lean_inc(v_recordExceptions_38_);
return v_recordExceptions_38_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_recordExceptions_elim___redArg___boxed(lean_object* v_recordExceptions_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lake_BuiltinLint_Mode_recordExceptions_elim___redArg(v_recordExceptions_39_);
lean_dec(v_recordExceptions_39_);
return v_res_40_;
}
}
lean_object* l_Lake_BuiltinLint_Mode_recordExceptions_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_recordExceptions_44_){
_start:
{
lean_inc(v_recordExceptions_44_);
return v_recordExceptions_44_;
}
}
LEAN_EXPORT void l_Lake_BuiltinLint_Mode_recordExceptions_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_recordExceptions_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lake_BuiltinLint_Mode_recordExceptions_elim(lean_box(0), v_t_42_, lean_box(0), v_recordExceptions_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_recordExceptions_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_recordExceptions_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Lake_BuiltinLint_Mode_recordExceptions_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_recordExceptions_49_);
lean_dec(v_recordExceptions_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_codeQuality_elim___redArg(lean_object* v_codeQuality_52_){
_start:
{
lean_inc(v_codeQuality_52_);
return v_codeQuality_52_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_codeQuality_elim___redArg___boxed(lean_object* v_codeQuality_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lake_BuiltinLint_Mode_codeQuality_elim___redArg(v_codeQuality_53_);
lean_dec(v_codeQuality_53_);
return v_res_54_;
}
}
lean_object* l_Lake_BuiltinLint_Mode_codeQuality_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_codeQuality_58_){
_start:
{
lean_inc(v_codeQuality_58_);
return v_codeQuality_58_;
}
}
LEAN_EXPORT void l_Lake_BuiltinLint_Mode_codeQuality_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_codeQuality_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Lake_BuiltinLint_Mode_codeQuality_elim(lean_box(0), v_t_56_, lean_box(0), v_codeQuality_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_codeQuality_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_codeQuality_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l_Lake_BuiltinLint_Mode_codeQuality_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_codeQuality_63_);
lean_dec(v_codeQuality_63_);
return v_res_65_;
}
}
uint8_t l_Lake_BuiltinLint_instBEqMode_beq(uint8_t v_x_66_, uint8_t v_y_67_){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; uint8_t v___x_72_; 
v___x_68_ = lean_box(v_x_66_);
v___x_69_ = lean_obj_tag_nat(v___x_68_);
lean_dec(v___x_68_);
v___x_70_ = lean_box(v_y_67_);
v___x_71_ = lean_obj_tag_nat(v___x_70_);
lean_dec(v___x_70_);
v___x_72_ = lean_nat_dec_eq(v___x_69_, v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT void l_Lake_BuiltinLint_instBEqMode_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_66_ = stack[0].m_num;
uint8_t v_y_67_ = stack[1].m_num;
uint8_t v_res_73_;
v_res_73_ = l_Lake_BuiltinLint_instBEqMode_beq(v_x_66_, v_y_67_);
stack->m_num = v_res_73_;
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_instBEqMode_beq___boxed(lean_object* v_x_74_, lean_object* v_y_75_){
_start:
{
uint8_t v_x_24__boxed_76_; uint8_t v_y_25__boxed_77_; uint8_t v_res_78_; lean_object* v_r_79_; 
v_x_24__boxed_76_ = lean_unbox(v_x_74_);
v_y_25__boxed_77_ = lean_unbox(v_y_75_);
v_res_78_ = l_Lake_BuiltinLint_instBEqMode_beq(v_x_24__boxed_76_, v_y_25__boxed_77_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1(size_t v_sz_85_, size_t v_i_86_, lean_object* v_bs_87_){
_start:
{
uint8_t v___x_88_; 
v___x_88_ = lean_usize_dec_lt(v_i_86_, v_sz_85_);
if (v___x_88_ == 0)
{
return v_bs_87_;
}
else
{
lean_object* v_v_89_; lean_object* v_fst_90_; lean_object* v_snd_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_108_; 
v_v_89_ = lean_array_uget(v_bs_87_, v_i_86_);
v_fst_90_ = lean_ctor_get(v_v_89_, 0);
v_snd_91_ = lean_ctor_get(v_v_89_, 1);
v_isSharedCheck_108_ = !lean_is_exclusive(v_v_89_);
if (v_isSharedCheck_108_ == 0)
{
v___x_93_ = v_v_89_;
v_isShared_94_ = v_isSharedCheck_108_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_snd_91_);
lean_inc(v_fst_90_);
lean_dec(v_v_89_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_108_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_95_; lean_object* v_bs_x27_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; uint8_t v___x_100_; lean_object* v___x_102_; 
v___x_95_ = lean_unsigned_to_nat(0u);
v_bs_x27_96_ = lean_array_uset(v_bs_87_, v_i_86_, v___x_95_);
v___x_97_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1___closed__1));
v___x_98_ = l_Lean_Name_append(v___x_97_, v_fst_90_);
v___x_99_ = lean_alloc_ctor(1, 0, 1);
v___x_100_ = lean_unbox(v_snd_91_);
lean_dec(v_snd_91_);
lean_ctor_set_uint8(v___x_99_, 0, v___x_100_);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 1, v___x_99_);
lean_ctor_set(v___x_93_, 0, v___x_98_);
v___x_102_ = v___x_93_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_98_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v___x_99_);
v___x_102_ = v_reuseFailAlloc_107_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
size_t v___x_103_; size_t v___x_104_; lean_object* v___x_105_; 
v___x_103_ = ((size_t)1ULL);
v___x_104_ = lean_usize_add(v_i_86_, v___x_103_);
v___x_105_ = lean_array_uset(v_bs_x27_96_, v_i_86_, v___x_102_);
v_i_86_ = v___x_104_;
v_bs_87_ = v___x_105_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_85_ = stack[0].m_num;
size_t v_i_86_ = stack[1].m_num;
lean_object* v_bs_87_ = stack[2].m_obj;
lean_object* v_res_109_;
v_res_109_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1(v_sz_85_, v_i_86_, v_bs_87_);
stack->m_obj
 = v_res_109_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1___boxed(lean_object* v_sz_110_, lean_object* v_i_111_, lean_object* v_bs_112_){
_start:
{
size_t v_sz_boxed_113_; size_t v_i_boxed_114_; lean_object* v_res_115_; 
v_sz_boxed_113_ = lean_unbox_usize(v_sz_110_);
lean_dec(v_sz_110_);
v_i_boxed_114_ = lean_unbox_usize(v_i_111_);
lean_dec(v_i_111_);
v_res_115_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1(v_sz_boxed_113_, v_i_boxed_114_, v_bs_112_);
return v_res_115_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_leanOptOverrides_spec__2(lean_object* v_as_116_, size_t v_i_117_, size_t v_stop_118_, lean_object* v_b_119_){
_start:
{
uint8_t v___x_120_; 
v___x_120_ = lean_usize_dec_eq(v_i_117_, v_stop_118_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; lean_object* v_fst_122_; lean_object* v_snd_123_; lean_object* v___x_124_; size_t v___x_125_; size_t v___x_126_; 
v___x_121_ = lean_array_uget_borrowed(v_as_116_, v_i_117_);
v_fst_122_ = lean_ctor_get(v___x_121_, 0);
v_snd_123_ = lean_ctor_get(v___x_121_, 1);
lean_inc(v_snd_123_);
lean_inc(v_fst_122_);
v___x_124_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_122_, v_snd_123_, v_b_119_);
v___x_125_ = ((size_t)1ULL);
v___x_126_ = lean_usize_add(v_i_117_, v___x_125_);
v_i_117_ = v___x_126_;
v_b_119_ = v___x_124_;
goto _start;
}
else
{
return v_b_119_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_leanOptOverrides_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_116_ = stack[0].m_obj;
size_t v_i_117_ = stack[1].m_num;
size_t v_stop_118_ = stack[2].m_num;
lean_object* v_b_119_ = stack[3].m_obj;
lean_object* v_res_128_;
v_res_128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_leanOptOverrides_spec__2(v_as_116_, v_i_117_, v_stop_118_, v_b_119_);
stack->m_obj
 = v_res_128_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_leanOptOverrides_spec__2___boxed(lean_object* v_as_129_, lean_object* v_i_130_, lean_object* v_stop_131_, lean_object* v_b_132_){
_start:
{
size_t v_i_boxed_133_; size_t v_stop_boxed_134_; lean_object* v_res_135_; 
v_i_boxed_133_ = lean_unbox_usize(v_i_130_);
lean_dec(v_i_130_);
v_stop_boxed_134_ = lean_unbox_usize(v_stop_131_);
lean_dec(v_stop_131_);
v_res_135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_leanOptOverrides_spec__2(v_as_129_, v_i_boxed_133_, v_stop_boxed_134_, v_b_132_);
lean_dec_ref(v_as_129_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0(lean_object* v_init_136_, lean_object* v_x_137_){
_start:
{
if (lean_obj_tag(v_x_137_) == 0)
{
lean_object* v_k_138_; lean_object* v_v_139_; lean_object* v_l_140_; lean_object* v_r_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v_k_138_ = lean_ctor_get(v_x_137_, 1);
v_v_139_ = lean_ctor_get(v_x_137_, 2);
v_l_140_ = lean_ctor_get(v_x_137_, 3);
v_r_141_ = lean_ctor_get(v_x_137_, 4);
v___x_142_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0(v_init_136_, v_l_140_);
lean_inc(v_v_139_);
lean_inc(v_k_138_);
v___x_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_143_, 0, v_k_138_);
lean_ctor_set(v___x_143_, 1, v_v_139_);
v___x_144_ = lean_array_push(v___x_142_, v___x_143_);
v_init_136_ = v___x_144_;
v_x_137_ = v_r_141_;
goto _start;
}
else
{
return v_init_136_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0___boxed(lean_object* v_init_146_, lean_object* v_x_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0(v_init_146_, v_x_147_);
lean_dec(v_x_147_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_leanOptOverrides(lean_object* v_args_161_){
_start:
{
lean_object* v_linterOverrides_162_; uint8_t v_mode_163_; lean_object* v___y_165_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v_linterOverrides_162_ = lean_ctor_get(v_args_161_, 0);
v_mode_163_ = lean_ctor_get_uint8(v_args_161_, sizeof(void*)*4 + 1);
v___x_177_ = lean_box(1);
v___x_178_ = lean_unsigned_to_nat(0u);
v___x_179_ = lean_array_get_size(v_linterOverrides_162_);
v___x_180_ = lean_nat_dec_lt(v___x_178_, v___x_179_);
if (v___x_180_ == 0)
{
v___y_165_ = v___x_177_;
goto v___jp_164_;
}
else
{
uint8_t v___x_181_; 
v___x_181_ = lean_nat_dec_le(v___x_179_, v___x_179_);
if (v___x_181_ == 0)
{
if (v___x_180_ == 0)
{
v___y_165_ = v___x_177_;
goto v___jp_164_;
}
else
{
size_t v___x_182_; size_t v___x_183_; lean_object* v___x_184_; 
v___x_182_ = ((size_t)0ULL);
v___x_183_ = lean_usize_of_nat(v___x_179_);
v___x_184_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_leanOptOverrides_spec__2(v_linterOverrides_162_, v___x_182_, v___x_183_, v___x_177_);
v___y_165_ = v___x_184_;
goto v___jp_164_;
}
}
else
{
size_t v___x_185_; size_t v___x_186_; lean_object* v___x_187_; 
v___x_185_ = ((size_t)0ULL);
v___x_186_ = lean_usize_of_nat(v___x_179_);
v___x_187_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_leanOptOverrides_spec__2(v_linterOverrides_162_, v___x_185_, v___x_186_, v___x_177_);
v___y_165_ = v___x_187_;
goto v___jp_164_;
}
}
v___jp_164_:
{
lean_object* v___x_166_; lean_object* v___x_167_; size_t v_sz_168_; size_t v___x_169_; lean_object* v_base_170_; uint8_t v___x_171_; uint8_t v___x_172_; 
v___x_166_ = ((lean_object*)(l_Lake_BuiltinLint_leanOptOverrides___closed__0));
v___x_167_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0(v___x_166_, v___y_165_);
lean_dec(v___y_165_);
v_sz_168_ = lean_array_size(v___x_167_);
v___x_169_ = ((size_t)0ULL);
v_base_170_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1(v_sz_168_, v___x_169_, v___x_167_);
v___x_171_ = 1;
v___x_172_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_163_, v___x_171_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; 
v___x_173_ = l_Lean_LeanOptions_ofArray(v_base_170_);
lean_dec_ref(v_base_170_);
return v___x_173_;
}
else
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_174_ = ((lean_object*)(l_Lake_BuiltinLint_leanOptOverrides___closed__5));
v___x_175_ = lean_array_push(v_base_170_, v___x_174_);
v___x_176_ = l_Lean_LeanOptions_ofArray(v___x_175_);
lean_dec_ref(v___x_175_);
return v___x_176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_leanOptOverrides___boxed(lean_object* v_args_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lake_BuiltinLint_leanOptOverrides(v_args_188_);
lean_dec_ref(v_args_188_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0(lean_object* v_init_190_, lean_object* v_t_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0(v_init_190_, v_t_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0___boxed(lean_object* v_init_193_, lean_object* v_t_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0(v_init_193_, v_t_194_);
lean_dec(v_t_194_);
return v_res_195_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__1(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_197_ = lean_box(0);
v___x_198_ = l_Lean_instInhabitedPosition_default;
v___x_199_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_200_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
lean_ctor_set(v___x_200_, 1, v___x_198_);
lean_ctor_set(v___x_200_, 2, v___x_197_);
return v___x_200_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_instInhabitedExceptionRecord_default(void){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = lean_obj_once(&l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__1, &l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__1_once, _init_l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__1);
return v___x_201_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_instInhabitedExceptionRecord(void){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lake_BuiltinLint_instInhabitedExceptionRecord_default;
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorIdx___impl(lean_object* v_x_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = lean_obj_tag_nat(v_x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorIdx___impl___boxed(lean_object* v_x_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorIdx___impl(v_x_205_);
lean_dec_ref(v_x_205_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___redArg(lean_object* v_t_207_, lean_object* v_k_208_){
_start:
{
switch(lean_obj_tag(v_t_207_))
{
case 0:
{
uint8_t v_failed_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v_failed_209_ = lean_ctor_get_uint8(v_t_207_, 0);
lean_dec_ref_known(v_t_207_, 0);
v___x_210_ = lean_box(v_failed_209_);
v___x_211_ = lean_apply_1(v_k_208_, v___x_210_);
return v___x_211_;
}
case 1:
{
lean_object* v_records_212_; uint8_t v_unlocated_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v_records_212_ = lean_ctor_get(v_t_207_, 0);
lean_inc_ref(v_records_212_);
v_unlocated_213_ = lean_ctor_get_uint8(v_t_207_, sizeof(void*)*1);
lean_dec_ref_known(v_t_207_, 1);
v___x_214_ = lean_box(v_unlocated_213_);
v___x_215_ = lean_apply_2(v_k_208_, v_records_212_, v___x_214_);
return v___x_215_;
}
default: 
{
lean_object* v_entries_216_; lean_object* v___x_217_; 
v_entries_216_ = lean_ctor_get(v_t_207_, 0);
lean_inc_ref(v_entries_216_);
lean_dec_ref_known(v_t_207_, 1);
v___x_217_ = lean_apply_1(v_k_208_, v_entries_216_);
return v___x_217_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim(lean_object* v_motive_218_, lean_object* v_ctorIdx_219_, lean_object* v_t_220_, lean_object* v_h_221_, lean_object* v_k_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___redArg(v_t_220_, v_k_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___boxed(lean_object* v_motive_224_, lean_object* v_ctorIdx_225_, lean_object* v_t_226_, lean_object* v_h_227_, lean_object* v_k_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim(v_motive_224_, v_ctorIdx_225_, v_t_226_, v_h_227_, v_k_228_);
lean_dec(v_ctorIdx_225_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_reported_elim___redArg(lean_object* v_t_230_, lean_object* v_reported_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___redArg(v_t_230_, v_reported_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_reported_elim(lean_object* v_motive_233_, lean_object* v_t_234_, lean_object* v_h_235_, lean_object* v_reported_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___redArg(v_t_234_, v_reported_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_recorded_elim___redArg(lean_object* v_t_238_, lean_object* v_recorded_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___redArg(v_t_238_, v_recorded_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_recorded_elim(lean_object* v_motive_241_, lean_object* v_t_242_, lean_object* v_h_243_, lean_object* v_recorded_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___redArg(v_t_242_, v_recorded_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_codeQualityChecks_elim___redArg(lean_object* v_t_246_, lean_object* v_codeQualityChecks_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___redArg(v_t_246_, v_codeQualityChecks_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_codeQualityChecks_elim(lean_object* v_motive_249_, lean_object* v_t_250_, lean_object* v_h_251_, lean_object* v_codeQualityChecks_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___redArg(v_t_250_, v_codeQualityChecks_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorIdx___impl(lean_object* v_x_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = lean_obj_tag_nat(v_x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorIdx___impl___boxed(lean_object* v_x_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorIdx___impl(v_x_256_);
lean_dec_ref(v_x_256_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(lean_object* v_t_258_, lean_object* v_k_259_){
_start:
{
if (lean_obj_tag(v_t_258_) == 0)
{
uint8_t v_failed_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v_failed_260_ = lean_ctor_get_uint8(v_t_258_, 0);
lean_dec_ref_known(v_t_258_, 0);
v___x_261_ = lean_box(v_failed_260_);
v___x_262_ = lean_apply_1(v_k_259_, v___x_261_);
return v___x_262_;
}
else
{
lean_object* v_records_263_; uint8_t v_unlocated_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v_records_263_ = lean_ctor_get(v_t_258_, 0);
lean_inc_ref(v_records_263_);
v_unlocated_264_ = lean_ctor_get_uint8(v_t_258_, sizeof(void*)*1);
lean_dec_ref_known(v_t_258_, 1);
v___x_265_ = lean_box(v_unlocated_264_);
v___x_266_ = lean_apply_2(v_k_259_, v_records_263_, v___x_265_);
return v___x_266_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim(lean_object* v_motive_267_, lean_object* v_ctorIdx_268_, lean_object* v_t_269_, lean_object* v_h_270_, lean_object* v_k_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(v_t_269_, v_k_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___boxed(lean_object* v_motive_273_, lean_object* v_ctorIdx_274_, lean_object* v_t_275_, lean_object* v_h_276_, lean_object* v_k_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim(v_motive_273_, v_ctorIdx_274_, v_t_275_, v_h_276_, v_k_277_);
lean_dec(v_ctorIdx_274_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_reported_elim___redArg(lean_object* v_t_279_, lean_object* v_reported_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(v_t_279_, v_reported_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_reported_elim(lean_object* v_motive_282_, lean_object* v_t_283_, lean_object* v_h_284_, lean_object* v_reported_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(v_t_283_, v_reported_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_recorded_elim___redArg(lean_object* v_t_287_, lean_object* v_recorded_288_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(v_t_287_, v_recorded_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_recorded_elim(lean_object* v_motive_290_, lean_object* v_t_291_, lean_object* v_h_292_, lean_object* v_recorded_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(v_t_291_, v_recorded_293_);
return v___x_294_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(lean_object* v_pkgRoot_295_, lean_object* v_as_296_, size_t v_i_297_, size_t v_stop_298_, lean_object* v_b_299_){
_start:
{
lean_object* v___y_301_; uint8_t v___x_305_; 
v___x_305_ = lean_usize_dec_eq(v_i_297_, v_stop_298_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; uint8_t v___y_308_; lean_object* v_fst_310_; lean_object* v_snd_311_; uint8_t v___x_312_; 
v___x_306_ = lean_array_uget_borrowed(v_as_296_, v_i_297_);
v_fst_310_ = lean_ctor_get(v___x_306_, 0);
v_snd_311_ = lean_ctor_get(v___x_306_, 1);
v___x_312_ = l_Lean_Name_isPrefixOf(v_pkgRoot_295_, v_fst_310_);
if (v___x_312_ == 0)
{
v___y_308_ = v___x_312_;
goto v___jp_307_;
}
else
{
lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_313_ = lean_array_get_size(v_snd_311_);
v___x_314_ = lean_unsigned_to_nat(0u);
v___x_315_ = lean_nat_dec_eq(v___x_313_, v___x_314_);
if (v___x_315_ == 0)
{
v___y_308_ = v___x_312_;
goto v___jp_307_;
}
else
{
v___y_301_ = v_b_299_;
goto v___jp_300_;
}
}
v___jp_307_:
{
if (v___y_308_ == 0)
{
v___y_301_ = v_b_299_;
goto v___jp_300_;
}
else
{
lean_object* v___x_309_; 
lean_inc(v___x_306_);
v___x_309_ = lean_array_push(v_b_299_, v___x_306_);
v___y_301_ = v___x_309_;
goto v___jp_300_;
}
}
}
else
{
return v_b_299_;
}
v___jp_300_:
{
size_t v___x_302_; size_t v___x_303_; 
v___x_302_ = ((size_t)1ULL);
v___x_303_ = lean_usize_add(v_i_297_, v___x_302_);
v_i_297_ = v___x_303_;
v_b_299_ = v___y_301_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pkgRoot_295_ = stack[0].m_obj;
lean_object* v_as_296_ = stack[1].m_obj;
size_t v_i_297_ = stack[2].m_num;
size_t v_stop_298_ = stack[3].m_num;
lean_object* v_b_299_ = stack[4].m_obj;
lean_object* v_res_316_;
v_res_316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(v_pkgRoot_295_, v_as_296_, v_i_297_, v_stop_298_, v_b_299_);
stack->m_obj
 = v_res_316_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0___boxed(lean_object* v_pkgRoot_317_, lean_object* v_as_318_, lean_object* v_i_319_, lean_object* v_stop_320_, lean_object* v_b_321_){
_start:
{
size_t v_i_boxed_322_; size_t v_stop_boxed_323_; lean_object* v_res_324_; 
v_i_boxed_322_ = lean_unbox_usize(v_i_319_);
lean_dec(v_i_319_);
v_stop_boxed_323_ = lean_unbox_usize(v_stop_320_);
lean_dec(v_stop_320_);
v_res_324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(v_pkgRoot_317_, v_as_318_, v_i_boxed_322_, v_stop_boxed_323_, v_b_321_);
lean_dec_ref(v_as_318_);
lean_dec(v_pkgRoot_317_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(lean_object* v_env_327_, lean_object* v_pkgRoot_328_){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_329_ = lean_unsigned_to_nat(0u);
v___x_330_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0));
v___x_331_ = l_Lean_Linter_getAllLints(v_env_327_);
v___x_332_ = lean_array_get_size(v___x_331_);
v___x_333_ = lean_nat_dec_lt(v___x_329_, v___x_332_);
if (v___x_333_ == 0)
{
lean_dec_ref(v___x_331_);
return v___x_330_;
}
else
{
uint8_t v___x_334_; 
v___x_334_ = lean_nat_dec_le(v___x_332_, v___x_332_);
if (v___x_334_ == 0)
{
if (v___x_333_ == 0)
{
lean_dec_ref(v___x_331_);
return v___x_330_;
}
else
{
size_t v___x_335_; size_t v___x_336_; lean_object* v___x_337_; 
v___x_335_ = ((size_t)0ULL);
v___x_336_ = lean_usize_of_nat(v___x_332_);
v___x_337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(v_pkgRoot_328_, v___x_331_, v___x_335_, v___x_336_, v___x_330_);
lean_dec_ref(v___x_331_);
return v___x_337_;
}
}
else
{
size_t v___x_338_; size_t v___x_339_; lean_object* v___x_340_; 
v___x_338_ = ((size_t)0ULL);
v___x_339_ = lean_usize_of_nat(v___x_332_);
v___x_340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(v_pkgRoot_328_, v___x_331_, v___x_338_, v___x_339_, v___x_330_);
lean_dec_ref(v___x_331_);
return v___x_340_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___boxed(lean_object* v_env_341_, lean_object* v_pkgRoot_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(v_env_341_, v_pkgRoot_342_);
lean_dec(v_pkgRoot_342_);
lean_dec_ref(v_env_341_);
return v_res_343_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__0(size_t v_sz_344_, size_t v_i_345_, lean_object* v_bs_346_){
_start:
{
uint8_t v___x_347_; 
v___x_347_ = lean_usize_dec_lt(v_i_345_, v_sz_344_);
if (v___x_347_ == 0)
{
return v_bs_346_;
}
else
{
lean_object* v_v_348_; lean_object* v_entry_349_; lean_object* v___x_350_; lean_object* v_bs_x27_351_; size_t v___x_352_; size_t v___x_353_; lean_object* v___x_354_; 
v_v_348_ = lean_array_uget_borrowed(v_bs_346_, v_i_345_);
v_entry_349_ = lean_ctor_get(v_v_348_, 1);
lean_inc_ref(v_entry_349_);
v___x_350_ = lean_unsigned_to_nat(0u);
v_bs_x27_351_ = lean_array_uset(v_bs_346_, v_i_345_, v___x_350_);
v___x_352_ = ((size_t)1ULL);
v___x_353_ = lean_usize_add(v_i_345_, v___x_352_);
v___x_354_ = lean_array_uset(v_bs_x27_351_, v_i_345_, v_entry_349_);
v_i_345_ = v___x_353_;
v_bs_346_ = v___x_354_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_344_ = stack[0].m_num;
size_t v_i_345_ = stack[1].m_num;
lean_object* v_bs_346_ = stack[2].m_obj;
lean_object* v_res_356_;
v_res_356_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__0(v_sz_344_, v_i_345_, v_bs_346_);
stack->m_obj
 = v_res_356_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__0___boxed(lean_object* v_sz_357_, lean_object* v_i_358_, lean_object* v_bs_359_){
_start:
{
size_t v_sz_boxed_360_; size_t v_i_boxed_361_; lean_object* v_res_362_; 
v_sz_boxed_360_ = lean_unbox_usize(v_sz_357_);
lean_dec(v_sz_357_);
v_i_boxed_361_ = lean_unbox_usize(v_i_358_);
lean_dec(v_i_358_);
v_res_362_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__0(v_sz_boxed_360_, v_i_boxed_361_, v_bs_359_);
return v_res_362_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__1(lean_object* v_linterOpts_363_, lean_object* v_as_364_, size_t v_i_365_, size_t v_stop_366_, lean_object* v_b_367_){
_start:
{
lean_object* v___y_369_; uint8_t v___x_373_; 
v___x_373_ = lean_usize_dec_eq(v_i_365_, v_stop_366_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; lean_object* v_linter_x3f_375_; 
v___x_374_ = lean_array_uget_borrowed(v_as_364_, v_i_365_);
v_linter_x3f_375_ = lean_ctor_get(v___x_374_, 0);
if (lean_obj_tag(v_linter_x3f_375_) == 0)
{
lean_object* v___x_376_; 
lean_inc(v___x_374_);
v___x_376_ = lean_array_push(v_b_367_, v___x_374_);
v___y_369_ = v___x_376_;
goto v___jp_368_;
}
else
{
lean_object* v_val_377_; uint8_t v___x_378_; 
v_val_377_ = lean_ctor_get(v_linter_x3f_375_, 0);
v___x_378_ = l_Lean_Linter_isLinterEnabledByOptions(v_val_377_, v_linterOpts_363_);
if (v___x_378_ == 0)
{
v___y_369_ = v_b_367_;
goto v___jp_368_;
}
else
{
lean_object* v___x_379_; 
lean_inc(v___x_374_);
v___x_379_ = lean_array_push(v_b_367_, v___x_374_);
v___y_369_ = v___x_379_;
goto v___jp_368_;
}
}
}
else
{
return v_b_367_;
}
v___jp_368_:
{
size_t v___x_370_; size_t v___x_371_; 
v___x_370_ = ((size_t)1ULL);
v___x_371_ = lean_usize_add(v_i_365_, v___x_370_);
v_i_365_ = v___x_371_;
v_b_367_ = v___y_369_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_linterOpts_363_ = stack[0].m_obj;
lean_object* v_as_364_ = stack[1].m_obj;
size_t v_i_365_ = stack[2].m_num;
size_t v_stop_366_ = stack[3].m_num;
lean_object* v_b_367_ = stack[4].m_obj;
lean_object* v_res_380_;
v_res_380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__1(v_linterOpts_363_, v_as_364_, v_i_365_, v_stop_366_, v_b_367_);
stack->m_obj
 = v_res_380_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__1___boxed(lean_object* v_linterOpts_381_, lean_object* v_as_382_, lean_object* v_i_383_, lean_object* v_stop_384_, lean_object* v_b_385_){
_start:
{
size_t v_i_boxed_386_; size_t v_stop_boxed_387_; lean_object* v_res_388_; 
v_i_boxed_386_ = lean_unbox_usize(v_i_383_);
lean_dec(v_i_383_);
v_stop_boxed_387_ = lean_unbox_usize(v_stop_384_);
lean_dec(v_stop_384_);
v_res_388_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__1(v_linterOpts_381_, v_as_382_, v_i_boxed_386_, v_stop_boxed_387_, v_b_385_);
lean_dec_ref(v_as_382_);
lean_dec_ref(v_linterOpts_381_);
return v_res_388_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__2(lean_object* v_args_391_, lean_object* v_linterOpts_392_, lean_object* v_mod_393_, lean_object* v_as_394_, size_t v_sz_395_, size_t v_i_396_, lean_object* v_b_397_){
_start:
{
lean_object* v_a_399_; uint8_t v___x_403_; 
v___x_403_ = lean_usize_dec_lt(v_i_396_, v_sz_395_);
if (v___x_403_ == 0)
{
return v_b_397_;
}
else
{
lean_object* v_a_404_; lean_object* v_fst_405_; lean_object* v_snd_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_448_; 
v_a_404_ = lean_array_uget(v_as_394_, v_i_396_);
v_fst_405_ = lean_ctor_get(v_a_404_, 0);
v_snd_406_ = lean_ctor_get(v_a_404_, 1);
v_isSharedCheck_448_ = !lean_is_exclusive(v_a_404_);
if (v_isSharedCheck_448_ == 0)
{
v___x_408_ = v_a_404_;
v_isShared_409_ = v_isSharedCheck_448_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_snd_406_);
lean_inc(v_fst_405_);
lean_dec(v_a_404_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_448_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v_fst_410_; lean_object* v_snd_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_447_; 
v_fst_410_ = lean_ctor_get(v_b_397_, 0);
v_snd_411_ = lean_ctor_get(v_b_397_, 1);
v_isSharedCheck_447_ = !lean_is_exclusive(v_b_397_);
if (v_isSharedCheck_447_ == 0)
{
v___x_413_ = v_b_397_;
v_isShared_414_ = v_isSharedCheck_447_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_snd_411_);
lean_inc(v_fst_410_);
lean_dec(v_b_397_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_447_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___y_416_; lean_object* v___y_417_; uint8_t v___y_430_; lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_444_ = l_Lean_Name_getRoot(v_mod_393_);
v___x_445_ = l_Lean_Name_isPrefixOf(v___x_444_, v_fst_405_);
lean_dec(v___x_444_);
if (v___x_445_ == 0)
{
v___y_430_ = v___x_445_;
goto v___jp_429_;
}
else
{
uint8_t v___x_446_; 
v___x_446_ = l_Lean_NameSet_contains(v_fst_410_, v_fst_405_);
if (v___x_446_ == 0)
{
v___y_430_ = v___x_445_;
goto v___jp_429_;
}
else
{
lean_del_object(v___x_413_);
lean_dec(v_snd_406_);
lean_dec(v_fst_405_);
goto v___jp_425_;
}
}
v___jp_415_:
{
size_t v_sz_418_; size_t v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_423_; 
v_sz_418_ = lean_array_size(v___y_417_);
v___x_419_ = ((size_t)0ULL);
v___x_420_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__0(v_sz_418_, v___x_419_, v___y_417_);
v___x_421_ = l_Array_append___redArg(v_snd_411_, v___x_420_);
lean_dec_ref(v___x_420_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 1, v___x_421_);
lean_ctor_set(v___x_413_, 0, v___y_416_);
v___x_423_ = v___x_413_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___y_416_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v___x_421_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
v_a_399_ = v___x_423_;
goto v___jp_398_;
}
}
v___jp_425_:
{
lean_object* v___x_427_; 
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 1, v_snd_411_);
lean_ctor_set(v___x_408_, 0, v_fst_410_);
v___x_427_ = v___x_408_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_fst_410_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_snd_411_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
v_a_399_ = v___x_427_;
goto v___jp_398_;
}
}
v___jp_429_:
{
if (v___y_430_ == 0)
{
lean_del_object(v___x_413_);
lean_dec(v_snd_406_);
lean_dec(v_fst_405_);
goto v___jp_425_;
}
else
{
uint8_t v_lintOnly_431_; lean_object* v___x_432_; 
lean_del_object(v___x_408_);
v_lintOnly_431_ = lean_ctor_get_uint8(v_args_391_, sizeof(void*)*4);
v___x_432_ = l_Lean_NameSet_insert(v_fst_410_, v_fst_405_);
if (v_lintOnly_431_ == 0)
{
v___y_416_ = v___x_432_;
v___y_417_ = v_snd_406_;
goto v___jp_415_;
}
else
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; uint8_t v___x_436_; 
v___x_433_ = lean_unsigned_to_nat(0u);
v___x_434_ = lean_array_get_size(v_snd_406_);
v___x_435_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__2___closed__0));
v___x_436_ = lean_nat_dec_lt(v___x_433_, v___x_434_);
if (v___x_436_ == 0)
{
lean_dec(v_snd_406_);
v___y_416_ = v___x_432_;
v___y_417_ = v___x_435_;
goto v___jp_415_;
}
else
{
uint8_t v___x_437_; 
v___x_437_ = lean_nat_dec_le(v___x_434_, v___x_434_);
if (v___x_437_ == 0)
{
if (v___x_436_ == 0)
{
lean_dec(v_snd_406_);
v___y_416_ = v___x_432_;
v___y_417_ = v___x_435_;
goto v___jp_415_;
}
else
{
size_t v___x_438_; size_t v___x_439_; lean_object* v___x_440_; 
v___x_438_ = ((size_t)0ULL);
v___x_439_ = lean_usize_of_nat(v___x_434_);
v___x_440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__1(v_linterOpts_392_, v_snd_406_, v___x_438_, v___x_439_, v___x_435_);
lean_dec(v_snd_406_);
v___y_416_ = v___x_432_;
v___y_417_ = v___x_440_;
goto v___jp_415_;
}
}
else
{
size_t v___x_441_; size_t v___x_442_; lean_object* v___x_443_; 
v___x_441_ = ((size_t)0ULL);
v___x_442_ = lean_usize_of_nat(v___x_434_);
v___x_443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__1(v_linterOpts_392_, v_snd_406_, v___x_441_, v___x_442_, v___x_435_);
lean_dec(v_snd_406_);
v___y_416_ = v___x_432_;
v___y_417_ = v___x_443_;
goto v___jp_415_;
}
}
}
}
}
}
}
}
v___jp_398_:
{
size_t v___x_400_; size_t v___x_401_; 
v___x_400_ = ((size_t)1ULL);
v___x_401_ = lean_usize_add(v_i_396_, v___x_400_);
v_i_396_ = v___x_401_;
v_b_397_ = v_a_399_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_391_ = stack[0].m_obj;
lean_object* v_linterOpts_392_ = stack[1].m_obj;
lean_object* v_mod_393_ = stack[2].m_obj;
lean_object* v_as_394_ = stack[3].m_obj;
size_t v_sz_395_ = stack[4].m_num;
size_t v_i_396_ = stack[5].m_num;
lean_object* v_b_397_ = stack[6].m_obj;
lean_object* v_res_449_;
v_res_449_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__2(v_args_391_, v_linterOpts_392_, v_mod_393_, v_as_394_, v_sz_395_, v_i_396_, v_b_397_);
stack->m_obj
 = v_res_449_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__2___boxed(lean_object* v_args_450_, lean_object* v_linterOpts_451_, lean_object* v_mod_452_, lean_object* v_as_453_, lean_object* v_sz_454_, lean_object* v_i_455_, lean_object* v_b_456_){
_start:
{
size_t v_sz_boxed_457_; size_t v_i_boxed_458_; lean_object* v_res_459_; 
v_sz_boxed_457_ = lean_unbox_usize(v_sz_454_);
lean_dec(v_sz_454_);
v_i_boxed_458_ = lean_unbox_usize(v_i_455_);
lean_dec(v_i_455_);
v_res_459_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__2(v_args_450_, v_linterOpts_451_, v_mod_452_, v_as_453_, v_sz_boxed_457_, v_i_boxed_458_, v_b_456_);
lean_dec_ref(v_as_453_);
lean_dec(v_mod_452_);
lean_dec_ref(v_linterOpts_451_);
lean_dec_ref(v_args_450_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality(lean_object* v_args_462_, lean_object* v_linterOpts_463_, lean_object* v_env_464_, lean_object* v_mod_465_, lean_object* v_collectedModules_466_){
_start:
{
lean_object* v_acc_467_; lean_object* v___x_468_; lean_object* v___x_469_; size_t v_sz_470_; size_t v___x_471_; lean_object* v___x_472_; lean_object* v_fst_473_; lean_object* v_snd_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
v_acc_467_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality___closed__0));
v___x_468_ = l_Lean_Linter_getAllCodeQualityEntries(v_env_464_);
v___x_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_469_, 0, v_collectedModules_466_);
lean_ctor_set(v___x_469_, 1, v_acc_467_);
v_sz_470_ = lean_array_size(v___x_468_);
v___x_471_ = ((size_t)0ULL);
v___x_472_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__2(v_args_462_, v_linterOpts_463_, v_mod_465_, v___x_468_, v_sz_470_, v___x_471_, v___x_469_);
lean_dec_ref(v___x_468_);
v_fst_473_ = lean_ctor_get(v___x_472_, 0);
v_snd_474_ = lean_ctor_get(v___x_472_, 1);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_472_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_snd_474_);
lean_inc(v_fst_473_);
lean_dec(v___x_472_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_479_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 1, v_fst_473_);
lean_ctor_set(v___x_476_, 0, v_snd_474_);
v___x_479_ = v___x_476_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_snd_474_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_fst_473_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality___boxed(lean_object* v_args_482_, lean_object* v_linterOpts_483_, lean_object* v_env_484_, lean_object* v_mod_485_, lean_object* v_collectedModules_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality(v_args_482_, v_linterOpts_483_, v_env_484_, v_mod_485_, v_collectedModules_486_);
lean_dec(v_mod_485_);
lean_dec_ref(v_env_484_);
lean_dec_ref(v_linterOpts_483_);
lean_dec_ref(v_args_482_);
return v_res_487_;
}
}
uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(lean_object* v_modData_488_){
_start:
{
uint8_t v_isModule_490_; 
v_isModule_490_ = lean_ctor_get_uint8(v_modData_488_, sizeof(void*)*5);
return v_isModule_490_;
}
}
LEAN_EXPORT void l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule_0interp(lean_interpreter_value* stack)
{
lean_object* v_modData_488_ = stack[0].m_obj;
uint8_t v_res_491_;
v_res_491_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(v_modData_488_);
stack->m_num = v_res_491_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule___boxed(lean_object* v_modData_492_, lean_object* v_a_493_){
_start:
{
uint8_t v_res_494_; lean_object* v_r_495_; 
v_res_494_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(v_modData_492_);
lean_dec_ref(v_modData_492_);
v_r_495_ = lean_box(v_res_494_);
return v_r_495_;
}
}
uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_isIndentChar(uint32_t v_c_498_){
_start:
{
uint32_t v___x_499_; uint8_t v___x_500_; 
v___x_499_ = 32;
v___x_500_ = lean_uint32_dec_eq(v_c_498_, v___x_499_);
if (v___x_500_ == 0)
{
uint32_t v___x_501_; uint8_t v___x_502_; 
v___x_501_ = 9;
v___x_502_ = lean_uint32_dec_eq(v_c_498_, v___x_501_);
return v___x_502_;
}
else
{
return v___x_500_;
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_isIndentChar_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_498_ = stack[0].m_num;
uint8_t v_res_503_;
v_res_503_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_isIndentChar(v_c_498_);
stack->m_num = v_res_503_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_isIndentChar___boxed(lean_object* v_c_504_){
_start:
{
uint32_t v_c_boxed_505_; uint8_t v_res_506_; lean_object* v_r_507_; 
v_c_boxed_505_ = lean_unbox_uint32(v_c_504_);
lean_dec(v_c_504_);
v_res_506_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_isIndentChar(v_c_boxed_505_);
v_r_507_ = lean_box(v_res_506_);
return v_r_507_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace_spec__0(lean_object* v_s_508_, lean_object* v_stopPos_509_, lean_object* v_i_510_){
_start:
{
uint8_t v___y_512_; lean_object* v___x_515_; lean_object* v___x_516_; uint8_t v___x_517_; 
v___x_515_ = lean_unsigned_to_nat(1u);
v___x_516_ = lean_nat_add(v_i_510_, v___x_515_);
v___x_517_ = lean_nat_dec_le(v___x_516_, v_stopPos_509_);
lean_dec(v___x_516_);
if (v___x_517_ == 0)
{
return v_i_510_;
}
else
{
if (v___x_517_ == 0)
{
v___y_512_ = v___x_517_;
goto v___jp_511_;
}
else
{
uint32_t v___x_518_; uint8_t v___x_519_; 
v___x_518_ = lean_string_utf8_get(v_s_508_, v_i_510_);
v___x_519_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_isIndentChar(v___x_518_);
v___y_512_ = v___x_519_;
goto v___jp_511_;
}
}
v___jp_511_:
{
if (v___y_512_ == 0)
{
return v_i_510_;
}
else
{
lean_object* v___x_513_; 
v___x_513_ = lean_string_utf8_next(v_s_508_, v_i_510_);
lean_dec(v_i_510_);
v_i_510_ = v___x_513_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace_spec__0___boxed(lean_object* v_s_520_, lean_object* v_stopPos_521_, lean_object* v_i_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Substring_Raw_takeWhileAux___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace_spec__0(v_s_520_, v_stopPos_521_, v_i_522_);
lean_dec(v_stopPos_521_);
lean_dec_ref(v_s_520_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace(lean_object* v_line_524_){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v_e_527_; lean_object* v___x_528_; 
v___x_525_ = lean_unsigned_to_nat(0u);
v___x_526_ = lean_string_utf8_byte_size(v_line_524_);
v_e_527_ = l_Substring_Raw_takeWhileAux___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace_spec__0(v_line_524_, v___x_526_, v___x_525_);
v___x_528_ = lean_string_utf8_extract(v_line_524_, v___x_525_, v_e_527_);
lean_dec(v_e_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace___boxed(lean_object* v_line_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace(v_line_529_);
lean_dec_ref(v_line_529_);
return v_res_530_;
}
}
lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg(){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg___closed__0));
return v___x_534_;
}
}
LEAN_EXPORT void l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_535_;
v_res_535_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg();
stack->m_obj
 = v_res_535_;
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg___boxed(lean_object* v___dummy_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg();
return v_res_537_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0(void){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg();
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7(lean_object* v_s_539_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___boxed(lean_object* v_s_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7(v_s_541_);
lean_dec_ref(v_s_541_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(lean_object* v_x_543_, lean_object* v_x_544_){
_start:
{
if (lean_obj_tag(v_x_544_) == 0)
{
return v_x_543_;
}
else
{
lean_object* v_key_545_; lean_object* v_value_546_; lean_object* v_tail_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v_key_545_ = lean_ctor_get(v_x_544_, 0);
v_value_546_ = lean_ctor_get(v_x_544_, 1);
v_tail_547_ = lean_ctor_get(v_x_544_, 2);
lean_inc(v_value_546_);
lean_inc(v_key_545_);
v___x_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_548_, 0, v_key_545_);
lean_ctor_set(v___x_548_, 1, v_value_546_);
v___x_549_ = lean_array_push(v_x_543_, v___x_548_);
v_x_543_ = v___x_549_;
v_x_544_ = v_tail_547_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19___boxed(lean_object* v_x_551_, lean_object* v_x_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(v_x_551_, v_x_552_);
lean_dec(v_x_552_);
return v_res_553_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(lean_object* v_as_554_, size_t v_i_555_, size_t v_stop_556_, lean_object* v_b_557_){
_start:
{
uint8_t v___x_558_; 
v___x_558_ = lean_usize_dec_eq(v_i_555_, v_stop_556_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; size_t v___x_561_; size_t v___x_562_; 
v___x_559_ = lean_array_uget_borrowed(v_as_554_, v_i_555_);
v___x_560_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(v_b_557_, v___x_559_);
v___x_561_ = ((size_t)1ULL);
v___x_562_ = lean_usize_add(v_i_555_, v___x_561_);
v_i_555_ = v___x_562_;
v_b_557_ = v___x_560_;
goto _start;
}
else
{
return v_b_557_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_554_ = stack[0].m_obj;
size_t v_i_555_ = stack[1].m_num;
size_t v_stop_556_ = stack[2].m_num;
lean_object* v_b_557_ = stack[3].m_obj;
lean_object* v_res_564_;
v_res_564_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(v_as_554_, v_i_555_, v_stop_556_, v_b_557_);
stack->m_obj
 = v_res_564_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___boxed(lean_object* v_as_565_, lean_object* v_i_566_, lean_object* v_stop_567_, lean_object* v_b_568_){
_start:
{
size_t v_i_boxed_569_; size_t v_stop_boxed_570_; lean_object* v_res_571_; 
v_i_boxed_569_ = lean_unbox_usize(v_i_566_);
lean_dec(v_i_566_);
v_stop_boxed_570_ = lean_unbox_usize(v_stop_567_);
lean_dec(v_stop_567_);
v_res_571_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(v_as_565_, v_i_boxed_569_, v_stop_boxed_570_, v_b_568_);
lean_dec_ref(v_as_565_);
return v_res_571_;
}
}
lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(lean_object* v_s_572_){
_start:
{
lean_object* v___x_574_; lean_object* v_putStr_575_; lean_object* v___x_576_; 
v___x_574_ = lean_get_stderr();
v_putStr_575_ = lean_ctor_get(v___x_574_, 4);
lean_inc_ref(v_putStr_575_);
lean_dec_ref(v___x_574_);
v___x_576_ = lean_apply_2(v_putStr_575_, v_s_572_, lean_box(0));
return v___x_576_;
}
}
LEAN_EXPORT void l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_572_ = stack[0].m_obj;
lean_object* v_res_577_;
v_res_577_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(v_s_572_);
stack->m_obj
 = v_res_577_;
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29___boxed(lean_object* v_s_578_, lean_object* v_a_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(v_s_578_);
return v_res_580_;
}
}
lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(lean_object* v_s_581_){
_start:
{
uint32_t v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_583_ = 10;
v___x_584_ = lean_string_push(v_s_581_, v___x_583_);
v___x_585_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(v___x_584_);
return v___x_585_;
}
}
LEAN_EXPORT void l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_581_ = stack[0].m_obj;
lean_object* v_res_586_;
v_res_586_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v_s_581_);
stack->m_obj
 = v_res_586_;
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17___boxed(lean_object* v_s_587_, lean_object* v_a_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v_s_587_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15(lean_object* v_x_590_, lean_object* v_x_591_){
_start:
{
if (lean_obj_tag(v_x_591_) == 0)
{
return v_x_590_;
}
else
{
lean_object* v_key_592_; lean_object* v_value_593_; lean_object* v_tail_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v_key_592_ = lean_ctor_get(v_x_591_, 0);
v_value_593_ = lean_ctor_get(v_x_591_, 1);
v_tail_594_ = lean_ctor_get(v_x_591_, 2);
lean_inc(v_value_593_);
lean_inc(v_key_592_);
v___x_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_595_, 0, v_key_592_);
lean_ctor_set(v___x_595_, 1, v_value_593_);
v___x_596_ = lean_array_push(v_x_590_, v___x_595_);
v_x_590_ = v___x_596_;
v_x_591_ = v_tail_594_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15___boxed(lean_object* v_x_598_, lean_object* v_x_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15(v_x_598_, v_x_599_);
lean_dec(v_x_599_);
return v_res_600_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(lean_object* v_as_601_, size_t v_i_602_, size_t v_stop_603_, lean_object* v_b_604_){
_start:
{
uint8_t v___x_605_; 
v___x_605_ = lean_usize_dec_eq(v_i_602_, v_stop_603_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; lean_object* v___x_607_; size_t v___x_608_; size_t v___x_609_; 
v___x_606_ = lean_array_uget_borrowed(v_as_601_, v_i_602_);
v___x_607_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15(v_b_604_, v___x_606_);
v___x_608_ = ((size_t)1ULL);
v___x_609_ = lean_usize_add(v_i_602_, v___x_608_);
v_i_602_ = v___x_609_;
v_b_604_ = v___x_607_;
goto _start;
}
else
{
return v_b_604_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_601_ = stack[0].m_obj;
size_t v_i_602_ = stack[1].m_num;
size_t v_stop_603_ = stack[2].m_num;
lean_object* v_b_604_ = stack[3].m_obj;
lean_object* v_res_611_;
v_res_611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(v_as_601_, v_i_602_, v_stop_603_, v_b_604_);
stack->m_obj
 = v_res_611_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16___boxed(lean_object* v_as_612_, lean_object* v_i_613_, lean_object* v_stop_614_, lean_object* v_b_615_){
_start:
{
size_t v_i_boxed_616_; size_t v_stop_boxed_617_; lean_object* v_res_618_; 
v_i_boxed_616_ = lean_unbox_usize(v_i_613_);
lean_dec(v_i_613_);
v_stop_boxed_617_ = lean_unbox_usize(v_stop_614_);
lean_dec(v_stop_614_);
v_res_618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(v_as_612_, v_i_boxed_616_, v_stop_boxed_617_, v_b_615_);
lean_dec_ref(v_as_612_);
return v_res_618_;
}
}
uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(lean_object* v_a_619_, lean_object* v_b_620_){
_start:
{
lean_object* v_fst_621_; lean_object* v_fst_622_; uint8_t v___x_623_; 
v_fst_621_ = lean_ctor_get(v_b_620_, 0);
v_fst_622_ = lean_ctor_get(v_a_619_, 0);
v___x_623_ = lean_nat_dec_lt(v_fst_621_, v_fst_622_);
return v___x_623_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_619_ = stack[0].m_obj;
lean_object* v_b_620_ = stack[1].m_obj;
uint8_t v_res_624_;
v_res_624_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v_a_619_, v_b_620_);
stack->m_num = v_res_624_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0___boxed(lean_object* v_a_625_, lean_object* v_b_626_){
_start:
{
uint8_t v_res_627_; lean_object* v_r_628_; 
v_res_627_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v_a_625_, v_b_626_);
lean_dec_ref(v_b_626_);
lean_dec_ref(v_a_625_);
v_r_628_ = lean_box(v_res_627_);
return v_r_628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(lean_object* v_hi_629_, lean_object* v_pivot_630_, lean_object* v_as_631_, lean_object* v_i_632_, lean_object* v_k_633_){
_start:
{
uint8_t v___x_634_; 
v___x_634_ = lean_nat_dec_lt(v_k_633_, v_hi_629_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; lean_object* v___x_636_; 
lean_dec(v_k_633_);
v___x_635_ = lean_array_fswap(v_as_631_, v_i_632_, v_hi_629_);
v___x_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_636_, 0, v_i_632_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
return v___x_636_;
}
else
{
lean_object* v_fst_637_; lean_object* v___x_638_; lean_object* v_fst_639_; uint8_t v___x_640_; 
v_fst_637_ = lean_ctor_get(v_pivot_630_, 0);
v___x_638_ = lean_array_fget_borrowed(v_as_631_, v_k_633_);
v_fst_639_ = lean_ctor_get(v___x_638_, 0);
v___x_640_ = lean_nat_dec_lt(v_fst_637_, v_fst_639_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = lean_unsigned_to_nat(1u);
v___x_642_ = lean_nat_add(v_k_633_, v___x_641_);
lean_dec(v_k_633_);
v_k_633_ = v___x_642_;
goto _start;
}
else
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_644_ = lean_array_fswap(v_as_631_, v_i_632_, v_k_633_);
v___x_645_ = lean_unsigned_to_nat(1u);
v___x_646_ = lean_nat_add(v_i_632_, v___x_645_);
lean_dec(v_i_632_);
v___x_647_ = lean_nat_add(v_k_633_, v___x_645_);
lean_dec(v_k_633_);
v_as_631_ = v___x_644_;
v_i_632_ = v___x_646_;
v_k_633_ = v___x_647_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg___boxed(lean_object* v_hi_649_, lean_object* v_pivot_650_, lean_object* v_as_651_, lean_object* v_i_652_, lean_object* v_k_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(v_hi_649_, v_pivot_650_, v_as_651_, v_i_652_, v_k_653_);
lean_dec_ref(v_pivot_650_);
lean_dec(v_hi_649_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(lean_object* v_n_655_, lean_object* v_as_656_, lean_object* v_lo_657_, lean_object* v_hi_658_){
_start:
{
lean_object* v___y_660_; uint8_t v___x_670_; 
v___x_670_ = lean_nat_dec_lt(v_lo_657_, v_hi_658_);
if (v___x_670_ == 0)
{
lean_dec(v_lo_657_);
return v_as_656_;
}
else
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v_mid_673_; lean_object* v___y_675_; lean_object* v___y_681_; lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_671_ = lean_nat_add(v_lo_657_, v_hi_658_);
v___x_672_ = lean_unsigned_to_nat(1u);
v_mid_673_ = lean_nat_shiftr(v___x_671_, v___x_672_);
lean_dec(v___x_671_);
v___x_686_ = lean_array_fget_borrowed(v_as_656_, v_mid_673_);
v___x_687_ = lean_array_fget_borrowed(v_as_656_, v_lo_657_);
v___x_688_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v___x_686_, v___x_687_);
if (v___x_688_ == 0)
{
v___y_681_ = v_as_656_;
goto v___jp_680_;
}
else
{
lean_object* v___x_689_; 
v___x_689_ = lean_array_fswap(v_as_656_, v_lo_657_, v_mid_673_);
v___y_681_ = v___x_689_;
goto v___jp_680_;
}
v___jp_674_:
{
lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v___x_676_ = lean_array_fget_borrowed(v___y_675_, v_mid_673_);
v___x_677_ = lean_array_fget_borrowed(v___y_675_, v_hi_658_);
v___x_678_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v___x_676_, v___x_677_);
if (v___x_678_ == 0)
{
lean_dec(v_mid_673_);
v___y_660_ = v___y_675_;
goto v___jp_659_;
}
else
{
lean_object* v___x_679_; 
v___x_679_ = lean_array_fswap(v___y_675_, v_mid_673_, v_hi_658_);
lean_dec(v_mid_673_);
v___y_660_ = v___x_679_;
goto v___jp_659_;
}
}
v___jp_680_:
{
lean_object* v___x_682_; lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_682_ = lean_array_fget_borrowed(v___y_681_, v_hi_658_);
v___x_683_ = lean_array_fget_borrowed(v___y_681_, v_lo_657_);
v___x_684_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v___x_682_, v___x_683_);
if (v___x_684_ == 0)
{
v___y_675_ = v___y_681_;
goto v___jp_674_;
}
else
{
lean_object* v___x_685_; 
v___x_685_ = lean_array_fswap(v___y_681_, v_lo_657_, v_hi_658_);
v___y_675_ = v___x_685_;
goto v___jp_674_;
}
}
}
v___jp_659_:
{
lean_object* v_pivot_661_; lean_object* v___x_662_; lean_object* v_fst_663_; lean_object* v_snd_664_; uint8_t v___x_665_; 
v_pivot_661_ = lean_array_fget(v___y_660_, v_hi_658_);
lean_inc_n(v_lo_657_, 2);
v___x_662_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(v_hi_658_, v_pivot_661_, v___y_660_, v_lo_657_, v_lo_657_);
lean_dec(v_pivot_661_);
v_fst_663_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_fst_663_);
v_snd_664_ = lean_ctor_get(v___x_662_, 1);
lean_inc(v_snd_664_);
lean_dec_ref(v___x_662_);
v___x_665_ = lean_nat_dec_le(v_hi_658_, v_fst_663_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_666_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v_n_655_, v_snd_664_, v_lo_657_, v_fst_663_);
v___x_667_ = lean_unsigned_to_nat(1u);
v___x_668_ = lean_nat_add(v_fst_663_, v___x_667_);
lean_dec(v_fst_663_);
v_as_656_ = v___x_666_;
v_lo_657_ = v___x_668_;
goto _start;
}
else
{
lean_dec(v_fst_663_);
lean_dec(v_lo_657_);
return v_snd_664_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___boxed(lean_object* v_n_690_, lean_object* v_as_691_, lean_object* v_lo_692_, lean_object* v_hi_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v_n_690_, v_as_691_, v_lo_692_, v_hi_693_);
lean_dec(v_hi_693_);
lean_dec(v_n_690_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(lean_object* v_a_695_, lean_object* v___x_696_, lean_object* v___x_697_, lean_object* v_a_698_, lean_object* v_b_699_){
_start:
{
lean_object* v_it_701_; lean_object* v_startInclusive_702_; lean_object* v_endExclusive_703_; 
if (lean_obj_tag(v_a_698_) == 0)
{
lean_object* v_currPos_707_; lean_object* v_searcher_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_731_; 
v_currPos_707_ = lean_ctor_get(v_a_698_, 0);
v_searcher_708_ = lean_ctor_get(v_a_698_, 1);
v_isSharedCheck_731_ = !lean_is_exclusive(v_a_698_);
if (v_isSharedCheck_731_ == 0)
{
v___x_710_ = v_a_698_;
v_isShared_711_ = v_isSharedCheck_731_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_searcher_708_);
lean_inc(v_currPos_707_);
lean_dec(v_a_698_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_731_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
uint8_t v_decide_712_; 
v_decide_712_ = lean_nat_dec_eq(v_searcher_708_, v___x_697_);
if (v_decide_712_ == 0)
{
uint32_t v___x_713_; uint32_t v___x_714_; uint8_t v___x_715_; 
v___x_713_ = 10;
v___x_714_ = lean_string_utf8_get_fast(v_a_695_, v_searcher_708_);
v___x_715_ = lean_uint32_dec_eq(v___x_714_, v___x_713_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; lean_object* v___x_718_; 
v___x_716_ = lean_string_utf8_next_fast(v_a_695_, v_searcher_708_);
lean_dec(v_searcher_708_);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 1, v___x_716_);
v___x_718_ = v___x_710_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_currPos_707_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v___x_716_);
v___x_718_ = v_reuseFailAlloc_720_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
v_a_698_ = v___x_718_;
goto _start;
}
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v_slice_724_; lean_object* v_nextIt_726_; 
v___x_721_ = lean_string_utf8_next_fast(v_a_695_, v_searcher_708_);
v___x_722_ = lean_nat_sub(v___x_721_, v_searcher_708_);
v___x_723_ = lean_nat_add(v_searcher_708_, v___x_722_);
lean_dec(v___x_722_);
v_slice_724_ = l_String_Slice_subslice_x21(v___x_696_, v_currPos_707_, v_searcher_708_);
lean_inc(v___x_723_);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 1, v___x_723_);
lean_ctor_set(v___x_710_, 0, v___x_723_);
v_nextIt_726_ = v___x_710_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_723_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v___x_723_);
v_nextIt_726_ = v_reuseFailAlloc_729_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
lean_object* v_startInclusive_727_; lean_object* v_endExclusive_728_; 
v_startInclusive_727_ = lean_ctor_get(v_slice_724_, 0);
lean_inc(v_startInclusive_727_);
v_endExclusive_728_ = lean_ctor_get(v_slice_724_, 1);
lean_inc(v_endExclusive_728_);
lean_dec_ref(v_slice_724_);
v_it_701_ = v_nextIt_726_;
v_startInclusive_702_ = v_startInclusive_727_;
v_endExclusive_703_ = v_endExclusive_728_;
goto v___jp_700_;
}
}
}
else
{
lean_object* v___x_730_; 
lean_del_object(v___x_710_);
lean_dec(v_searcher_708_);
v___x_730_ = lean_box(1);
lean_inc(v___x_697_);
v_it_701_ = v___x_730_;
v_startInclusive_702_ = v_currPos_707_;
v_endExclusive_703_ = v___x_697_;
goto v___jp_700_;
}
}
}
else
{
lean_dec(v___x_697_);
lean_dec_ref(v_a_695_);
return v_b_699_;
}
v___jp_700_:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
lean_inc_ref(v_a_695_);
v___x_704_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_704_, 0, v_a_695_);
lean_ctor_set(v___x_704_, 1, v_startInclusive_702_);
lean_ctor_set(v___x_704_, 2, v_endExclusive_703_);
v___x_705_ = lean_array_push(v_b_699_, v___x_704_);
v_a_698_ = v_it_701_;
v_b_699_ = v___x_705_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg___boxed(lean_object* v_a_732_, lean_object* v___x_733_, lean_object* v___x_734_, lean_object* v_a_735_, lean_object* v_b_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(v_a_732_, v___x_733_, v___x_734_, v_a_735_, v_b_736_);
lean_dec_ref(v___x_733_);
return v_res_737_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9(size_t v_sz_738_, size_t v_i_739_, lean_object* v_bs_740_){
_start:
{
uint8_t v___x_741_; 
v___x_741_ = lean_usize_dec_lt(v_i_739_, v_sz_738_);
if (v___x_741_ == 0)
{
return v_bs_740_;
}
else
{
lean_object* v_v_742_; lean_object* v___x_743_; lean_object* v_bs_x27_744_; lean_object* v___x_745_; size_t v___x_746_; size_t v___x_747_; lean_object* v___x_748_; 
v_v_742_ = lean_array_uget(v_bs_740_, v_i_739_);
v___x_743_ = lean_unsigned_to_nat(0u);
v_bs_x27_744_ = lean_array_uset(v_bs_740_, v_i_739_, v___x_743_);
v___x_745_ = l_String_Slice_toString(v_v_742_);
lean_dec(v_v_742_);
v___x_746_ = ((size_t)1ULL);
v___x_747_ = lean_usize_add(v_i_739_, v___x_746_);
v___x_748_ = lean_array_uset(v_bs_x27_744_, v_i_739_, v___x_745_);
v_i_739_ = v___x_747_;
v_bs_740_ = v___x_748_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9_0interp(lean_interpreter_value* stack)
{
size_t v_sz_738_ = stack[0].m_num;
size_t v_i_739_ = stack[1].m_num;
lean_object* v_bs_740_ = stack[2].m_obj;
lean_object* v_res_750_;
v_res_750_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9(v_sz_738_, v_i_739_, v_bs_740_);
stack->m_obj
 = v_res_750_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9___boxed(lean_object* v_sz_751_, lean_object* v_i_752_, lean_object* v_bs_753_){
_start:
{
size_t v_sz_boxed_754_; size_t v_i_boxed_755_; lean_object* v_res_756_; 
v_sz_boxed_754_ = lean_unbox_usize(v_sz_751_);
lean_dec(v_sz_751_);
v_i_boxed_755_ = lean_unbox_usize(v_i_752_);
lean_dec(v_i_752_);
v_res_756_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9(v_sz_boxed_754_, v_i_boxed_755_, v_bs_753_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33___redArg(lean_object* v_x_757_, lean_object* v_x_758_){
_start:
{
if (lean_obj_tag(v_x_758_) == 0)
{
return v_x_757_;
}
else
{
lean_object* v_key_759_; lean_object* v_value_760_; lean_object* v_tail_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_784_; 
v_key_759_ = lean_ctor_get(v_x_758_, 0);
v_value_760_ = lean_ctor_get(v_x_758_, 1);
v_tail_761_ = lean_ctor_get(v_x_758_, 2);
v_isSharedCheck_784_ = !lean_is_exclusive(v_x_758_);
if (v_isSharedCheck_784_ == 0)
{
v___x_763_ = v_x_758_;
v_isShared_764_ = v_isSharedCheck_784_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_tail_761_);
lean_inc(v_value_760_);
lean_inc(v_key_759_);
lean_dec(v_x_758_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_784_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_765_; uint64_t v___x_766_; uint64_t v___x_767_; uint64_t v___x_768_; uint64_t v_fold_769_; uint64_t v___x_770_; uint64_t v___x_771_; uint64_t v___x_772_; size_t v___x_773_; size_t v___x_774_; size_t v___x_775_; size_t v___x_776_; size_t v___x_777_; lean_object* v___x_778_; lean_object* v___x_780_; 
v___x_765_ = lean_array_get_size(v_x_757_);
v___x_766_ = lean_uint64_of_nat(v_key_759_);
v___x_767_ = 32ULL;
v___x_768_ = lean_uint64_shift_right(v___x_766_, v___x_767_);
v_fold_769_ = lean_uint64_xor(v___x_766_, v___x_768_);
v___x_770_ = 16ULL;
v___x_771_ = lean_uint64_shift_right(v_fold_769_, v___x_770_);
v___x_772_ = lean_uint64_xor(v_fold_769_, v___x_771_);
v___x_773_ = lean_uint64_to_usize(v___x_772_);
v___x_774_ = lean_usize_of_nat(v___x_765_);
v___x_775_ = ((size_t)1ULL);
v___x_776_ = lean_usize_sub(v___x_774_, v___x_775_);
v___x_777_ = lean_usize_land(v___x_773_, v___x_776_);
v___x_778_ = lean_array_uget_borrowed(v_x_757_, v___x_777_);
lean_inc(v___x_778_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 2, v___x_778_);
v___x_780_ = v___x_763_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_key_759_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_value_760_);
lean_ctor_set(v_reuseFailAlloc_783_, 2, v___x_778_);
v___x_780_ = v_reuseFailAlloc_783_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_781_; 
v___x_781_ = lean_array_uset(v_x_757_, v___x_777_, v___x_780_);
v_x_757_ = v___x_781_;
v_x_758_ = v_tail_761_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15___redArg(lean_object* v_i_785_, lean_object* v_source_786_, lean_object* v_target_787_){
_start:
{
lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_788_ = lean_array_get_size(v_source_786_);
v___x_789_ = lean_nat_dec_lt(v_i_785_, v___x_788_);
if (v___x_789_ == 0)
{
lean_dec_ref(v_source_786_);
lean_dec(v_i_785_);
return v_target_787_;
}
else
{
lean_object* v_es_790_; lean_object* v___x_791_; lean_object* v_source_792_; lean_object* v_target_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v_es_790_ = lean_array_fget(v_source_786_, v_i_785_);
v___x_791_ = lean_box(0);
v_source_792_ = lean_array_fset(v_source_786_, v_i_785_, v___x_791_);
v_target_793_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33___redArg(v_target_787_, v_es_790_);
v___x_794_ = lean_unsigned_to_nat(1u);
v___x_795_ = lean_nat_add(v_i_785_, v___x_794_);
lean_dec(v_i_785_);
v_i_785_ = v___x_795_;
v_source_786_ = v_source_792_;
v_target_787_ = v_target_793_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12___redArg(lean_object* v_data_797_){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v_nbuckets_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_798_ = lean_array_get_size(v_data_797_);
v___x_799_ = lean_unsigned_to_nat(2u);
v_nbuckets_800_ = lean_nat_mul(v___x_798_, v___x_799_);
v___x_801_ = lean_unsigned_to_nat(0u);
v___x_802_ = lean_box(0);
v___x_803_ = lean_mk_array(v_nbuckets_800_, v___x_802_);
v___x_804_ = lean_array_propagate_mark(v_data_797_, v___x_803_);
v___x_805_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15___redArg(v___x_801_, v_data_797_, v___x_804_);
return v___x_805_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(lean_object* v_a_806_, lean_object* v_x_807_){
_start:
{
if (lean_obj_tag(v_x_807_) == 0)
{
uint8_t v___x_808_; 
v___x_808_ = 0;
return v___x_808_;
}
else
{
lean_object* v_key_809_; lean_object* v_tail_810_; uint8_t v___x_811_; 
v_key_809_ = lean_ctor_get(v_x_807_, 0);
v_tail_810_ = lean_ctor_get(v_x_807_, 2);
v___x_811_ = lean_nat_dec_eq(v_key_809_, v_a_806_);
if (v___x_811_ == 0)
{
v_x_807_ = v_tail_810_;
goto _start;
}
else
{
return v___x_811_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_806_ = stack[0].m_obj;
lean_object* v_x_807_ = stack[1].m_obj;
uint8_t v_res_813_;
v_res_813_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(v_a_806_, v_x_807_);
stack->m_num = v_res_813_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg___boxed(lean_object* v_a_814_, lean_object* v_x_815_){
_start:
{
uint8_t v_res_816_; lean_object* v_r_817_; 
v_res_816_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(v_a_814_, v_x_815_);
lean_dec(v_x_815_);
lean_dec(v_a_814_);
v_r_817_ = lean_box(v_res_816_);
return v_r_817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(lean_object* v_a_818_, lean_object* v_b_819_, lean_object* v_x_820_){
_start:
{
if (lean_obj_tag(v_x_820_) == 0)
{
lean_dec(v_b_819_);
lean_dec(v_a_818_);
return v_x_820_;
}
else
{
lean_object* v_key_821_; lean_object* v_value_822_; lean_object* v_tail_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_835_; 
v_key_821_ = lean_ctor_get(v_x_820_, 0);
v_value_822_ = lean_ctor_get(v_x_820_, 1);
v_tail_823_ = lean_ctor_get(v_x_820_, 2);
v_isSharedCheck_835_ = !lean_is_exclusive(v_x_820_);
if (v_isSharedCheck_835_ == 0)
{
v___x_825_ = v_x_820_;
v_isShared_826_ = v_isSharedCheck_835_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_tail_823_);
lean_inc(v_value_822_);
lean_inc(v_key_821_);
lean_dec(v_x_820_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_835_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
uint8_t v___x_827_; 
v___x_827_ = lean_nat_dec_eq(v_key_821_, v_a_818_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; lean_object* v___x_830_; 
v___x_828_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(v_a_818_, v_b_819_, v_tail_823_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 2, v___x_828_);
v___x_830_ = v___x_825_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_key_821_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v_value_822_);
lean_ctor_set(v_reuseFailAlloc_831_, 2, v___x_828_);
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
lean_dec(v_value_822_);
lean_dec(v_key_821_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 1, v_b_819_);
lean_ctor_set(v___x_825_, 0, v_a_818_);
v___x_833_ = v___x_825_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_818_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v_b_819_);
lean_ctor_set(v_reuseFailAlloc_834_, 2, v_tail_823_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(lean_object* v_m_836_, lean_object* v_a_837_, lean_object* v_b_838_){
_start:
{
lean_object* v_size_839_; lean_object* v_buckets_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_883_; 
v_size_839_ = lean_ctor_get(v_m_836_, 0);
v_buckets_840_ = lean_ctor_get(v_m_836_, 1);
v_isSharedCheck_883_ = !lean_is_exclusive(v_m_836_);
if (v_isSharedCheck_883_ == 0)
{
v___x_842_ = v_m_836_;
v_isShared_843_ = v_isSharedCheck_883_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_buckets_840_);
lean_inc(v_size_839_);
lean_dec(v_m_836_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_883_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_844_; uint64_t v___x_845_; uint64_t v___x_846_; uint64_t v___x_847_; uint64_t v_fold_848_; uint64_t v___x_849_; uint64_t v___x_850_; uint64_t v___x_851_; size_t v___x_852_; size_t v___x_853_; size_t v___x_854_; size_t v___x_855_; size_t v___x_856_; lean_object* v_bkt_857_; uint8_t v___x_858_; 
v___x_844_ = lean_array_get_size(v_buckets_840_);
v___x_845_ = lean_uint64_of_nat(v_a_837_);
v___x_846_ = 32ULL;
v___x_847_ = lean_uint64_shift_right(v___x_845_, v___x_846_);
v_fold_848_ = lean_uint64_xor(v___x_845_, v___x_847_);
v___x_849_ = 16ULL;
v___x_850_ = lean_uint64_shift_right(v_fold_848_, v___x_849_);
v___x_851_ = lean_uint64_xor(v_fold_848_, v___x_850_);
v___x_852_ = lean_uint64_to_usize(v___x_851_);
v___x_853_ = lean_usize_of_nat(v___x_844_);
v___x_854_ = ((size_t)1ULL);
v___x_855_ = lean_usize_sub(v___x_853_, v___x_854_);
v___x_856_ = lean_usize_land(v___x_852_, v___x_855_);
v_bkt_857_ = lean_array_uget_borrowed(v_buckets_840_, v___x_856_);
v___x_858_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(v_a_837_, v_bkt_857_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; lean_object* v_size_x27_860_; lean_object* v___x_861_; lean_object* v_buckets_x27_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; uint8_t v___x_868_; 
v___x_859_ = lean_unsigned_to_nat(1u);
v_size_x27_860_ = lean_nat_add(v_size_839_, v___x_859_);
lean_dec(v_size_839_);
lean_inc(v_bkt_857_);
v___x_861_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_861_, 0, v_a_837_);
lean_ctor_set(v___x_861_, 1, v_b_838_);
lean_ctor_set(v___x_861_, 2, v_bkt_857_);
v_buckets_x27_862_ = lean_array_uset(v_buckets_840_, v___x_856_, v___x_861_);
v___x_863_ = lean_unsigned_to_nat(4u);
v___x_864_ = lean_nat_mul(v_size_x27_860_, v___x_863_);
v___x_865_ = lean_unsigned_to_nat(3u);
v___x_866_ = lean_nat_div(v___x_864_, v___x_865_);
lean_dec(v___x_864_);
v___x_867_ = lean_array_get_size(v_buckets_x27_862_);
v___x_868_ = lean_nat_dec_le(v___x_866_, v___x_867_);
lean_dec(v___x_866_);
if (v___x_868_ == 0)
{
lean_object* v_val_869_; lean_object* v___x_871_; 
v_val_869_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12___redArg(v_buckets_x27_862_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 1, v_val_869_);
lean_ctor_set(v___x_842_, 0, v_size_x27_860_);
v___x_871_ = v___x_842_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_size_x27_860_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_val_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
else
{
lean_object* v___x_874_; 
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 1, v_buckets_x27_862_);
lean_ctor_set(v___x_842_, 0, v_size_x27_860_);
v___x_874_ = v___x_842_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_size_x27_860_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v_buckets_x27_862_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
else
{
lean_object* v___x_876_; lean_object* v_buckets_x27_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_881_; 
lean_inc(v_bkt_857_);
v___x_876_ = lean_box(0);
v_buckets_x27_877_ = lean_array_uset(v_buckets_840_, v___x_856_, v___x_876_);
v___x_878_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(v_a_837_, v_b_838_, v_bkt_857_);
v___x_879_ = lean_array_uset(v_buckets_x27_877_, v___x_856_, v___x_878_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 1, v___x_879_);
v___x_881_ = v___x_842_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_size_839_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v___x_879_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9(lean_object* v_a_884_, lean_object* v_as_885_, size_t v_i_886_, size_t v_stop_887_){
_start:
{
uint8_t v___x_888_; 
v___x_888_ = lean_usize_dec_eq(v_i_886_, v_stop_887_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; uint8_t v___x_890_; 
v___x_889_ = lean_array_uget_borrowed(v_as_885_, v_i_886_);
v___x_890_ = lean_name_eq(v_a_884_, v___x_889_);
if (v___x_890_ == 0)
{
size_t v___x_891_; size_t v___x_892_; 
v___x_891_ = ((size_t)1ULL);
v___x_892_ = lean_usize_add(v_i_886_, v___x_891_);
v_i_886_ = v___x_892_;
goto _start;
}
else
{
return v___x_890_;
}
}
else
{
uint8_t v___x_894_; 
v___x_894_ = 0;
return v___x_894_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_884_ = stack[0].m_obj;
lean_object* v_as_885_ = stack[1].m_obj;
size_t v_i_886_ = stack[2].m_num;
size_t v_stop_887_ = stack[3].m_num;
uint8_t v_res_895_;
v_res_895_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9(v_a_884_, v_as_885_, v_i_886_, v_stop_887_);
stack->m_num = v_res_895_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9___boxed(lean_object* v_a_896_, lean_object* v_as_897_, lean_object* v_i_898_, lean_object* v_stop_899_){
_start:
{
size_t v_i_boxed_900_; size_t v_stop_boxed_901_; uint8_t v_res_902_; lean_object* v_r_903_; 
v_i_boxed_900_ = lean_unbox_usize(v_i_898_);
lean_dec(v_i_898_);
v_stop_boxed_901_ = lean_unbox_usize(v_stop_899_);
lean_dec(v_stop_899_);
v_res_902_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9(v_a_896_, v_as_897_, v_i_boxed_900_, v_stop_boxed_901_);
lean_dec_ref(v_as_897_);
lean_dec(v_a_896_);
v_r_903_ = lean_box(v_res_902_);
return v_r_903_;
}
}
uint8_t l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(lean_object* v_as_904_, lean_object* v_a_905_){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; uint8_t v___x_908_; 
v___x_906_ = lean_unsigned_to_nat(0u);
v___x_907_ = lean_array_get_size(v_as_904_);
v___x_908_ = lean_nat_dec_lt(v___x_906_, v___x_907_);
if (v___x_908_ == 0)
{
return v___x_908_;
}
else
{
if (v___x_908_ == 0)
{
return v___x_908_;
}
else
{
size_t v___x_909_; size_t v___x_910_; uint8_t v___x_911_; 
v___x_909_ = ((size_t)0ULL);
v___x_910_ = lean_usize_of_nat(v___x_907_);
v___x_911_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9(v_a_905_, v_as_904_, v___x_909_, v___x_910_);
return v___x_911_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_904_ = stack[0].m_obj;
lean_object* v_a_905_ = stack[1].m_obj;
uint8_t v_res_912_;
v_res_912_ = l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(v_as_904_, v_a_905_);
stack->m_num = v_res_912_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4___boxed(lean_object* v_as_913_, lean_object* v_a_914_){
_start:
{
uint8_t v_res_915_; lean_object* v_r_916_; 
v_res_915_ = l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(v_as_913_, v_a_914_);
lean_dec(v_a_914_);
lean_dec_ref(v_as_913_);
v_r_916_ = lean_box(v_res_915_);
return v_r_916_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(lean_object* v_a_917_, lean_object* v_fallback_918_, lean_object* v_x_919_){
_start:
{
if (lean_obj_tag(v_x_919_) == 0)
{
lean_inc(v_fallback_918_);
return v_fallback_918_;
}
else
{
lean_object* v_key_920_; lean_object* v_value_921_; lean_object* v_tail_922_; uint8_t v___x_923_; 
v_key_920_ = lean_ctor_get(v_x_919_, 0);
v_value_921_ = lean_ctor_get(v_x_919_, 1);
v_tail_922_ = lean_ctor_get(v_x_919_, 2);
v___x_923_ = lean_nat_dec_eq(v_key_920_, v_a_917_);
if (v___x_923_ == 0)
{
v_x_919_ = v_tail_922_;
goto _start;
}
else
{
lean_inc(v_value_921_);
return v_value_921_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg___boxed(lean_object* v_a_925_, lean_object* v_fallback_926_, lean_object* v_x_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(v_a_925_, v_fallback_926_, v_x_927_);
lean_dec(v_x_927_);
lean_dec(v_fallback_926_);
lean_dec(v_a_925_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(lean_object* v_m_929_, lean_object* v_a_930_, lean_object* v_fallback_931_){
_start:
{
lean_object* v_buckets_932_; lean_object* v___x_933_; uint64_t v___x_934_; uint64_t v___x_935_; uint64_t v___x_936_; uint64_t v_fold_937_; uint64_t v___x_938_; uint64_t v___x_939_; uint64_t v___x_940_; size_t v___x_941_; size_t v___x_942_; size_t v___x_943_; size_t v___x_944_; size_t v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v_buckets_932_ = lean_ctor_get(v_m_929_, 1);
v___x_933_ = lean_array_get_size(v_buckets_932_);
v___x_934_ = lean_uint64_of_nat(v_a_930_);
v___x_935_ = 32ULL;
v___x_936_ = lean_uint64_shift_right(v___x_934_, v___x_935_);
v_fold_937_ = lean_uint64_xor(v___x_934_, v___x_936_);
v___x_938_ = 16ULL;
v___x_939_ = lean_uint64_shift_right(v_fold_937_, v___x_938_);
v___x_940_ = lean_uint64_xor(v_fold_937_, v___x_939_);
v___x_941_ = lean_uint64_to_usize(v___x_940_);
v___x_942_ = lean_usize_of_nat(v___x_933_);
v___x_943_ = ((size_t)1ULL);
v___x_944_ = lean_usize_sub(v___x_942_, v___x_943_);
v___x_945_ = lean_usize_land(v___x_941_, v___x_944_);
v___x_946_ = lean_array_uget_borrowed(v_buckets_932_, v___x_945_);
v___x_947_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(v_a_930_, v_fallback_931_, v___x_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg___boxed(lean_object* v_m_948_, lean_object* v_a_949_, lean_object* v_fallback_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(v_m_948_, v_a_949_, v_fallback_950_);
lean_dec(v_fallback_950_);
lean_dec(v_a_949_);
lean_dec_ref(v_m_948_);
return v_res_951_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(lean_object* v_as_954_, size_t v_sz_955_, size_t v_i_956_, lean_object* v_b_957_){
_start:
{
lean_object* v_a_960_; uint8_t v___x_964_; 
v___x_964_ = lean_usize_dec_lt(v_i_956_, v_sz_955_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; 
v___x_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_965_, 0, v_b_957_);
return v___x_965_;
}
else
{
lean_object* v_a_966_; lean_object* v_fst_967_; lean_object* v_snd_968_; lean_object* v___x_969_; lean_object* v___x_970_; uint8_t v___x_971_; 
v_a_966_ = lean_array_uget_borrowed(v_as_954_, v_i_956_);
v_fst_967_ = lean_ctor_get(v_a_966_, 0);
v_snd_968_ = lean_ctor_get(v_a_966_, 1);
v___x_969_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___closed__0));
v___x_970_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(v_b_957_, v_fst_967_, v___x_969_);
v___x_971_ = l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(v___x_970_, v_snd_968_);
if (v___x_971_ == 0)
{
lean_object* v___x_972_; lean_object* v___x_973_; 
lean_inc(v_snd_968_);
v___x_972_ = lean_array_push(v___x_970_, v_snd_968_);
lean_inc(v_fst_967_);
v___x_973_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(v_b_957_, v_fst_967_, v___x_972_);
v_a_960_ = v___x_973_;
goto v___jp_959_;
}
else
{
lean_dec(v___x_970_);
v_a_960_ = v_b_957_;
goto v___jp_959_;
}
}
v___jp_959_:
{
size_t v___x_961_; size_t v___x_962_; 
v___x_961_ = ((size_t)1ULL);
v___x_962_ = lean_usize_add(v_i_956_, v___x_961_);
v_i_956_ = v___x_962_;
v_b_957_ = v_a_960_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_954_ = stack[0].m_obj;
size_t v_sz_955_ = stack[1].m_num;
size_t v_i_956_ = stack[2].m_num;
lean_object* v_b_957_ = stack[3].m_obj;
lean_object* v_res_974_;
v_res_974_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(v_as_954_, v_sz_955_, v_i_956_, v_b_957_);
stack->m_obj
 = v_res_974_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___boxed(lean_object* v_as_975_, lean_object* v_sz_976_, lean_object* v_i_977_, lean_object* v_b_978_, lean_object* v___y_979_){
_start:
{
size_t v_sz_boxed_980_; size_t v_i_boxed_981_; lean_object* v_res_982_; 
v_sz_boxed_980_ = lean_unbox_usize(v_sz_976_);
lean_dec(v_sz_976_);
v_i_boxed_981_ = lean_unbox_usize(v_i_977_);
lean_dec(v_i_977_);
v_res_982_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(v_as_975_, v_sz_boxed_980_, v_i_boxed_981_, v_b_978_);
lean_dec_ref(v_as_975_);
return v_res_982_;
}
}
lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(lean_object* v_s_983_){
_start:
{
lean_object* v___x_985_; lean_object* v_putStr_986_; lean_object* v___x_987_; 
v___x_985_ = lean_get_stdout();
v_putStr_986_ = lean_ctor_get(v___x_985_, 4);
lean_inc_ref(v_putStr_986_);
lean_dec_ref(v___x_985_);
v___x_987_ = lean_apply_2(v_putStr_986_, v_s_983_, lean_box(0));
return v___x_987_;
}
}
LEAN_EXPORT void l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_983_ = stack[0].m_obj;
lean_object* v_res_988_;
v_res_988_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v_s_983_);
stack->m_obj
 = v_res_988_;
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23___boxed(lean_object* v_s_989_, lean_object* v_a_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v_s_989_);
return v_res_991_;
}
}
lean_object* l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(lean_object* v_s_992_){
_start:
{
uint32_t v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_994_ = 10;
v___x_995_ = lean_string_push(v_s_992_, v___x_994_);
v___x_996_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_995_);
return v___x_996_;
}
}
LEAN_EXPORT void l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_992_ = stack[0].m_obj;
lean_object* v_res_997_;
v_res_997_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v_s_992_);
stack->m_obj
 = v_res_997_;
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13___boxed(lean_object* v_s_998_, lean_object* v_a_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v_s_998_);
return v_res_1000_;
}
}
uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(uint8_t v___x_1001_, lean_object* v_a_1002_, lean_object* v_b_1003_){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; 
v___x_1004_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_1002_, v___x_1001_);
v___x_1005_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_b_1003_, v___x_1001_);
v___x_1006_ = lean_string_dec_lt(v___x_1004_, v___x_1005_);
lean_dec_ref(v___x_1005_);
lean_dec_ref(v___x_1004_);
return v___x_1006_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1001_ = stack[0].m_num;
lean_object* v_a_1002_ = stack[1].m_obj;
lean_object* v_b_1003_ = stack[2].m_obj;
uint8_t v_res_1007_;
v_res_1007_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_1001_, v_a_1002_, v_b_1003_);
stack->m_num = v_res_1007_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0___boxed(lean_object* v___x_1008_, lean_object* v_a_1009_, lean_object* v_b_1010_){
_start:
{
uint8_t v___x_11837__boxed_1011_; uint8_t v_res_1012_; lean_object* v_r_1013_; 
v___x_11837__boxed_1011_ = lean_unbox(v___x_1008_);
v_res_1012_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_11837__boxed_1011_, v_a_1009_, v_b_1010_);
v_r_1013_ = lean_box(v_res_1012_);
return v_r_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(lean_object* v___x_1014_, lean_object* v___x_1015_, lean_object* v_hi_1016_, lean_object* v_pivot_1017_, lean_object* v_as_1018_, lean_object* v_i_1019_, lean_object* v_k_1020_){
_start:
{
uint8_t v___x_1021_; 
v___x_1021_ = lean_nat_dec_lt(v_k_1020_, v_hi_1016_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
lean_dec(v_k_1020_);
lean_dec(v_pivot_1017_);
v___x_1022_ = lean_array_fswap(v_as_1018_, v_i_1019_, v_hi_1016_);
v___x_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1023_, 0, v_i_1019_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
return v___x_1023_;
}
else
{
uint8_t v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; uint8_t v___x_1028_; 
v___x_1024_ = lean_nat_dec_lt(v___x_1014_, v___x_1015_);
v___x_1025_ = lean_array_fget_borrowed(v_as_1018_, v_k_1020_);
lean_inc(v___x_1025_);
v___x_1026_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1025_, v___x_1024_);
lean_inc(v_pivot_1017_);
v___x_1027_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pivot_1017_, v___x_1024_);
v___x_1028_ = lean_string_dec_lt(v___x_1026_, v___x_1027_);
lean_dec_ref(v___x_1027_);
lean_dec_ref(v___x_1026_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = lean_unsigned_to_nat(1u);
v___x_1030_ = lean_nat_add(v_k_1020_, v___x_1029_);
lean_dec(v_k_1020_);
v_k_1020_ = v___x_1030_;
goto _start;
}
else
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1032_ = lean_array_fswap(v_as_1018_, v_i_1019_, v_k_1020_);
v___x_1033_ = lean_unsigned_to_nat(1u);
v___x_1034_ = lean_nat_add(v_i_1019_, v___x_1033_);
lean_dec(v_i_1019_);
v___x_1035_ = lean_nat_add(v_k_1020_, v___x_1033_);
lean_dec(v_k_1020_);
v_as_1018_ = v___x_1032_;
v_i_1019_ = v___x_1034_;
v_k_1020_ = v___x_1035_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg___boxed(lean_object* v___x_1037_, lean_object* v___x_1038_, lean_object* v_hi_1039_, lean_object* v_pivot_1040_, lean_object* v_as_1041_, lean_object* v_i_1042_, lean_object* v_k_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(v___x_1037_, v___x_1038_, v_hi_1039_, v_pivot_1040_, v_as_1041_, v_i_1042_, v_k_1043_);
lean_dec(v_hi_1039_);
lean_dec(v___x_1038_);
lean_dec(v___x_1037_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(lean_object* v___x_1045_, lean_object* v___x_1046_, lean_object* v_n_1047_, lean_object* v_as_1048_, lean_object* v_lo_1049_, lean_object* v_hi_1050_){
_start:
{
lean_object* v___y_1052_; uint8_t v___x_1062_; 
v___x_1062_ = lean_nat_dec_lt(v_lo_1049_, v_hi_1050_);
if (v___x_1062_ == 0)
{
lean_dec(v_lo_1049_);
return v_as_1048_;
}
else
{
uint8_t v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v_mid_1066_; lean_object* v___y_1068_; lean_object* v___y_1074_; lean_object* v___x_1079_; lean_object* v___x_1080_; uint8_t v___x_1081_; 
v___x_1063_ = lean_nat_dec_lt(v___x_1045_, v___x_1046_);
v___x_1064_ = lean_nat_add(v_lo_1049_, v_hi_1050_);
v___x_1065_ = lean_unsigned_to_nat(1u);
v_mid_1066_ = lean_nat_shiftr(v___x_1064_, v___x_1065_);
lean_dec(v___x_1064_);
v___x_1079_ = lean_array_fget_borrowed(v_as_1048_, v_mid_1066_);
v___x_1080_ = lean_array_fget_borrowed(v_as_1048_, v_lo_1049_);
lean_inc(v___x_1080_);
lean_inc(v___x_1079_);
v___x_1081_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_1063_, v___x_1079_, v___x_1080_);
if (v___x_1081_ == 0)
{
v___y_1074_ = v_as_1048_;
goto v___jp_1073_;
}
else
{
lean_object* v___x_1082_; 
v___x_1082_ = lean_array_fswap(v_as_1048_, v_lo_1049_, v_mid_1066_);
v___y_1074_ = v___x_1082_;
goto v___jp_1073_;
}
v___jp_1067_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; uint8_t v___x_1071_; 
v___x_1069_ = lean_array_fget_borrowed(v___y_1068_, v_mid_1066_);
v___x_1070_ = lean_array_fget_borrowed(v___y_1068_, v_hi_1050_);
lean_inc(v___x_1070_);
lean_inc(v___x_1069_);
v___x_1071_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_1063_, v___x_1069_, v___x_1070_);
if (v___x_1071_ == 0)
{
lean_dec(v_mid_1066_);
v___y_1052_ = v___y_1068_;
goto v___jp_1051_;
}
else
{
lean_object* v___x_1072_; 
v___x_1072_ = lean_array_fswap(v___y_1068_, v_mid_1066_, v_hi_1050_);
lean_dec(v_mid_1066_);
v___y_1052_ = v___x_1072_;
goto v___jp_1051_;
}
}
v___jp_1073_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; 
v___x_1075_ = lean_array_fget_borrowed(v___y_1074_, v_hi_1050_);
v___x_1076_ = lean_array_fget_borrowed(v___y_1074_, v_lo_1049_);
lean_inc(v___x_1076_);
lean_inc(v___x_1075_);
v___x_1077_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_1063_, v___x_1075_, v___x_1076_);
if (v___x_1077_ == 0)
{
v___y_1068_ = v___y_1074_;
goto v___jp_1067_;
}
else
{
lean_object* v___x_1078_; 
v___x_1078_ = lean_array_fswap(v___y_1074_, v_lo_1049_, v_hi_1050_);
v___y_1068_ = v___x_1078_;
goto v___jp_1067_;
}
}
}
v___jp_1051_:
{
lean_object* v_pivot_1053_; lean_object* v___x_1054_; lean_object* v_fst_1055_; lean_object* v_snd_1056_; uint8_t v___x_1057_; 
v_pivot_1053_ = lean_array_fget(v___y_1052_, v_hi_1050_);
lean_inc_n(v_lo_1049_, 2);
v___x_1054_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(v___x_1045_, v___x_1046_, v_hi_1050_, v_pivot_1053_, v___y_1052_, v_lo_1049_, v_lo_1049_);
v_fst_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_fst_1055_);
v_snd_1056_ = lean_ctor_get(v___x_1054_, 1);
lean_inc(v_snd_1056_);
lean_dec_ref(v___x_1054_);
v___x_1057_ = lean_nat_dec_le(v_hi_1050_, v_fst_1055_);
if (v___x_1057_ == 0)
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1058_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v___x_1045_, v___x_1046_, v_n_1047_, v_snd_1056_, v_lo_1049_, v_fst_1055_);
v___x_1059_ = lean_unsigned_to_nat(1u);
v___x_1060_ = lean_nat_add(v_fst_1055_, v___x_1059_);
lean_dec(v_fst_1055_);
v_as_1048_ = v___x_1058_;
v_lo_1049_ = v___x_1060_;
goto _start;
}
else
{
lean_dec(v_fst_1055_);
lean_dec(v_lo_1049_);
return v_snd_1056_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___boxed(lean_object* v___x_1083_, lean_object* v___x_1084_, lean_object* v_n_1085_, lean_object* v_as_1086_, lean_object* v_lo_1087_, lean_object* v_hi_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v___x_1083_, v___x_1084_, v_n_1085_, v_as_1086_, v_lo_1087_, v_hi_1088_);
lean_dec(v_hi_1088_);
lean_dec(v_n_1085_);
lean_dec(v___x_1084_);
lean_dec(v___x_1083_);
return v_res_1089_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(lean_object* v___x_1092_, lean_object* v___x_1093_, lean_object* v___x_1094_, size_t v_sz_1095_, size_t v_i_1096_, lean_object* v_bs_1097_){
_start:
{
uint8_t v___x_1098_; 
v___x_1098_ = lean_usize_dec_lt(v_i_1096_, v_sz_1095_);
if (v___x_1098_ == 0)
{
lean_dec_ref(v___x_1092_);
return v_bs_1097_;
}
else
{
uint8_t v___x_1099_; lean_object* v_v_1100_; lean_object* v___x_1101_; lean_object* v_bs_x27_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; size_t v___x_1111_; size_t v___x_1112_; lean_object* v___x_1113_; 
v___x_1099_ = lean_nat_dec_lt(v___x_1093_, v___x_1094_);
v_v_1100_ = lean_array_uget(v_bs_1097_, v_i_1096_);
v___x_1101_ = lean_unsigned_to_nat(0u);
v_bs_x27_1102_ = lean_array_uset(v_bs_1097_, v_i_1096_, v___x_1101_);
v___x_1103_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__0));
lean_inc_ref(v___x_1092_);
v___x_1104_ = lean_string_append(v___x_1092_, v___x_1103_);
v___x_1105_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_1100_, v___x_1099_);
v___x_1106_ = lean_string_append(v___x_1104_, v___x_1105_);
lean_dec_ref(v___x_1105_);
v___x_1107_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__1));
v___x_1108_ = lean_string_append(v___x_1106_, v___x_1107_);
v___x_1109_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordedMarker___closed__0));
v___x_1110_ = lean_string_append(v___x_1108_, v___x_1109_);
v___x_1111_ = ((size_t)1ULL);
v___x_1112_ = lean_usize_add(v_i_1096_, v___x_1111_);
v___x_1113_ = lean_array_uset(v_bs_x27_1102_, v_i_1096_, v___x_1110_);
v_i_1096_ = v___x_1112_;
v_bs_1097_ = v___x_1113_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1092_ = stack[0].m_obj;
lean_object* v___x_1093_ = stack[1].m_obj;
lean_object* v___x_1094_ = stack[2].m_obj;
size_t v_sz_1095_ = stack[3].m_num;
size_t v_i_1096_ = stack[4].m_num;
lean_object* v_bs_1097_ = stack[5].m_obj;
lean_object* v_res_1115_;
v_res_1115_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(v___x_1092_, v___x_1093_, v___x_1094_, v_sz_1095_, v_i_1096_, v_bs_1097_);
stack->m_obj
 = v_res_1115_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___boxed(lean_object* v___x_1116_, lean_object* v___x_1117_, lean_object* v___x_1118_, lean_object* v_sz_1119_, lean_object* v_i_1120_, lean_object* v_bs_1121_){
_start:
{
size_t v_sz_boxed_1122_; size_t v_i_boxed_1123_; lean_object* v_res_1124_; 
v_sz_boxed_1122_ = lean_unbox_usize(v_sz_1119_);
lean_dec(v_sz_1119_);
v_i_boxed_1123_ = lean_unbox_usize(v_i_1120_);
lean_dec(v_i_1120_);
v_res_1124_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(v___x_1116_, v___x_1117_, v___x_1118_, v_sz_boxed_1122_, v_i_boxed_1123_, v_bs_1121_);
lean_dec(v___x_1118_);
lean_dec(v___x_1117_);
return v_res_1124_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(lean_object* v_as_1125_, size_t v_sz_1126_, size_t v_i_1127_, lean_object* v_b_1128_){
_start:
{
lean_object* v_a_1131_; uint8_t v___x_1135_; 
v___x_1135_ = lean_usize_dec_lt(v_i_1127_, v_sz_1126_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; 
v___x_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1136_, 0, v_b_1128_);
return v___x_1136_;
}
else
{
lean_object* v_a_1137_; lean_object* v_fst_1138_; lean_object* v_snd_1139_; lean_object* v_fst_1140_; lean_object* v_snd_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1180_; 
v_a_1137_ = lean_array_uget_borrowed(v_as_1125_, v_i_1127_);
v_fst_1138_ = lean_ctor_get(v_a_1137_, 0);
v_snd_1139_ = lean_ctor_get(v_a_1137_, 1);
v_fst_1140_ = lean_ctor_get(v_b_1128_, 0);
v_snd_1141_ = lean_ctor_get(v_b_1128_, 1);
v_isSharedCheck_1180_ = !lean_is_exclusive(v_b_1128_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1143_ = v_b_1128_;
v_isShared_1144_ = v_isSharedCheck_1180_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_snd_1141_);
lean_inc(v_fst_1140_);
lean_dec(v_b_1128_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1180_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; 
v___x_1145_ = lean_unsigned_to_nat(1u);
v___x_1146_ = lean_nat_sub(v_fst_1138_, v___x_1145_);
v___x_1147_ = lean_array_get_size(v_fst_1140_);
v___x_1148_ = lean_nat_dec_lt(v___x_1146_, v___x_1147_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1150_; 
lean_dec(v___x_1146_);
if (v_isShared_1144_ == 0)
{
v___x_1150_ = v___x_1143_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_fst_1140_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_snd_1141_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
v_a_1131_ = v___x_1150_;
goto v___jp_1130_;
}
}
else
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___y_1156_; lean_object* v___x_1169_; lean_object* v___y_1171_; lean_object* v___y_1172_; uint8_t v___x_1174_; 
v___x_1152_ = lean_unsigned_to_nat(0u);
v___x_1153_ = lean_array_fget_borrowed(v_fst_1140_, v___x_1146_);
v___x_1154_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace(v___x_1153_);
v___x_1169_ = lean_array_get_size(v_snd_1139_);
v___x_1174_ = lean_nat_dec_eq(v___x_1169_, v___x_1152_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1175_; lean_object* v___y_1177_; uint8_t v___x_1179_; 
v___x_1175_ = lean_nat_sub(v___x_1169_, v___x_1145_);
v___x_1179_ = lean_nat_dec_le(v___x_1152_, v___x_1175_);
if (v___x_1179_ == 0)
{
lean_inc(v___x_1175_);
v___y_1177_ = v___x_1175_;
goto v___jp_1176_;
}
else
{
v___y_1177_ = v___x_1152_;
goto v___jp_1176_;
}
v___jp_1176_:
{
uint8_t v___x_1178_; 
v___x_1178_ = lean_nat_dec_le(v___y_1177_, v___x_1175_);
if (v___x_1178_ == 0)
{
lean_dec(v___x_1175_);
lean_inc(v___y_1177_);
v___y_1171_ = v___y_1177_;
v___y_1172_ = v___y_1177_;
goto v___jp_1170_;
}
else
{
v___y_1171_ = v___y_1177_;
v___y_1172_ = v___x_1175_;
goto v___jp_1170_;
}
}
}
else
{
lean_inc(v_snd_1139_);
v___y_1156_ = v_snd_1139_;
goto v___jp_1155_;
}
v___jp_1155_:
{
size_t v_sz_1157_; size_t v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1167_; 
v_sz_1157_ = lean_array_size(v___y_1156_);
v___x_1158_ = ((size_t)0ULL);
v___x_1159_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(v___x_1154_, v___x_1146_, v___x_1147_, v_sz_1157_, v___x_1158_, v___y_1156_);
lean_inc(v___x_1146_);
v___x_1160_ = l_Array_extract___redArg(v_fst_1140_, v___x_1152_, v___x_1146_);
v___x_1161_ = l_Array_append___redArg(v___x_1160_, v___x_1159_);
v___x_1162_ = l_Array_extract___redArg(v_fst_1140_, v___x_1146_, v___x_1147_);
lean_dec(v_fst_1140_);
v___x_1163_ = l_Array_append___redArg(v___x_1161_, v___x_1162_);
lean_dec_ref(v___x_1162_);
v___x_1164_ = lean_array_get_size(v___x_1159_);
lean_dec_ref(v___x_1159_);
v___x_1165_ = lean_nat_add(v_snd_1141_, v___x_1164_);
lean_dec(v_snd_1141_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 1, v___x_1165_);
lean_ctor_set(v___x_1143_, 0, v___x_1163_);
v___x_1167_ = v___x_1143_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1163_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
v_a_1131_ = v___x_1167_;
goto v___jp_1130_;
}
}
v___jp_1170_:
{
lean_object* v___x_1173_; 
lean_inc(v_snd_1139_);
v___x_1173_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v___x_1146_, v___x_1147_, v___x_1169_, v_snd_1139_, v___y_1171_, v___y_1172_);
lean_dec(v___y_1172_);
v___y_1156_ = v___x_1173_;
goto v___jp_1155_;
}
}
}
}
v___jp_1130_:
{
size_t v___x_1132_; size_t v___x_1133_; 
v___x_1132_ = ((size_t)1ULL);
v___x_1133_ = lean_usize_add(v_i_1127_, v___x_1132_);
v_i_1127_ = v___x_1133_;
v_b_1128_ = v_a_1131_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1125_ = stack[0].m_obj;
size_t v_sz_1126_ = stack[1].m_num;
size_t v_i_1127_ = stack[2].m_num;
lean_object* v_b_1128_ = stack[3].m_obj;
lean_object* v_res_1181_;
v_res_1181_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(v_as_1125_, v_sz_1126_, v_i_1127_, v_b_1128_);
stack->m_obj
 = v_res_1181_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12___boxed(lean_object* v_as_1182_, lean_object* v_sz_1183_, lean_object* v_i_1184_, lean_object* v_b_1185_, lean_object* v___y_1186_){
_start:
{
size_t v_sz_boxed_1187_; size_t v_i_boxed_1188_; lean_object* v_res_1189_; 
v_sz_boxed_1187_ = lean_unbox_usize(v_sz_1183_);
lean_dec(v_sz_1183_);
v_i_boxed_1188_ = lean_unbox_usize(v_i_1184_);
lean_dec(v_i_1184_);
v_res_1189_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(v_as_1182_, v_sz_boxed_1187_, v_i_boxed_1188_, v_b_1185_);
lean_dec_ref(v_as_1182_);
return v_res_1189_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__2(void){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1192_ = lean_box(0);
v___x_1193_ = lean_unsigned_to_nat(16u);
v___x_1194_ = lean_mk_array(v___x_1193_, v___x_1192_);
return v___x_1194_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__3(void){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1195_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__2);
v___x_1196_ = lean_unsigned_to_nat(0u);
v___x_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
lean_ctor_set(v___x_1197_, 1, v___x_1195_);
return v___x_1197_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(lean_object* v_as_1206_, size_t v_sz_1207_, size_t v_i_1208_, lean_object* v_b_1209_){
_start:
{
lean_object* v_a_1212_; uint8_t v___x_1216_; 
v___x_1216_ = lean_usize_dec_lt(v_i_1208_, v_sz_1207_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1217_; 
v___x_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1217_, 0, v_b_1209_);
return v___x_1217_;
}
else
{
lean_object* v_a_1218_; lean_object* v_snd_1219_; lean_object* v_fst_1220_; lean_object* v_snd_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1328_; 
v_a_1218_ = lean_array_uget_borrowed(v_as_1206_, v_i_1208_);
v_snd_1219_ = lean_ctor_get(v_a_1218_, 1);
lean_inc(v_snd_1219_);
v_fst_1220_ = lean_ctor_get(v_snd_1219_, 0);
v_snd_1221_ = lean_ctor_get(v_snd_1219_, 1);
v_isSharedCheck_1328_ = !lean_is_exclusive(v_snd_1219_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1223_ = v_snd_1219_;
v_isShared_1224_ = v_isSharedCheck_1328_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_snd_1221_);
lean_inc(v_fst_1220_);
lean_dec(v_snd_1219_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1328_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1225_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___x_1239_; lean_object* v___x_1240_; size_t v_sz_1241_; size_t v___x_1242_; lean_object* v___x_1243_; 
v___x_1225_ = lean_box(0);
v___x_1239_ = lean_unsigned_to_nat(0u);
v___x_1240_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__3);
v_sz_1241_ = lean_array_size(v_snd_1221_);
v___x_1242_ = ((size_t)0ULL);
v___x_1243_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(v_snd_1221_, v_sz_1241_, v___x_1242_, v___x_1240_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; lean_object* v___x_1245_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_a_1244_);
lean_dec_ref_known(v___x_1243_, 1);
v___x_1245_ = l_IO_FS_readFile(v_fst_1220_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v_size_1249_; lean_object* v_buckets_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; size_t v_sz_1254_; lean_object* v___x_1255_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1285_; lean_object* v___y_1286_; lean_object* v___y_1287_; lean_object* v___y_1288_; lean_object* v___y_1289_; lean_object* v___y_1292_; lean_object* v___y_1293_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1299_; lean_object* v___x_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
lean_dec(v_snd_1221_);
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc_n(v_a_1246_, 2);
lean_dec_ref_known(v___x_1245_, 1);
v___x_1247_ = lean_string_utf8_byte_size(v_a_1246_);
v___x_1248_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1248_, 0, v_a_1246_);
lean_ctor_set(v___x_1248_, 1, v___x_1239_);
lean_ctor_set(v___x_1248_, 2, v___x_1247_);
v_size_1249_ = lean_ctor_get(v_a_1244_, 0);
lean_inc(v_size_1249_);
v_buckets_1250_ = lean_ctor_get(v_a_1244_, 1);
lean_inc_ref(v_buckets_1250_);
lean_dec(v_a_1244_);
v___x_1251_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0);
v___x_1252_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__4));
v___x_1253_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(v_a_1246_, v___x_1248_, v___x_1247_, v___x_1251_, v___x_1252_);
lean_dec_ref_known(v___x_1248_, 3);
v_sz_1254_ = lean_array_size(v___x_1253_);
v___x_1255_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9(v_sz_1254_, v___x_1242_, v___x_1253_);
v___x_1305_ = lean_mk_empty_array_with_capacity(v_size_1249_);
lean_dec(v_size_1249_);
v___x_1306_ = lean_array_get_size(v_buckets_1250_);
v___x_1307_ = lean_nat_dec_lt(v___x_1239_, v___x_1306_);
if (v___x_1307_ == 0)
{
lean_dec_ref(v_buckets_1250_);
v___y_1299_ = v___x_1305_;
goto v___jp_1298_;
}
else
{
size_t v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = lean_usize_of_nat(v___x_1306_);
v___x_1309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(v_buckets_1250_, v___x_1242_, v___x_1308_, v___x_1305_);
lean_dec_ref(v_buckets_1250_);
v___y_1299_ = v___x_1309_;
goto v___jp_1298_;
}
v___jp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 1, v___x_1239_);
lean_ctor_set(v___x_1223_, 0, v___x_1255_);
v___x_1260_ = v___x_1223_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1255_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v___x_1239_);
v___x_1260_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
size_t v_sz_1261_; lean_object* v___x_1262_; 
v_sz_1261_ = lean_array_size(v___y_1258_);
v___x_1262_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(v___y_1258_, v_sz_1261_, v___x_1242_, v___x_1260_);
lean_dec_ref(v___y_1258_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_a_1263_; lean_object* v_fst_1264_; lean_object* v_snd_1265_; uint8_t v___x_1266_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_a_1263_);
lean_dec_ref_known(v___x_1262_, 1);
v_fst_1264_ = lean_ctor_get(v_a_1263_, 0);
lean_inc(v_fst_1264_);
v_snd_1265_ = lean_ctor_get(v_a_1263_, 1);
lean_inc(v_snd_1265_);
lean_dec(v_a_1263_);
v___x_1266_ = lean_nat_dec_lt(v___x_1239_, v_snd_1265_);
if (v___x_1266_ == 0)
{
lean_dec(v_snd_1265_);
lean_dec(v_fst_1264_);
lean_dec(v_fst_1220_);
v_a_1212_ = v___x_1225_;
goto v___jp_1211_;
}
else
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; 
v___x_1267_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__5));
lean_inc(v_snd_1265_);
v___x_1268_ = l_Nat_reprFast(v_snd_1265_);
v___x_1269_ = lean_string_append(v___x_1267_, v___x_1268_);
lean_dec_ref(v___x_1268_);
v___x_1270_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__6));
v___x_1271_ = lean_string_append(v___x_1269_, v___x_1270_);
v___x_1272_ = lean_nat_dec_eq(v_snd_1265_, v___y_1257_);
lean_dec(v_snd_1265_);
if (v___x_1272_ == 0)
{
lean_object* v___x_1273_; 
v___x_1273_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__7));
v___y_1227_ = v_fst_1264_;
v___y_1228_ = v___x_1271_;
v___y_1229_ = v___x_1273_;
goto v___jp_1226_;
}
else
{
lean_object* v___x_1274_; 
v___x_1274_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___y_1227_ = v_fst_1264_;
v___y_1228_ = v___x_1271_;
v___y_1229_ = v___x_1274_;
goto v___jp_1226_;
}
}
}
else
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
lean_dec(v_fst_1220_);
v_a_1275_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1277_ = v___x_1262_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1262_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_a_1275_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
}
v___jp_1284_:
{
lean_object* v___x_1290_; 
v___x_1290_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v___y_1287_, v___y_1286_, v___y_1285_, v___y_1289_);
lean_dec(v___y_1289_);
lean_dec(v___y_1287_);
v___y_1257_ = v___y_1288_;
v___y_1258_ = v___x_1290_;
goto v___jp_1256_;
}
v___jp_1291_:
{
uint8_t v___x_1297_; 
v___x_1297_ = lean_nat_dec_le(v___y_1296_, v___y_1294_);
if (v___x_1297_ == 0)
{
lean_dec(v___y_1294_);
lean_inc(v___y_1296_);
v___y_1285_ = v___y_1296_;
v___y_1286_ = v___y_1293_;
v___y_1287_ = v___y_1292_;
v___y_1288_ = v___y_1295_;
v___y_1289_ = v___y_1296_;
goto v___jp_1284_;
}
else
{
v___y_1285_ = v___y_1296_;
v___y_1286_ = v___y_1293_;
v___y_1287_ = v___y_1292_;
v___y_1288_ = v___y_1295_;
v___y_1289_ = v___y_1294_;
goto v___jp_1284_;
}
}
v___jp_1298_:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; uint8_t v___x_1302_; 
v___x_1300_ = lean_unsigned_to_nat(1u);
v___x_1301_ = lean_array_get_size(v___y_1299_);
v___x_1302_ = lean_nat_dec_eq(v___x_1301_, v___x_1239_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1303_ = lean_nat_sub(v___x_1301_, v___x_1300_);
v___x_1304_ = lean_nat_dec_le(v___x_1239_, v___x_1303_);
if (v___x_1304_ == 0)
{
lean_inc(v___x_1303_);
v___y_1292_ = v___x_1301_;
v___y_1293_ = v___y_1299_;
v___y_1294_ = v___x_1303_;
v___y_1295_ = v___x_1300_;
v___y_1296_ = v___x_1303_;
goto v___jp_1291_;
}
else
{
v___y_1292_ = v___x_1301_;
v___y_1293_ = v___y_1299_;
v___y_1294_ = v___x_1303_;
v___y_1295_ = v___x_1300_;
v___y_1296_ = v___x_1239_;
goto v___jp_1291_;
}
}
else
{
v___y_1257_ = v___x_1300_;
v___y_1258_ = v___y_1299_;
goto v___jp_1256_;
}
}
}
else
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
lean_dec_ref_known(v___x_1245_, 1);
lean_dec(v_a_1244_);
lean_del_object(v___x_1223_);
v___x_1310_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__8));
v___x_1311_ = lean_string_append(v___x_1310_, v_fst_1220_);
lean_dec(v_fst_1220_);
v___x_1312_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__9));
v___x_1313_ = lean_string_append(v___x_1311_, v___x_1312_);
v___x_1314_ = lean_array_get_size(v_snd_1221_);
lean_dec(v_snd_1221_);
v___x_1315_ = l_Nat_reprFast(v___x_1314_);
v___x_1316_ = lean_string_append(v___x_1313_, v___x_1315_);
lean_dec_ref(v___x_1315_);
v___x_1317_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__10));
v___x_1318_ = lean_string_append(v___x_1316_, v___x_1317_);
v___x_1319_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_1318_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_dec_ref_known(v___x_1319_, 1);
v_a_1212_ = v___x_1225_;
goto v___jp_1211_;
}
else
{
return v___x_1319_;
}
}
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
lean_del_object(v___x_1223_);
lean_dec(v_snd_1221_);
lean_dec(v_fst_1220_);
v_a_1320_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1243_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1243_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1320_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
v___jp_1226_:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1230_ = lean_string_append(v___y_1228_, v___y_1229_);
v___x_1231_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__0));
v___x_1232_ = lean_string_append(v___x_1230_, v___x_1231_);
v___x_1233_ = lean_string_append(v___x_1232_, v_fst_1220_);
v___x_1234_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_1233_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
lean_dec_ref_known(v___x_1234_, 1);
v___x_1235_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__1));
v___x_1236_ = lean_array_to_list(v___y_1227_);
v___x_1237_ = l_String_intercalate(v___x_1235_, v___x_1236_);
v___x_1238_ = l_IO_FS_writeFile(v_fst_1220_, v___x_1237_);
lean_dec_ref(v___x_1237_);
lean_dec(v_fst_1220_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_dec_ref_known(v___x_1238_, 1);
v_a_1212_ = v___x_1225_;
goto v___jp_1211_;
}
else
{
return v___x_1238_;
}
}
else
{
lean_dec(v___y_1227_);
lean_dec(v_fst_1220_);
return v___x_1234_;
}
}
}
}
v___jp_1211_:
{
size_t v___x_1213_; size_t v___x_1214_; 
v___x_1213_ = ((size_t)1ULL);
v___x_1214_ = lean_usize_add(v_i_1208_, v___x_1213_);
v_i_1208_ = v___x_1214_;
v_b_1209_ = v_a_1212_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1206_ = stack[0].m_obj;
size_t v_sz_1207_ = stack[1].m_num;
size_t v_i_1208_ = stack[2].m_num;
lean_object* v_b_1209_ = stack[3].m_obj;
lean_object* v_res_1329_;
v_res_1329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(v_as_1206_, v_sz_1207_, v_i_1208_, v_b_1209_);
stack->m_obj
 = v_res_1329_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___boxed(lean_object* v_as_1330_, lean_object* v_sz_1331_, lean_object* v_i_1332_, lean_object* v_b_1333_, lean_object* v___y_1334_){
_start:
{
size_t v_sz_boxed_1335_; size_t v_i_boxed_1336_; lean_object* v_res_1337_; 
v_sz_boxed_1335_ = lean_unbox_usize(v_sz_1331_);
lean_dec(v_sz_1331_);
v_i_boxed_1336_ = lean_unbox_usize(v_i_1332_);
lean_dec(v_i_1332_);
v_res_1337_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(v_as_1330_, v_sz_boxed_1335_, v_i_boxed_1336_, v_b_1333_);
lean_dec_ref(v_as_1330_);
return v_res_1337_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(lean_object* v_a_1338_, lean_object* v_x_1339_){
_start:
{
if (lean_obj_tag(v_x_1339_) == 0)
{
uint8_t v___x_1340_; 
v___x_1340_ = 0;
return v___x_1340_;
}
else
{
lean_object* v_key_1341_; lean_object* v_tail_1342_; uint8_t v___x_1343_; 
v_key_1341_ = lean_ctor_get(v_x_1339_, 0);
v_tail_1342_ = lean_ctor_get(v_x_1339_, 2);
v___x_1343_ = lean_string_dec_eq(v_key_1341_, v_a_1338_);
if (v___x_1343_ == 0)
{
v_x_1339_ = v_tail_1342_;
goto _start;
}
else
{
return v___x_1343_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1338_ = stack[0].m_obj;
lean_object* v_x_1339_ = stack[1].m_obj;
uint8_t v_res_1345_;
v_res_1345_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(v_a_1338_, v_x_1339_);
stack->m_num = v_res_1345_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg___boxed(lean_object* v_a_1346_, lean_object* v_x_1347_){
_start:
{
uint8_t v_res_1348_; lean_object* v_r_1349_; 
v_res_1348_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(v_a_1346_, v_x_1347_);
lean_dec(v_x_1347_);
lean_dec_ref(v_a_1346_);
v_r_1349_ = lean_box(v_res_1348_);
return v_r_1349_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(lean_object* v_a_1350_, lean_object* v_b_1351_, lean_object* v_x_1352_){
_start:
{
if (lean_obj_tag(v_x_1352_) == 0)
{
lean_dec(v_b_1351_);
lean_dec_ref(v_a_1350_);
return v_x_1352_;
}
else
{
lean_object* v_key_1353_; lean_object* v_value_1354_; lean_object* v_tail_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1367_; 
v_key_1353_ = lean_ctor_get(v_x_1352_, 0);
v_value_1354_ = lean_ctor_get(v_x_1352_, 1);
v_tail_1355_ = lean_ctor_get(v_x_1352_, 2);
v_isSharedCheck_1367_ = !lean_is_exclusive(v_x_1352_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1357_ = v_x_1352_;
v_isShared_1358_ = v_isSharedCheck_1367_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_tail_1355_);
lean_inc(v_value_1354_);
lean_inc(v_key_1353_);
lean_dec(v_x_1352_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1367_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
uint8_t v___x_1359_; 
v___x_1359_ = lean_string_dec_eq(v_key_1353_, v_a_1350_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; lean_object* v___x_1362_; 
v___x_1360_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(v_a_1350_, v_b_1351_, v_tail_1355_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 2, v___x_1360_);
v___x_1362_ = v___x_1357_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_key_1353_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v_value_1354_);
lean_ctor_set(v_reuseFailAlloc_1363_, 2, v___x_1360_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
else
{
lean_object* v___x_1365_; 
lean_dec(v_value_1354_);
lean_dec(v_key_1353_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 1, v_b_1351_);
lean_ctor_set(v___x_1357_, 0, v_a_1350_);
v___x_1365_ = v___x_1357_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1350_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_b_1351_);
lean_ctor_set(v_reuseFailAlloc_1366_, 2, v_tail_1355_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26___redArg(lean_object* v_x_1368_, lean_object* v_x_1369_){
_start:
{
if (lean_obj_tag(v_x_1369_) == 0)
{
return v_x_1368_;
}
else
{
lean_object* v_key_1370_; lean_object* v_value_1371_; lean_object* v_tail_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1395_; 
v_key_1370_ = lean_ctor_get(v_x_1369_, 0);
v_value_1371_ = lean_ctor_get(v_x_1369_, 1);
v_tail_1372_ = lean_ctor_get(v_x_1369_, 2);
v_isSharedCheck_1395_ = !lean_is_exclusive(v_x_1369_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1374_ = v_x_1369_;
v_isShared_1375_ = v_isSharedCheck_1395_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_tail_1372_);
lean_inc(v_value_1371_);
lean_inc(v_key_1370_);
lean_dec(v_x_1369_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1395_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; uint64_t v___x_1377_; uint64_t v___x_1378_; uint64_t v___x_1379_; uint64_t v_fold_1380_; uint64_t v___x_1381_; uint64_t v___x_1382_; uint64_t v___x_1383_; size_t v___x_1384_; size_t v___x_1385_; size_t v___x_1386_; size_t v___x_1387_; size_t v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1391_; 
v___x_1376_ = lean_array_get_size(v_x_1368_);
v___x_1377_ = lean_string_hash(v_key_1370_);
v___x_1378_ = 32ULL;
v___x_1379_ = lean_uint64_shift_right(v___x_1377_, v___x_1378_);
v_fold_1380_ = lean_uint64_xor(v___x_1377_, v___x_1379_);
v___x_1381_ = 16ULL;
v___x_1382_ = lean_uint64_shift_right(v_fold_1380_, v___x_1381_);
v___x_1383_ = lean_uint64_xor(v_fold_1380_, v___x_1382_);
v___x_1384_ = lean_uint64_to_usize(v___x_1383_);
v___x_1385_ = lean_usize_of_nat(v___x_1376_);
v___x_1386_ = ((size_t)1ULL);
v___x_1387_ = lean_usize_sub(v___x_1385_, v___x_1386_);
v___x_1388_ = lean_usize_land(v___x_1384_, v___x_1387_);
v___x_1389_ = lean_array_uget_borrowed(v_x_1368_, v___x_1388_);
lean_inc(v___x_1389_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 2, v___x_1389_);
v___x_1391_ = v___x_1374_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_key_1370_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v_value_1371_);
lean_ctor_set(v_reuseFailAlloc_1394_, 2, v___x_1389_);
v___x_1391_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
lean_object* v___x_1392_; 
v___x_1392_ = lean_array_uset(v_x_1368_, v___x_1388_, v___x_1391_);
v_x_1368_ = v___x_1392_;
v_x_1369_ = v_tail_1372_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5___redArg(lean_object* v_i_1396_, lean_object* v_source_1397_, lean_object* v_target_1398_){
_start:
{
lean_object* v___x_1399_; uint8_t v___x_1400_; 
v___x_1399_ = lean_array_get_size(v_source_1397_);
v___x_1400_ = lean_nat_dec_lt(v_i_1396_, v___x_1399_);
if (v___x_1400_ == 0)
{
lean_dec_ref(v_source_1397_);
lean_dec(v_i_1396_);
return v_target_1398_;
}
else
{
lean_object* v_es_1401_; lean_object* v___x_1402_; lean_object* v_source_1403_; lean_object* v_target_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v_es_1401_ = lean_array_fget(v_source_1397_, v_i_1396_);
v___x_1402_ = lean_box(0);
v_source_1403_ = lean_array_fset(v_source_1397_, v_i_1396_, v___x_1402_);
v_target_1404_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26___redArg(v_target_1398_, v_es_1401_);
v___x_1405_ = lean_unsigned_to_nat(1u);
v___x_1406_ = lean_nat_add(v_i_1396_, v___x_1405_);
lean_dec(v_i_1396_);
v_i_1396_ = v___x_1406_;
v_source_1397_ = v_source_1403_;
v_target_1398_ = v_target_1404_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3___redArg(lean_object* v_data_1408_){
_start:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v_nbuckets_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1409_ = lean_array_get_size(v_data_1408_);
v___x_1410_ = lean_unsigned_to_nat(2u);
v_nbuckets_1411_ = lean_nat_mul(v___x_1409_, v___x_1410_);
v___x_1412_ = lean_unsigned_to_nat(0u);
v___x_1413_ = lean_box(0);
v___x_1414_ = lean_mk_array(v_nbuckets_1411_, v___x_1413_);
v___x_1415_ = lean_array_propagate_mark(v_data_1408_, v___x_1414_);
v___x_1416_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5___redArg(v___x_1412_, v_data_1408_, v___x_1415_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(lean_object* v_m_1417_, lean_object* v_a_1418_, lean_object* v_b_1419_){
_start:
{
lean_object* v_size_1420_; lean_object* v_buckets_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1464_; 
v_size_1420_ = lean_ctor_get(v_m_1417_, 0);
v_buckets_1421_ = lean_ctor_get(v_m_1417_, 1);
v_isSharedCheck_1464_ = !lean_is_exclusive(v_m_1417_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1423_ = v_m_1417_;
v_isShared_1424_ = v_isSharedCheck_1464_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_buckets_1421_);
lean_inc(v_size_1420_);
lean_dec(v_m_1417_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1464_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1425_; uint64_t v___x_1426_; uint64_t v___x_1427_; uint64_t v___x_1428_; uint64_t v_fold_1429_; uint64_t v___x_1430_; uint64_t v___x_1431_; uint64_t v___x_1432_; size_t v___x_1433_; size_t v___x_1434_; size_t v___x_1435_; size_t v___x_1436_; size_t v___x_1437_; lean_object* v_bkt_1438_; uint8_t v___x_1439_; 
v___x_1425_ = lean_array_get_size(v_buckets_1421_);
v___x_1426_ = lean_string_hash(v_a_1418_);
v___x_1427_ = 32ULL;
v___x_1428_ = lean_uint64_shift_right(v___x_1426_, v___x_1427_);
v_fold_1429_ = lean_uint64_xor(v___x_1426_, v___x_1428_);
v___x_1430_ = 16ULL;
v___x_1431_ = lean_uint64_shift_right(v_fold_1429_, v___x_1430_);
v___x_1432_ = lean_uint64_xor(v_fold_1429_, v___x_1431_);
v___x_1433_ = lean_uint64_to_usize(v___x_1432_);
v___x_1434_ = lean_usize_of_nat(v___x_1425_);
v___x_1435_ = ((size_t)1ULL);
v___x_1436_ = lean_usize_sub(v___x_1434_, v___x_1435_);
v___x_1437_ = lean_usize_land(v___x_1433_, v___x_1436_);
v_bkt_1438_ = lean_array_uget_borrowed(v_buckets_1421_, v___x_1437_);
v___x_1439_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(v_a_1418_, v_bkt_1438_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1440_; lean_object* v_size_x27_1441_; lean_object* v___x_1442_; lean_object* v_buckets_x27_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; uint8_t v___x_1449_; 
v___x_1440_ = lean_unsigned_to_nat(1u);
v_size_x27_1441_ = lean_nat_add(v_size_1420_, v___x_1440_);
lean_dec(v_size_1420_);
lean_inc(v_bkt_1438_);
v___x_1442_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1442_, 0, v_a_1418_);
lean_ctor_set(v___x_1442_, 1, v_b_1419_);
lean_ctor_set(v___x_1442_, 2, v_bkt_1438_);
v_buckets_x27_1443_ = lean_array_uset(v_buckets_1421_, v___x_1437_, v___x_1442_);
v___x_1444_ = lean_unsigned_to_nat(4u);
v___x_1445_ = lean_nat_mul(v_size_x27_1441_, v___x_1444_);
v___x_1446_ = lean_unsigned_to_nat(3u);
v___x_1447_ = lean_nat_div(v___x_1445_, v___x_1446_);
lean_dec(v___x_1445_);
v___x_1448_ = lean_array_get_size(v_buckets_x27_1443_);
v___x_1449_ = lean_nat_dec_le(v___x_1447_, v___x_1448_);
lean_dec(v___x_1447_);
if (v___x_1449_ == 0)
{
lean_object* v_val_1450_; lean_object* v___x_1452_; 
v_val_1450_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3___redArg(v_buckets_x27_1443_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 1, v_val_1450_);
lean_ctor_set(v___x_1423_, 0, v_size_x27_1441_);
v___x_1452_ = v___x_1423_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_size_x27_1441_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v_val_1450_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
else
{
lean_object* v___x_1455_; 
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 1, v_buckets_x27_1443_);
lean_ctor_set(v___x_1423_, 0, v_size_x27_1441_);
v___x_1455_ = v___x_1423_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_size_x27_1441_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v_buckets_x27_1443_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
else
{
lean_object* v___x_1457_; lean_object* v_buckets_x27_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1462_; 
lean_inc(v_bkt_1438_);
v___x_1457_ = lean_box(0);
v_buckets_x27_1458_ = lean_array_uset(v_buckets_1421_, v___x_1437_, v___x_1457_);
v___x_1459_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(v_a_1418_, v_b_1419_, v_bkt_1438_);
v___x_1460_ = lean_array_uset(v_buckets_x27_1458_, v___x_1437_, v___x_1459_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 1, v___x_1460_);
v___x_1462_ = v___x_1423_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_size_1420_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v___x_1460_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(lean_object* v_a_1465_, lean_object* v_fallback_1466_, lean_object* v_x_1467_){
_start:
{
if (lean_obj_tag(v_x_1467_) == 0)
{
lean_inc(v_fallback_1466_);
return v_fallback_1466_;
}
else
{
lean_object* v_key_1468_; lean_object* v_value_1469_; lean_object* v_tail_1470_; uint8_t v___x_1471_; 
v_key_1468_ = lean_ctor_get(v_x_1467_, 0);
v_value_1469_ = lean_ctor_get(v_x_1467_, 1);
v_tail_1470_ = lean_ctor_get(v_x_1467_, 2);
v___x_1471_ = lean_string_dec_eq(v_key_1468_, v_a_1465_);
if (v___x_1471_ == 0)
{
v_x_1467_ = v_tail_1470_;
goto _start;
}
else
{
lean_inc(v_value_1469_);
return v_value_1469_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg___boxed(lean_object* v_a_1473_, lean_object* v_fallback_1474_, lean_object* v_x_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(v_a_1473_, v_fallback_1474_, v_x_1475_);
lean_dec(v_x_1475_);
lean_dec(v_fallback_1474_);
lean_dec_ref(v_a_1473_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(lean_object* v_m_1477_, lean_object* v_a_1478_, lean_object* v_fallback_1479_){
_start:
{
lean_object* v_buckets_1480_; lean_object* v___x_1481_; uint64_t v___x_1482_; uint64_t v___x_1483_; uint64_t v___x_1484_; uint64_t v_fold_1485_; uint64_t v___x_1486_; uint64_t v___x_1487_; uint64_t v___x_1488_; size_t v___x_1489_; size_t v___x_1490_; size_t v___x_1491_; size_t v___x_1492_; size_t v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v_buckets_1480_ = lean_ctor_get(v_m_1477_, 1);
v___x_1481_ = lean_array_get_size(v_buckets_1480_);
v___x_1482_ = lean_string_hash(v_a_1478_);
v___x_1483_ = 32ULL;
v___x_1484_ = lean_uint64_shift_right(v___x_1482_, v___x_1483_);
v_fold_1485_ = lean_uint64_xor(v___x_1482_, v___x_1484_);
v___x_1486_ = 16ULL;
v___x_1487_ = lean_uint64_shift_right(v_fold_1485_, v___x_1486_);
v___x_1488_ = lean_uint64_xor(v_fold_1485_, v___x_1487_);
v___x_1489_ = lean_uint64_to_usize(v___x_1488_);
v___x_1490_ = lean_usize_of_nat(v___x_1481_);
v___x_1491_ = ((size_t)1ULL);
v___x_1492_ = lean_usize_sub(v___x_1490_, v___x_1491_);
v___x_1493_ = lean_usize_land(v___x_1489_, v___x_1492_);
v___x_1494_ = lean_array_uget_borrowed(v_buckets_1480_, v___x_1493_);
v___x_1495_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(v_a_1478_, v_fallback_1479_, v___x_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg___boxed(lean_object* v_m_1496_, lean_object* v_a_1497_, lean_object* v_fallback_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(v_m_1496_, v_a_1497_, v_fallback_1498_);
lean_dec(v_fallback_1498_);
lean_dec_ref(v_a_1497_);
lean_dec_ref(v_m_1496_);
return v_res_1499_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(lean_object* v_as_1502_, size_t v_sz_1503_, size_t v_i_1504_, lean_object* v_b_1505_){
_start:
{
uint8_t v___x_1507_; 
v___x_1507_ = lean_usize_dec_lt(v_i_1504_, v_sz_1503_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1508_; 
v___x_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1508_, 0, v_b_1505_);
return v___x_1508_;
}
else
{
lean_object* v_a_1509_; lean_object* v_file_1510_; lean_object* v_pos_1511_; lean_object* v_option_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v_fst_1516_; lean_object* v_snd_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1538_; 
v_a_1509_ = lean_array_uget_borrowed(v_as_1502_, v_i_1504_);
v_file_1510_ = lean_ctor_get(v_a_1509_, 0);
v_pos_1511_ = lean_ctor_get(v_a_1509_, 1);
lean_inc_ref(v_pos_1511_);
v_option_1512_ = lean_ctor_get(v_a_1509_, 2);
v___x_1513_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___closed__0));
lean_inc_ref(v_file_1510_);
v___x_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1514_, 0, v_file_1510_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
v___x_1515_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(v_b_1505_, v_file_1510_, v___x_1514_);
lean_dec_ref_known(v___x_1514_, 2);
v_fst_1516_ = lean_ctor_get(v___x_1515_, 0);
v_snd_1517_ = lean_ctor_get(v___x_1515_, 1);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1519_ = v___x_1515_;
v_isShared_1520_ = v_isSharedCheck_1538_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_snd_1517_);
lean_inc(v_fst_1516_);
lean_dec(v___x_1515_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1538_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v_line_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1536_; 
v_line_1521_ = lean_ctor_get(v_pos_1511_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v_pos_1511_);
if (v_isSharedCheck_1536_ == 0)
{
lean_object* v_unused_1537_; 
v_unused_1537_ = lean_ctor_get(v_pos_1511_, 1);
lean_dec(v_unused_1537_);
v___x_1523_ = v_pos_1511_;
v_isShared_1524_ = v_isSharedCheck_1536_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_line_1521_);
lean_dec(v_pos_1511_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1536_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
lean_inc(v_option_1512_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 1, v_option_1512_);
lean_ctor_set(v___x_1519_, 0, v_line_1521_);
v___x_1526_ = v___x_1519_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_line_1521_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v_option_1512_);
v___x_1526_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
lean_object* v___x_1527_; lean_object* v___x_1529_; 
v___x_1527_ = lean_array_push(v_snd_1517_, v___x_1526_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 1, v___x_1527_);
lean_ctor_set(v___x_1523_, 0, v_fst_1516_);
v___x_1529_ = v___x_1523_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_fst_1516_);
lean_ctor_set(v_reuseFailAlloc_1534_, 1, v___x_1527_);
v___x_1529_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
lean_object* v___x_1530_; size_t v___x_1531_; size_t v___x_1532_; 
lean_inc_ref(v_file_1510_);
v___x_1530_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(v_b_1505_, v_file_1510_, v___x_1529_);
v___x_1531_ = ((size_t)1ULL);
v___x_1532_ = lean_usize_add(v_i_1504_, v___x_1531_);
v_i_1504_ = v___x_1532_;
v_b_1505_ = v___x_1530_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1502_ = stack[0].m_obj;
size_t v_sz_1503_ = stack[1].m_num;
size_t v_i_1504_ = stack[2].m_num;
lean_object* v_b_1505_ = stack[3].m_obj;
lean_object* v_res_1539_;
v_res_1539_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(v_as_1502_, v_sz_1503_, v_i_1504_, v_b_1505_);
stack->m_obj
 = v_res_1539_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___boxed(lean_object* v_as_1540_, lean_object* v_sz_1541_, lean_object* v_i_1542_, lean_object* v_b_1543_, lean_object* v___y_1544_){
_start:
{
size_t v_sz_boxed_1545_; size_t v_i_boxed_1546_; lean_object* v_res_1547_; 
v_sz_boxed_1545_ = lean_unbox_usize(v_sz_1541_);
lean_dec(v_sz_1541_);
v_i_boxed_1546_ = lean_unbox_usize(v_i_1542_);
lean_dec(v_i_1542_);
v_res_1547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(v_as_1540_, v_sz_boxed_1545_, v_i_boxed_1546_, v_b_1543_);
lean_dec_ref(v_as_1540_);
return v_res_1547_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0(void){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1548_ = lean_box(0);
v___x_1549_ = lean_unsigned_to_nat(16u);
v___x_1550_ = lean_mk_array(v___x_1549_, v___x_1548_);
return v___x_1550_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1(void){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v_byFile_1553_; 
v___x_1551_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0);
v___x_1552_ = lean_unsigned_to_nat(0u);
v_byFile_1553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byFile_1553_, 0, v___x_1552_);
lean_ctor_set(v_byFile_1553_, 1, v___x_1551_);
return v_byFile_1553_;
}
}
lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(lean_object* v_records_1554_){
_start:
{
lean_object* v___x_1556_; lean_object* v_byFile_1557_; size_t v_sz_1558_; size_t v___x_1559_; lean_object* v___x_1560_; 
v___x_1556_ = lean_unsigned_to_nat(0u);
v_byFile_1557_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1);
v_sz_1558_ = lean_array_size(v_records_1554_);
v___x_1559_ = ((size_t)0ULL);
v___x_1560_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(v_records_1554_, v_sz_1558_, v___x_1559_, v_byFile_1557_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; lean_object* v___y_1563_; lean_object* v_size_1575_; lean_object* v_buckets_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; uint8_t v___x_1579_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1561_);
lean_dec_ref_known(v___x_1560_, 1);
v_size_1575_ = lean_ctor_get(v_a_1561_, 0);
lean_inc(v_size_1575_);
v_buckets_1576_ = lean_ctor_get(v_a_1561_, 1);
lean_inc_ref(v_buckets_1576_);
lean_dec(v_a_1561_);
v___x_1577_ = lean_mk_empty_array_with_capacity(v_size_1575_);
lean_dec(v_size_1575_);
v___x_1578_ = lean_array_get_size(v_buckets_1576_);
v___x_1579_ = lean_nat_dec_lt(v___x_1556_, v___x_1578_);
if (v___x_1579_ == 0)
{
lean_dec_ref(v_buckets_1576_);
v___y_1563_ = v___x_1577_;
goto v___jp_1562_;
}
else
{
size_t v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = lean_usize_of_nat(v___x_1578_);
v___x_1581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(v_buckets_1576_, v___x_1559_, v___x_1580_, v___x_1577_);
lean_dec_ref(v_buckets_1576_);
v___y_1563_ = v___x_1581_;
goto v___jp_1562_;
}
v___jp_1562_:
{
lean_object* v___x_1564_; size_t v_sz_1565_; lean_object* v___x_1566_; 
v___x_1564_ = lean_box(0);
v_sz_1565_ = lean_array_size(v___y_1563_);
v___x_1566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(v___y_1563_, v_sz_1565_, v___x_1559_, v___x_1564_);
lean_dec_ref(v___y_1563_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1573_ == 0)
{
lean_object* v_unused_1574_; 
v_unused_1574_ = lean_ctor_get(v___x_1566_, 0);
lean_dec(v_unused_1574_);
v___x_1568_ = v___x_1566_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_dec(v___x_1566_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 0, v___x_1564_);
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1564_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
else
{
return v___x_1566_;
}
}
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
v_a_1582_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1560_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1560_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_0interp(lean_interpreter_value* stack)
{
lean_object* v_records_1554_ = stack[0].m_obj;
lean_object* v_res_1590_;
v_res_1590_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(v_records_1554_);
stack->m_obj
 = v_res_1590_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___boxed(lean_object* v_records_1591_, lean_object* v_a_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(v_records_1591_);
lean_dec_ref(v_records_1591_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0(lean_object* v_00_u03b2_1594_, lean_object* v_m_1595_, lean_object* v_a_1596_, lean_object* v_fallback_1597_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(v_m_1595_, v_a_1596_, v_fallback_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___boxed(lean_object* v_00_u03b2_1599_, lean_object* v_m_1600_, lean_object* v_a_1601_, lean_object* v_fallback_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0(v_00_u03b2_1599_, v_m_1600_, v_a_1601_, v_fallback_1602_);
lean_dec(v_fallback_1602_);
lean_dec_ref(v_a_1601_);
lean_dec_ref(v_m_1600_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1(lean_object* v_00_u03b2_1604_, lean_object* v_m_1605_, lean_object* v_a_1606_, lean_object* v_b_1607_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(v_m_1605_, v_a_1606_, v_b_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3(lean_object* v_00_u03b2_1609_, lean_object* v_m_1610_, lean_object* v_a_1611_, lean_object* v_fallback_1612_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(v_m_1610_, v_a_1611_, v_fallback_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___boxed(lean_object* v_00_u03b2_1614_, lean_object* v_m_1615_, lean_object* v_a_1616_, lean_object* v_fallback_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3(v_00_u03b2_1614_, v_m_1615_, v_a_1616_, v_fallback_1617_);
lean_dec(v_fallback_1617_);
lean_dec(v_a_1616_);
lean_dec_ref(v_m_1615_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5(lean_object* v_00_u03b2_1619_, lean_object* v_m_1620_, lean_object* v_a_1621_, lean_object* v_b_1622_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(v_m_1620_, v_a_1621_, v_b_1622_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8(lean_object* v_a_1624_, lean_object* v___x_1625_, lean_object* v___x_1626_, lean_object* v_inst_1627_, lean_object* v_R_1628_, lean_object* v_a_1629_, lean_object* v_b_1630_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(v_a_1624_, v___x_1625_, v___x_1626_, v_a_1629_, v_b_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___boxed(lean_object* v_a_1632_, lean_object* v___x_1633_, lean_object* v___x_1634_, lean_object* v_inst_1635_, lean_object* v_R_1636_, lean_object* v_a_1637_, lean_object* v_b_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8(v_a_1632_, v___x_1633_, v___x_1634_, v_inst_1635_, v_R_1636_, v_a_1637_, v_b_1638_);
lean_dec_ref(v___x_1633_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11(lean_object* v___x_1640_, lean_object* v___x_1641_, lean_object* v_n_1642_, lean_object* v_as_1643_, lean_object* v_lo_1644_, lean_object* v_hi_1645_, lean_object* v_w_1646_, lean_object* v_hlo_1647_, lean_object* v_hhi_1648_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v___x_1640_, v___x_1641_, v_n_1642_, v_as_1643_, v_lo_1644_, v_hi_1645_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___boxed(lean_object* v___x_1650_, lean_object* v___x_1651_, lean_object* v_n_1652_, lean_object* v_as_1653_, lean_object* v_lo_1654_, lean_object* v_hi_1655_, lean_object* v_w_1656_, lean_object* v_hlo_1657_, lean_object* v_hhi_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11(v___x_1650_, v___x_1651_, v_n_1652_, v_as_1653_, v_lo_1654_, v_hi_1655_, v_w_1656_, v_hlo_1657_, v_hhi_1658_);
lean_dec(v_hi_1655_);
lean_dec(v_n_1652_);
lean_dec(v___x_1651_);
lean_dec(v___x_1650_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14(lean_object* v_n_1660_, lean_object* v_as_1661_, lean_object* v_lo_1662_, lean_object* v_hi_1663_, lean_object* v_w_1664_, lean_object* v_hlo_1665_, lean_object* v_hhi_1666_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v_n_1660_, v_as_1661_, v_lo_1662_, v_hi_1663_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___boxed(lean_object* v_n_1668_, lean_object* v_as_1669_, lean_object* v_lo_1670_, lean_object* v_hi_1671_, lean_object* v_w_1672_, lean_object* v_hlo_1673_, lean_object* v_hhi_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14(v_n_1668_, v_as_1669_, v_lo_1670_, v_hi_1671_, v_w_1672_, v_hlo_1673_, v_hhi_1674_);
lean_dec(v_hi_1671_);
lean_dec(v_n_1668_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0(lean_object* v_00_u03b2_1676_, lean_object* v_a_1677_, lean_object* v_fallback_1678_, lean_object* v_x_1679_){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(v_a_1677_, v_fallback_1678_, v_x_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1681_, lean_object* v_a_1682_, lean_object* v_fallback_1683_, lean_object* v_x_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0(v_00_u03b2_1681_, v_a_1682_, v_fallback_1683_, v_x_1684_);
lean_dec(v_x_1684_);
lean_dec(v_fallback_1683_);
lean_dec_ref(v_a_1682_);
return v_res_1685_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2(lean_object* v_00_u03b2_1686_, lean_object* v_a_1687_, lean_object* v_x_1688_){
_start:
{
uint8_t v___x_1689_; 
v___x_1689_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(v_a_1687_, v_x_1688_);
return v___x_1689_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1687_ = stack[1].m_obj;
lean_object* v_x_1688_ = stack[2].m_obj;
uint8_t v_res_1690_;
v_res_1690_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2(lean_box(0), v_a_1687_, v_x_1688_);
stack->m_num = v_res_1690_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1691_, lean_object* v_a_1692_, lean_object* v_x_1693_){
_start:
{
uint8_t v_res_1694_; lean_object* v_r_1695_; 
v_res_1694_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2(v_00_u03b2_1691_, v_a_1692_, v_x_1693_);
lean_dec(v_x_1693_);
lean_dec_ref(v_a_1692_);
v_r_1695_ = lean_box(v_res_1694_);
return v_r_1695_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3(lean_object* v_00_u03b2_1696_, lean_object* v_data_1697_){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3___redArg(v_data_1697_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4(lean_object* v_00_u03b2_1699_, lean_object* v_a_1700_, lean_object* v_b_1701_, lean_object* v_x_1702_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(v_a_1700_, v_b_1701_, v_x_1702_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7(lean_object* v_00_u03b2_1704_, lean_object* v_a_1705_, lean_object* v_fallback_1706_, lean_object* v_x_1707_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(v_a_1705_, v_fallback_1706_, v_x_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___boxed(lean_object* v_00_u03b2_1709_, lean_object* v_a_1710_, lean_object* v_fallback_1711_, lean_object* v_x_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7(v_00_u03b2_1709_, v_a_1710_, v_fallback_1711_, v_x_1712_);
lean_dec(v_x_1712_);
lean_dec(v_fallback_1711_);
lean_dec(v_a_1710_);
return v_res_1713_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11(lean_object* v_00_u03b2_1714_, lean_object* v_a_1715_, lean_object* v_x_1716_){
_start:
{
uint8_t v___x_1717_; 
v___x_1717_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(v_a_1715_, v_x_1716_);
return v___x_1717_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1715_ = stack[1].m_obj;
lean_object* v_x_1716_ = stack[2].m_obj;
uint8_t v_res_1718_;
v_res_1718_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11(lean_box(0), v_a_1715_, v_x_1716_);
stack->m_num = v_res_1718_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___boxed(lean_object* v_00_u03b2_1719_, lean_object* v_a_1720_, lean_object* v_x_1721_){
_start:
{
uint8_t v_res_1722_; lean_object* v_r_1723_; 
v_res_1722_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11(v_00_u03b2_1719_, v_a_1720_, v_x_1721_);
lean_dec(v_x_1721_);
lean_dec(v_a_1720_);
v_r_1723_ = lean_box(v_res_1722_);
return v_r_1723_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12(lean_object* v_00_u03b2_1724_, lean_object* v_data_1725_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12___redArg(v_data_1725_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13(lean_object* v_00_u03b2_1727_, lean_object* v_a_1728_, lean_object* v_b_1729_, lean_object* v_x_1730_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(v_a_1728_, v_b_1729_, v_x_1730_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20(lean_object* v___x_1732_, lean_object* v___x_1733_, lean_object* v_n_1734_, lean_object* v_lo_1735_, lean_object* v_hi_1736_, lean_object* v_hhi_1737_, lean_object* v_pivot_1738_, lean_object* v_as_1739_, lean_object* v_i_1740_, lean_object* v_k_1741_, lean_object* v_ilo_1742_, lean_object* v_ik_1743_, lean_object* v_w_1744_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(v___x_1732_, v___x_1733_, v_hi_1736_, v_pivot_1738_, v_as_1739_, v_i_1740_, v_k_1741_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___boxed(lean_object* v___x_1746_, lean_object* v___x_1747_, lean_object* v_n_1748_, lean_object* v_lo_1749_, lean_object* v_hi_1750_, lean_object* v_hhi_1751_, lean_object* v_pivot_1752_, lean_object* v_as_1753_, lean_object* v_i_1754_, lean_object* v_k_1755_, lean_object* v_ilo_1756_, lean_object* v_ik_1757_, lean_object* v_w_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20(v___x_1746_, v___x_1747_, v_n_1748_, v_lo_1749_, v_hi_1750_, v_hhi_1751_, v_pivot_1752_, v_as_1753_, v_i_1754_, v_k_1755_, v_ilo_1756_, v_ik_1757_, v_w_1758_);
lean_dec(v_hi_1750_);
lean_dec(v_lo_1749_);
lean_dec(v_n_1748_);
lean_dec(v___x_1747_);
lean_dec(v___x_1746_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25(lean_object* v_n_1760_, lean_object* v_lo_1761_, lean_object* v_hi_1762_, lean_object* v_hhi_1763_, lean_object* v_pivot_1764_, lean_object* v_as_1765_, lean_object* v_i_1766_, lean_object* v_k_1767_, lean_object* v_ilo_1768_, lean_object* v_ik_1769_, lean_object* v_w_1770_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(v_hi_1762_, v_pivot_1764_, v_as_1765_, v_i_1766_, v_k_1767_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___boxed(lean_object* v_n_1772_, lean_object* v_lo_1773_, lean_object* v_hi_1774_, lean_object* v_hhi_1775_, lean_object* v_pivot_1776_, lean_object* v_as_1777_, lean_object* v_i_1778_, lean_object* v_k_1779_, lean_object* v_ilo_1780_, lean_object* v_ik_1781_, lean_object* v_w_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25(v_n_1772_, v_lo_1773_, v_hi_1774_, v_hhi_1775_, v_pivot_1776_, v_as_1777_, v_i_1778_, v_k_1779_, v_ilo_1780_, v_ik_1781_, v_w_1782_);
lean_dec_ref(v_pivot_1776_);
lean_dec(v_hi_1774_);
lean_dec(v_lo_1773_);
lean_dec(v_n_1772_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_1784_, lean_object* v_i_1785_, lean_object* v_source_1786_, lean_object* v_target_1787_){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5___redArg(v_i_1785_, v_source_1786_, v_target_1787_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15(lean_object* v_00_u03b2_1789_, lean_object* v_i_1790_, lean_object* v_source_1791_, lean_object* v_target_1792_){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15___redArg(v_i_1790_, v_source_1791_, v_target_1792_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26(lean_object* v_00_u03b2_1794_, lean_object* v_x_1795_, lean_object* v_x_1796_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26___redArg(v_x_1795_, v_x_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33(lean_object* v_00_u03b2_1798_, lean_object* v_x_1799_, lean_object* v_x_1800_){
_start:
{
lean_object* v___x_1801_; 
v___x_1801_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33___redArg(v_x_1799_, v_x_1800_);
return v___x_1801_;
}
}
lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(lean_object* v_declName_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v_env_1807_; lean_object* v___x_1808_; lean_object* v_env_1809_; lean_object* v___x_1810_; lean_object* v_toEnvExtension_1811_; lean_object* v_asyncMode_1812_; uint8_t v___x_1813_; lean_object* v___x_1814_; 
v___x_1805_ = l_Lean_instInhabitedDeclarationRanges_default;
v___x_1806_ = lean_st_ref_get(v___y_1803_);
v_env_1807_ = lean_ctor_get(v___x_1806_, 0);
lean_inc_ref(v_env_1807_);
lean_dec(v___x_1806_);
v___x_1808_ = lean_st_ref_get(v___y_1803_);
v_env_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc_ref(v_env_1809_);
lean_dec(v___x_1808_);
v___x_1810_ = l_Lean_declRangeExt;
v_toEnvExtension_1811_ = lean_ctor_get(v___x_1810_, 0);
v_asyncMode_1812_ = lean_ctor_get(v_toEnvExtension_1811_, 2);
v___x_1813_ = 0;
lean_inc(v_declName_1802_);
v___x_1814_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1805_, v___x_1810_, v_env_1807_, v_declName_1802_, v_asyncMode_1812_, v___x_1813_);
if (lean_obj_tag(v___x_1814_) == 0)
{
uint8_t v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1815_ = 1;
v___x_1816_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1805_, v___x_1810_, v_env_1809_, v_declName_1802_, v_asyncMode_1812_, v___x_1815_);
v___x_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1816_);
return v___x_1817_;
}
else
{
lean_object* v___x_1818_; 
lean_dec_ref(v_env_1809_);
lean_dec(v_declName_1802_);
v___x_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1814_);
return v___x_1818_;
}
}
}
LEAN_EXPORT void l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1802_ = stack[0].m_obj;
lean_object* v___y_1803_ = stack[1].m_obj;
lean_object* v_res_1819_;
v_res_1819_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1802_, v___y_1803_);
stack->m_obj
 = v_res_1819_;
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg___boxed(lean_object* v_declName_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1820_, v___y_1821_);
lean_dec(v___y_1821_);
return v_res_1823_;
}
}
lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(lean_object* v_declName_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v___x_1827_; lean_object* v_env_1828_; uint8_t v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1827_ = lean_st_ref_get(v___y_1825_);
v_env_1828_ = lean_ctor_get(v___x_1827_, 0);
lean_inc_ref(v_env_1828_);
lean_dec(v___x_1827_);
v___x_1829_ = l_Lean_isRecCore(v_env_1828_, v_declName_1824_);
v___x_1830_ = lean_box(v___x_1829_);
v___x_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1830_);
return v___x_1831_;
}
}
LEAN_EXPORT void l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1824_ = stack[0].m_obj;
lean_object* v___y_1825_ = stack[1].m_obj;
lean_object* v_res_1832_;
v_res_1832_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1824_, v___y_1825_);
stack->m_obj
 = v_res_1832_;
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1833_, v___y_1834_);
lean_dec(v___y_1834_);
return v_res_1836_;
}
}
lean_object* l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(lean_object* v_declName_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v_ranges_1842_; lean_object* v___x_1848_; lean_object* v_env_1849_; lean_object* v___x_1850_; lean_object* v_a_1851_; uint8_t v___y_1857_; uint8_t v___x_1861_; 
v___x_1848_ = lean_st_ref_get(v___y_1839_);
v_env_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc_ref_n(v_env_1849_, 2);
lean_dec(v___x_1848_);
lean_inc_n(v_declName_1837_, 2);
v___x_1850_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1837_, v___y_1839_);
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
lean_inc(v_a_1851_);
lean_dec_ref(v___x_1850_);
v___x_1861_ = l_Lean_isAuxRecursor(v_env_1849_, v_declName_1837_);
if (v___x_1861_ == 0)
{
uint8_t v___x_1862_; 
lean_inc(v_declName_1837_);
v___x_1862_ = l_Lean_isNoConfusion(v_env_1849_, v_declName_1837_);
v___y_1857_ = v___x_1862_;
goto v___jp_1856_;
}
else
{
lean_dec_ref(v_env_1849_);
v___y_1857_ = v___x_1861_;
goto v___jp_1856_;
}
v___jp_1841_:
{
if (lean_obj_tag(v_ranges_1842_) == 0)
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1843_ = l_Lean_builtinDeclRanges;
v___x_1844_ = lean_st_ref_get(v___x_1843_);
v___x_1845_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1844_, v_declName_1837_);
lean_dec(v_declName_1837_);
lean_dec(v___x_1844_);
v___x_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
return v___x_1846_;
}
else
{
lean_object* v___x_1847_; 
lean_dec(v_declName_1837_);
v___x_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1847_, 0, v_ranges_1842_);
return v___x_1847_;
}
}
v___jp_1852_:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v_a_1855_; 
v___x_1853_ = l_Lean_Name_getPrefix(v_declName_1837_);
v___x_1854_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v___x_1853_, v___y_1839_);
v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_a_1855_);
lean_dec_ref(v___x_1854_);
v_ranges_1842_ = v_a_1855_;
goto v___jp_1841_;
}
v___jp_1856_:
{
if (v___y_1857_ == 0)
{
uint8_t v___x_1858_; 
v___x_1858_ = lean_unbox(v_a_1851_);
lean_dec(v_a_1851_);
if (v___x_1858_ == 0)
{
lean_object* v___x_1859_; lean_object* v_a_1860_; 
lean_inc(v_declName_1837_);
v___x_1859_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1837_, v___y_1839_);
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_a_1860_);
lean_dec_ref(v___x_1859_);
v_ranges_1842_ = v_a_1860_;
goto v___jp_1841_;
}
else
{
goto v___jp_1852_;
}
}
else
{
lean_dec(v_a_1851_);
goto v___jp_1852_;
}
}
}
}
LEAN_EXPORT void l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1837_ = stack[0].m_obj;
lean_object* v___y_1838_ = stack[1].m_obj;
lean_object* v___y_1839_ = stack[2].m_obj;
lean_object* v_res_1863_;
v_res_1863_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_declName_1837_, v___y_1838_, v___y_1839_);
stack->m_obj
 = v_res_1863_;
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0___boxed(lean_object* v_declName_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_declName_1864_, v___y_1865_, v___y_1866_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
return v_res_1868_;
}
}
lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(lean_object* v_failMod_1869_, lean_object* v_site_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_){
_start:
{
if (lean_obj_tag(v_site_1870_) == 0)
{
lean_object* v_name_1874_; lean_object* v___x_1875_; 
v_name_1874_ = lean_ctor_get(v_site_1870_, 0);
lean_inc(v_name_1874_);
lean_dec_ref_known(v_site_1870_, 1);
v___x_1875_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_name_1874_, v_a_1871_, v_a_1872_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1897_; 
v_a_1876_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1878_ = v___x_1875_;
v_isShared_1879_ = v_isSharedCheck_1897_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1875_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1897_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
if (lean_obj_tag(v_a_1876_) == 0)
{
lean_object* v___x_1880_; lean_object* v___x_1882_; 
v___x_1880_ = lean_box(0);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 0, v___x_1880_);
v___x_1882_ = v___x_1878_;
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
lean_object* v_val_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1896_; 
v_val_1884_ = lean_ctor_get(v_a_1876_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v_a_1876_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1886_ = v_a_1876_;
v_isShared_1887_ = v_isSharedCheck_1896_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_val_1884_);
lean_dec(v_a_1876_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1896_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v_range_1888_; lean_object* v_pos_1889_; lean_object* v___x_1891_; 
v_range_1888_ = lean_ctor_get(v_val_1884_, 0);
lean_inc_ref(v_range_1888_);
lean_dec(v_val_1884_);
v_pos_1889_ = lean_ctor_get(v_range_1888_, 0);
lean_inc_ref(v_pos_1889_);
lean_dec_ref(v_range_1888_);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 0, v_pos_1889_);
v___x_1891_ = v___x_1886_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_pos_1889_);
v___x_1891_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
lean_object* v___x_1893_; 
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 0, v___x_1891_);
v___x_1893_ = v___x_1878_;
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
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
v_a_1898_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1875_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1875_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
else
{
lean_object* v_n_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1937_; 
v_n_1906_ = lean_ctor_get(v_site_1870_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v_site_1870_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1908_ = v_site_1870_;
v_isShared_1909_ = v_isSharedCheck_1937_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_n_1906_);
lean_dec(v_site_1870_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1937_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1910_; lean_object* v_env_1911_; lean_object* v___x_1912_; 
v___x_1910_ = lean_st_ref_get(v_a_1872_);
v_env_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc_ref(v_env_1911_);
lean_dec(v___x_1910_);
v___x_1912_ = l_Lean_getVersoModuleDoc_x3f(v_env_1911_, v_failMod_1869_);
lean_dec_ref(v_env_1911_);
if (lean_obj_tag(v___x_1912_) == 1)
{
lean_object* v_val_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1932_; 
v_val_1913_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1915_ = v___x_1912_;
v_isShared_1916_ = v_isSharedCheck_1932_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_val_1913_);
lean_dec(v___x_1912_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1932_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1917_; uint8_t v___x_1918_; 
v___x_1917_ = lean_array_get_size(v_val_1913_);
v___x_1918_ = lean_nat_dec_lt(v_n_1906_, v___x_1917_);
if (v___x_1918_ == 0)
{
lean_object* v___x_1919_; lean_object* v___x_1921_; 
lean_del_object(v___x_1915_);
lean_dec(v_val_1913_);
lean_dec(v_n_1906_);
v___x_1919_ = lean_box(0);
if (v_isShared_1909_ == 0)
{
lean_ctor_set_tag(v___x_1908_, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1919_);
v___x_1921_ = v___x_1908_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1919_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
else
{
lean_object* v___x_1923_; lean_object* v_declarationRange_1924_; lean_object* v_pos_1925_; lean_object* v___x_1927_; 
v___x_1923_ = lean_array_fget(v_val_1913_, v_n_1906_);
lean_dec(v_n_1906_);
lean_dec(v_val_1913_);
v_declarationRange_1924_ = lean_ctor_get(v___x_1923_, 2);
lean_inc_ref(v_declarationRange_1924_);
lean_dec(v___x_1923_);
v_pos_1925_ = lean_ctor_get(v_declarationRange_1924_, 0);
lean_inc_ref(v_pos_1925_);
lean_dec_ref(v_declarationRange_1924_);
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 0, v_pos_1925_);
v___x_1927_ = v___x_1915_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_pos_1925_);
v___x_1927_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
lean_object* v___x_1929_; 
if (v_isShared_1909_ == 0)
{
lean_ctor_set_tag(v___x_1908_, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1927_);
v___x_1929_ = v___x_1908_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1927_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
}
else
{
lean_object* v___x_1933_; lean_object* v___x_1935_; 
lean_dec(v___x_1912_);
lean_dec(v_n_1906_);
v___x_1933_ = lean_box(0);
if (v_isShared_1909_ == 0)
{
lean_ctor_set_tag(v___x_1908_, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1933_);
v___x_1935_ = v___x_1908_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1933_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_failMod_1869_ = stack[0].m_obj;
lean_object* v_site_1870_ = stack[1].m_obj;
lean_object* v_a_1871_ = stack[2].m_obj;
lean_object* v_a_1872_ = stack[3].m_obj;
lean_object* v_res_1938_;
v_res_1938_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(v_failMod_1869_, v_site_1870_, v_a_1871_, v_a_1872_);
stack->m_obj
 = v_res_1938_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f___boxed(lean_object* v_failMod_1939_, lean_object* v_site_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(v_failMod_1939_, v_site_1940_, v_a_1941_, v_a_1942_);
lean_dec(v_a_1942_);
lean_dec_ref(v_a_1941_);
lean_dec(v_failMod_1939_);
return v_res_1944_;
}
}
lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0(lean_object* v_declName_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v___x_1949_; 
v___x_1949_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1945_, v___y_1947_);
return v___x_1949_;
}
}
LEAN_EXPORT void l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1945_ = stack[0].m_obj;
lean_object* v___y_1946_ = stack[1].m_obj;
lean_object* v___y_1947_ = stack[2].m_obj;
lean_object* v_res_1950_;
v_res_1950_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0(v_declName_1945_, v___y_1946_, v___y_1947_);
stack->m_obj
 = v_res_1950_;
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___boxed(lean_object* v_declName_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0(v_declName_1951_, v___y_1952_, v___y_1953_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
return v_res_1955_;
}
}
lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1(lean_object* v_declName_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v___x_1960_; 
v___x_1960_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1956_, v___y_1958_);
return v___x_1960_;
}
}
LEAN_EXPORT void l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1956_ = stack[0].m_obj;
lean_object* v___y_1957_ = stack[1].m_obj;
lean_object* v___y_1958_ = stack[2].m_obj;
lean_object* v_res_1961_;
v_res_1961_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1(v_declName_1956_, v___y_1957_, v___y_1958_);
stack->m_obj
 = v_res_1961_;
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___boxed(lean_object* v_declName_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1(v_declName_1962_, v___y_1963_, v___y_1964_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(lean_object* v_x_1970_){
_start:
{
if (lean_obj_tag(v_x_1970_) == 0)
{
lean_object* v_name_1971_; lean_object* v___x_1972_; uint8_t v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v_name_1971_ = lean_ctor_get(v_x_1970_, 0);
lean_inc(v_name_1971_);
lean_dec_ref_known(v_x_1970_, 1);
v___x_1972_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__0));
v___x_1973_ = 1;
v___x_1974_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1971_, v___x_1973_);
v___x_1975_ = lean_string_append(v___x_1972_, v___x_1974_);
lean_dec_ref(v___x_1974_);
v___x_1976_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__1));
v___x_1977_ = lean_string_append(v___x_1975_, v___x_1976_);
return v___x_1977_;
}
else
{
lean_object* v_n_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
v_n_1978_ = lean_ctor_get(v_x_1970_, 0);
lean_inc(v_n_1978_);
lean_dec_ref_known(v_x_1970_, 1);
v___x_1979_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__2));
v___x_1980_ = lean_unsigned_to_nat(1u);
v___x_1981_ = lean_nat_add(v_n_1978_, v___x_1980_);
lean_dec(v_n_1978_);
v___x_1982_ = l_Nat_reprFast(v___x_1981_);
v___x_1983_ = lean_string_append(v___x_1979_, v___x_1982_);
lean_dec_ref(v___x_1982_);
return v___x_1983_;
}
}
}
lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(lean_object* v_o_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v_env_1989_; lean_object* v___x_1990_; lean_object* v_toEnvExtension_1991_; lean_object* v_asyncMode_1992_; lean_object* v___x_1993_; uint8_t v___x_1994_; lean_object* v___x_1995_; lean_object* v_merged_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2004_; 
v___x_1987_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1988_ = lean_st_ref_get(v___y_1985_);
v_env_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc_ref(v_env_1989_);
lean_dec(v___x_1988_);
v___x_1990_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1991_ = lean_ctor_get(v___x_1990_, 0);
v_asyncMode_1992_ = lean_ctor_get(v_toEnvExtension_1991_, 2);
v___x_1993_ = lean_box(0);
v___x_1994_ = 0;
v___x_1995_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1987_, v___x_1990_, v_env_1989_, v_asyncMode_1992_, v___x_1993_, v___x_1994_);
v_merged_1996_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2004_ == 0)
{
lean_object* v_unused_2005_; 
v_unused_2005_ = lean_ctor_get(v___x_1995_, 1);
lean_dec(v_unused_2005_);
v___x_1998_ = v___x_1995_;
v_isShared_1999_ = v_isSharedCheck_2004_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_merged_1996_);
lean_dec(v___x_1995_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2004_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 1, v_merged_1996_);
lean_ctor_set(v___x_1998_, 0, v_o_1984_);
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_o_1984_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_merged_1996_);
v___x_2001_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
lean_object* v___x_2002_; 
v___x_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2001_);
return v___x_2002_;
}
}
}
}
LEAN_EXPORT void l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_1984_ = stack[0].m_obj;
lean_object* v___y_1985_ = stack[1].m_obj;
lean_object* v_res_2006_;
v_res_2006_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_o_1984_, v___y_1985_);
stack->m_obj
 = v_res_2006_;
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg___boxed(lean_object* v_o_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_o_2007_, v___y_2008_);
lean_dec(v___y_2008_);
return v_res_2010_;
}
}
lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0(lean_object* v_o_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v___x_2015_; 
v___x_2015_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_o_2011_, v___y_2013_);
return v___x_2015_;
}
}
LEAN_EXPORT void l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_2011_ = stack[0].m_obj;
lean_object* v___y_2012_ = stack[1].m_obj;
lean_object* v___y_2013_ = stack[2].m_obj;
lean_object* v_res_2016_;
v_res_2016_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0(v_o_2011_, v___y_2012_, v___y_2013_);
stack->m_obj
 = v_res_2016_;
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___boxed(lean_object* v_o_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0(v_o_2017_, v___y_2018_, v___y_2019_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(lean_object* v_opts_2022_, lean_object* v_opt_2023_){
_start:
{
lean_object* v_name_2024_; lean_object* v_defValue_2025_; lean_object* v_map_2026_; lean_object* v___x_2027_; 
v_name_2024_ = lean_ctor_get(v_opt_2023_, 0);
v_defValue_2025_ = lean_ctor_get(v_opt_2023_, 1);
v_map_2026_ = lean_ctor_get(v_opts_2022_, 0);
v___x_2027_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2026_, v_name_2024_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_inc(v_defValue_2025_);
return v_defValue_2025_;
}
else
{
lean_object* v_val_2028_; 
v_val_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_val_2028_);
lean_dec_ref_known(v___x_2027_, 1);
if (lean_obj_tag(v_val_2028_) == 3)
{
lean_object* v_v_2029_; 
v_v_2029_ = lean_ctor_get(v_val_2028_, 0);
lean_inc(v_v_2029_);
lean_dec_ref_known(v_val_2028_, 1);
return v_v_2029_;
}
else
{
lean_dec(v_val_2028_);
lean_inc(v_defValue_2025_);
return v_defValue_2025_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2___boxed(lean_object* v_opts_2030_, lean_object* v_opt_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(v_opts_2030_, v_opt_2031_);
lean_dec_ref(v_opt_2031_);
lean_dec_ref(v_opts_2030_);
return v_res_2032_;
}
}
lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0(lean_object* v_c_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v_options_2037_; lean_object* v___x_2038_; lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2049_; 
v_options_2037_ = lean_ctor_get(v_c_2033_, 6);
lean_inc_ref(v_options_2037_);
lean_dec_ref(v_c_2033_);
v___x_2038_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_options_2037_, v___y_2035_);
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2041_ = v___x_2038_;
v_isShared_2042_ = v_isSharedCheck_2049_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2038_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2049_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2043_; uint8_t v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2047_; 
v___x_2043_ = l_Lean_linter_doc_deferred;
v___x_2044_ = l_Lean_Linter_getLinterValue(v___x_2043_, v_a_2039_);
lean_dec(v_a_2039_);
v___x_2045_ = lean_box(v___x_2044_);
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 0, v___x_2045_);
v___x_2047_ = v___x_2041_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2045_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_2033_ = stack[0].m_obj;
lean_object* v___y_2034_ = stack[1].m_obj;
lean_object* v___y_2035_ = stack[2].m_obj;
lean_object* v_res_2050_;
v_res_2050_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0(v_c_2033_, v___y_2034_, v___y_2035_);
stack->m_obj
 = v_res_2050_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0___boxed(lean_object* v_c_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0(v_c_2051_, v___y_2052_, v___y_2053_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
return v_res_2055_;
}
}
uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1(lean_object* v_pkgRoot_2056_, lean_object* v_docCheckedModules_2057_, uint8_t v___y_2058_, lean_object* v_m_2059_){
_start:
{
uint8_t v___x_2060_; 
v___x_2060_ = l_Lean_Name_isPrefixOf(v_pkgRoot_2056_, v_m_2059_);
if (v___x_2060_ == 0)
{
return v___x_2060_;
}
else
{
uint8_t v___x_2061_; 
v___x_2061_ = l_Lean_NameSet_contains(v_docCheckedModules_2057_, v_m_2059_);
if (v___x_2061_ == 0)
{
return v___y_2058_;
}
else
{
uint8_t v___x_2062_; 
v___x_2062_ = 0;
return v___x_2062_;
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_pkgRoot_2056_ = stack[0].m_obj;
lean_object* v_docCheckedModules_2057_ = stack[1].m_obj;
uint8_t v___y_2058_ = stack[2].m_num;
lean_object* v_m_2059_ = stack[3].m_obj;
uint8_t v_res_2063_;
v_res_2063_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1(v_pkgRoot_2056_, v_docCheckedModules_2057_, v___y_2058_, v_m_2059_);
stack->m_num = v_res_2063_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1___boxed(lean_object* v_pkgRoot_2064_, lean_object* v_docCheckedModules_2065_, lean_object* v___y_2066_, lean_object* v_m_2067_){
_start:
{
uint8_t v___y_7583__boxed_2068_; uint8_t v_res_2069_; lean_object* v_r_2070_; 
v___y_7583__boxed_2068_ = lean_unbox(v___y_2066_);
v_res_2069_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1(v_pkgRoot_2064_, v_docCheckedModules_2065_, v___y_7583__boxed_2068_, v_m_2067_);
lean_dec(v_m_2067_);
lean_dec(v_docCheckedModules_2065_);
lean_dec(v_pkgRoot_2064_);
v_r_2070_ = lean_box(v_res_2069_);
return v_r_2070_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(uint8_t v___x_2078_, lean_object* v_sp_2079_, lean_object* v_as_2080_, size_t v_sz_2081_, size_t v_i_2082_, lean_object* v_b_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v_a_2088_; uint8_t v_unlocated_2092_; 
v_unlocated_2092_ = lean_usize_dec_lt(v_i_2082_, v_sz_2081_);
if (v_unlocated_2092_ == 0)
{
lean_object* v___x_2093_; 
lean_dec(v_sp_2079_);
v___x_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2093_, 0, v_b_2083_);
return v___x_2093_;
}
else
{
lean_object* v_a_2094_; lean_object* v_snd_2095_; lean_object* v_fst_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2218_; 
v_a_2094_ = lean_array_uget_borrowed(v_as_2080_, v_i_2082_);
v_snd_2095_ = lean_ctor_get(v_a_2094_, 1);
lean_inc(v_snd_2095_);
v_fst_2096_ = lean_ctor_get(v_snd_2095_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v_snd_2095_);
if (v_isSharedCheck_2218_ == 0)
{
lean_object* v_unused_2219_; 
v_unused_2219_ = lean_ctor_get(v_snd_2095_, 1);
lean_dec(v_unused_2219_);
v___x_2098_ = v_snd_2095_;
v_isShared_2099_ = v_isSharedCheck_2218_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_fst_2096_);
lean_dec(v_snd_2095_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2218_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v_fst_2100_; lean_object* v_fst_2101_; lean_object* v_snd_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2217_; 
v_fst_2100_ = lean_ctor_get(v_a_2094_, 0);
v_fst_2101_ = lean_ctor_get(v_b_2083_, 0);
v_snd_2102_ = lean_ctor_get(v_b_2083_, 1);
v_isSharedCheck_2217_ = !lean_is_exclusive(v_b_2083_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2104_ = v_b_2083_;
v_isShared_2105_ = v_isSharedCheck_2217_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_snd_2102_);
lean_inc(v_fst_2101_);
lean_dec(v_b_2083_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2217_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v_site_2106_; lean_object* v___x_2107_; 
v_site_2106_ = lean_ctor_get(v_fst_2096_, 0);
lean_inc_ref_n(v_site_2106_, 2);
lean_dec(v_fst_2096_);
v___x_2107_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(v_fst_2100_, v_site_2106_, v___y_2084_, v___y_2085_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v_a_2108_; 
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc(v_a_2108_);
lean_dec_ref_known(v___x_2107_, 1);
if (lean_obj_tag(v_a_2108_) == 0)
{
lean_object* v___x_2109_; lean_object* v_name_2110_; lean_object* v_ref_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
lean_dec(v_snd_2102_);
v___x_2109_ = l_Lean_linter_doc_deferred;
v_name_2110_ = lean_ctor_get(v___x_2109_, 0);
v_ref_2111_ = lean_ctor_get(v___y_2084_, 2);
lean_inc(v_fst_2100_);
v___x_2112_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2100_, v___x_2078_);
v___x_2113_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__0));
v___x_2114_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_2106_);
v___x_2115_ = lean_string_append(v___x_2113_, v___x_2114_);
lean_dec_ref(v___x_2114_);
v___x_2116_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__1));
v___x_2117_ = lean_string_append(v___x_2115_, v___x_2116_);
v___x_2118_ = lean_string_append(v___x_2117_, v___x_2112_);
lean_dec_ref(v___x_2112_);
v___x_2119_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__2));
v___x_2120_ = lean_string_append(v___x_2118_, v___x_2119_);
lean_inc(v_name_2110_);
v___x_2121_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2110_, v___x_2078_);
v___x_2122_ = lean_string_append(v___x_2120_, v___x_2121_);
lean_dec_ref(v___x_2121_);
v___x_2123_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__3));
v___x_2124_ = lean_string_append(v___x_2122_, v___x_2123_);
v___x_2125_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2124_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v___x_2126_; lean_object* v___x_2128_; 
lean_dec_ref_known(v___x_2125_, 1);
lean_del_object(v___x_2098_);
v___x_2126_ = lean_box(v_unlocated_2092_);
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 1, v___x_2126_);
v___x_2128_ = v___x_2104_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_fst_2101_);
lean_ctor_set(v_reuseFailAlloc_2129_, 1, v___x_2126_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
v_a_2088_ = v___x_2128_;
goto v___jp_2087_;
}
}
else
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2143_; 
lean_del_object(v___x_2104_);
lean_dec(v_fst_2101_);
lean_dec(v_sp_2079_);
v_a_2130_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2132_ = v___x_2125_;
v_isShared_2133_ = v_isSharedCheck_2143_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2125_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2143_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2138_; 
v___x_2134_ = lean_io_error_to_string(v_a_2130_);
v___x_2135_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2134_);
v___x_2136_ = l_Lean_MessageData_ofFormat(v___x_2135_);
lean_inc(v_ref_2111_);
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 1, v___x_2136_);
lean_ctor_set(v___x_2098_, 0, v_ref_2111_);
v___x_2138_ = v___x_2098_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_ref_2111_);
lean_ctor_set(v_reuseFailAlloc_2142_, 1, v___x_2136_);
v___x_2138_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
lean_object* v___x_2140_; 
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 0, v___x_2138_);
v___x_2140_ = v___x_2132_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2138_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
}
else
{
lean_object* v_val_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2208_; 
lean_dec_ref(v_site_2106_);
v_val_2144_ = lean_ctor_get(v_a_2108_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v_a_2108_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2146_ = v_a_2108_;
v_isShared_2147_ = v_isSharedCheck_2208_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_val_2144_);
lean_dec(v_a_2108_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2208_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v_ref_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v_ref_2148_ = lean_ctor_get(v___y_2084_, 2);
v___x_2149_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__4));
lean_inc(v_fst_2100_);
lean_inc(v_sp_2079_);
v___x_2150_ = l_Lean_SearchPath_findWithExt(v_sp_2079_, v___x_2149_, v_fst_2100_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; 
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_a_2151_);
lean_dec_ref_known(v___x_2150_, 1);
if (lean_obj_tag(v_a_2151_) == 0)
{
lean_object* v___x_2152_; lean_object* v_name_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
lean_dec(v_val_2144_);
lean_dec(v_snd_2102_);
v___x_2152_ = l_Lean_linter_doc_deferred;
v_name_2153_ = lean_ctor_get(v___x_2152_, 0);
v___x_2154_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__5));
lean_inc(v_fst_2100_);
v___x_2155_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2100_, v___x_2078_);
v___x_2156_ = lean_string_append(v___x_2154_, v___x_2155_);
lean_dec_ref(v___x_2155_);
v___x_2157_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__6));
v___x_2158_ = lean_string_append(v___x_2156_, v___x_2157_);
lean_inc(v_name_2153_);
v___x_2159_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2153_, v___x_2078_);
v___x_2160_ = lean_string_append(v___x_2158_, v___x_2159_);
lean_dec_ref(v___x_2159_);
v___x_2161_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__3));
v___x_2162_ = lean_string_append(v___x_2160_, v___x_2161_);
v___x_2163_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2162_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v___x_2164_; lean_object* v___x_2166_; 
lean_dec_ref_known(v___x_2163_, 1);
lean_del_object(v___x_2146_);
lean_del_object(v___x_2098_);
v___x_2164_ = lean_box(v_unlocated_2092_);
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 1, v___x_2164_);
v___x_2166_ = v___x_2104_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_fst_2101_);
lean_ctor_set(v_reuseFailAlloc_2167_, 1, v___x_2164_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
v_a_2088_ = v___x_2166_;
goto v___jp_2087_;
}
}
else
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2183_; 
lean_del_object(v___x_2104_);
lean_dec(v_fst_2101_);
lean_dec(v_sp_2079_);
v_a_2168_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2170_ = v___x_2163_;
v_isShared_2171_ = v_isSharedCheck_2183_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2163_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2183_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2172_; lean_object* v___x_2174_; 
v___x_2172_ = lean_io_error_to_string(v_a_2168_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set_tag(v___x_2146_, 3);
lean_ctor_set(v___x_2146_, 0, v___x_2172_);
v___x_2174_ = v___x_2146_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v___x_2172_);
v___x_2174_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
lean_object* v___x_2175_; lean_object* v___x_2177_; 
v___x_2175_ = l_Lean_MessageData_ofFormat(v___x_2174_);
lean_inc(v_ref_2148_);
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 1, v___x_2175_);
lean_ctor_set(v___x_2098_, 0, v_ref_2148_);
v___x_2177_ = v___x_2098_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_ref_2148_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v___x_2175_);
v___x_2177_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
lean_object* v___x_2179_; 
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 0, v___x_2177_);
v___x_2179_ = v___x_2170_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2177_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
}
}
else
{
lean_object* v_val_2184_; lean_object* v___x_2185_; lean_object* v_name_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2190_; 
lean_del_object(v___x_2146_);
lean_del_object(v___x_2098_);
v_val_2184_ = lean_ctor_get(v_a_2151_, 0);
lean_inc(v_val_2184_);
lean_dec_ref_known(v_a_2151_, 1);
v___x_2185_ = l_Lean_linter_doc_deferred;
v_name_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_name_2186_);
v___x_2187_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2187_, 0, v_val_2184_);
lean_ctor_set(v___x_2187_, 1, v_val_2144_);
lean_ctor_set(v___x_2187_, 2, v_name_2186_);
v___x_2188_ = lean_array_push(v_fst_2101_, v___x_2187_);
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 0, v___x_2188_);
v___x_2190_ = v___x_2104_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v___x_2188_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v_snd_2102_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
v_a_2088_ = v___x_2190_;
goto v___jp_2087_;
}
}
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2207_; 
lean_dec(v_val_2144_);
lean_del_object(v___x_2104_);
lean_dec(v_snd_2102_);
lean_dec(v_fst_2101_);
lean_dec(v_sp_2079_);
v_a_2192_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2194_ = v___x_2150_;
v_isShared_2195_ = v_isSharedCheck_2207_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2150_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2207_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2196_; lean_object* v___x_2198_; 
v___x_2196_ = lean_io_error_to_string(v_a_2192_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set_tag(v___x_2146_, 3);
lean_ctor_set(v___x_2146_, 0, v___x_2196_);
v___x_2198_ = v___x_2146_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___x_2196_);
v___x_2198_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
lean_object* v___x_2199_; lean_object* v___x_2201_; 
v___x_2199_ = l_Lean_MessageData_ofFormat(v___x_2198_);
lean_inc(v_ref_2148_);
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 1, v___x_2199_);
lean_ctor_set(v___x_2098_, 0, v_ref_2148_);
v___x_2201_ = v___x_2098_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_ref_2148_);
lean_ctor_set(v_reuseFailAlloc_2205_, 1, v___x_2199_);
v___x_2201_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
lean_object* v___x_2203_; 
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 0, v___x_2201_);
v___x_2203_ = v___x_2194_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2201_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
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
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
lean_dec_ref(v_site_2106_);
lean_del_object(v___x_2104_);
lean_dec(v_snd_2102_);
lean_dec(v_fst_2101_);
lean_del_object(v___x_2098_);
lean_dec(v_sp_2079_);
v_a_2209_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___x_2107_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2107_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2209_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
}
}
v___jp_2087_:
{
size_t v___x_2089_; size_t v___x_2090_; 
v___x_2089_ = ((size_t)1ULL);
v___x_2090_ = lean_usize_add(v_i_2082_, v___x_2089_);
v_i_2082_ = v___x_2090_;
v_b_2083_ = v_a_2088_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2078_ = stack[0].m_num;
lean_object* v_sp_2079_ = stack[1].m_obj;
lean_object* v_as_2080_ = stack[2].m_obj;
size_t v_sz_2081_ = stack[3].m_num;
size_t v_i_2082_ = stack[4].m_num;
lean_object* v_b_2083_ = stack[5].m_obj;
lean_object* v___y_2084_ = stack[6].m_obj;
lean_object* v___y_2085_ = stack[7].m_obj;
lean_object* v_res_2220_;
v_res_2220_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(v___x_2078_, v_sp_2079_, v_as_2080_, v_sz_2081_, v_i_2082_, v_b_2083_, v___y_2084_, v___y_2085_);
stack->m_obj
 = v_res_2220_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___boxed(lean_object* v___x_2221_, lean_object* v_sp_2222_, lean_object* v_as_2223_, lean_object* v_sz_2224_, lean_object* v_i_2225_, lean_object* v_b_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
uint8_t v___x_7612__boxed_2230_; size_t v_sz_boxed_2231_; size_t v_i_boxed_2232_; lean_object* v_res_2233_; 
v___x_7612__boxed_2230_ = lean_unbox(v___x_2221_);
v_sz_boxed_2231_ = lean_unbox_usize(v_sz_2224_);
lean_dec(v_sz_2224_);
v_i_boxed_2232_ = lean_unbox_usize(v_i_2225_);
lean_dec(v_i_2225_);
v_res_2233_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(v___x_7612__boxed_2230_, v_sp_2222_, v_as_2223_, v_sz_boxed_2231_, v_i_boxed_2232_, v_b_2226_, v___y_2227_, v___y_2228_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec_ref(v_as_2223_);
return v_res_2233_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg(lean_object* v_sp_2240_, uint8_t v___y_2241_, lean_object* v_as_2242_, size_t v_sz_2243_, size_t v_i_2244_, lean_object* v_b_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v_a_2249_; uint8_t v___x_2253_; 
v___x_2253_ = lean_usize_dec_lt(v_i_2244_, v_sz_2243_);
if (v___x_2253_ == 0)
{
lean_object* v___x_2254_; 
lean_dec(v_sp_2240_);
v___x_2254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2254_, 0, v_b_2245_);
return v___x_2254_;
}
else
{
lean_object* v_a_2255_; lean_object* v_snd_2256_; lean_object* v_fst_2257_; lean_object* v_fst_2258_; lean_object* v_snd_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2352_; 
v_a_2255_ = lean_array_uget_borrowed(v_as_2242_, v_i_2244_);
v_snd_2256_ = lean_ctor_get(v_a_2255_, 1);
lean_inc(v_snd_2256_);
v_fst_2257_ = lean_ctor_get(v_snd_2256_, 0);
lean_inc(v_fst_2257_);
v_fst_2258_ = lean_ctor_get(v_a_2255_, 0);
v_snd_2259_ = lean_ctor_get(v_snd_2256_, 1);
v_isSharedCheck_2352_ = !lean_is_exclusive(v_snd_2256_);
if (v_isSharedCheck_2352_ == 0)
{
lean_object* v_unused_2353_; 
v_unused_2353_ = lean_ctor_get(v_snd_2256_, 0);
lean_dec(v_unused_2353_);
v___x_2261_ = v_snd_2256_;
v_isShared_2262_ = v_isSharedCheck_2352_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_snd_2259_);
lean_dec(v_snd_2256_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2352_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v_site_2263_; lean_object* v_sourceString_2264_; lean_object* v___x_2265_; lean_object* v___y_2267_; lean_object* v___x_2344_; lean_object* v___x_2345_; uint8_t v___x_2346_; 
v_site_2263_ = lean_ctor_get(v_fst_2257_, 0);
lean_inc_ref(v_site_2263_);
v_sourceString_2264_ = lean_ctor_get(v_fst_2257_, 2);
lean_inc_ref(v_sourceString_2264_);
lean_dec(v_fst_2257_);
v___x_2265_ = lean_box(0);
v___x_2344_ = lean_string_utf8_byte_size(v_sourceString_2264_);
v___x_2345_ = lean_unsigned_to_nat(0u);
v___x_2346_ = lean_nat_dec_eq(v___x_2344_, v___x_2345_);
if (v___x_2346_ == 0)
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2347_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__4));
v___x_2348_ = lean_string_append(v___x_2347_, v_sourceString_2264_);
lean_dec_ref(v_sourceString_2264_);
v___x_2349_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__5));
v___x_2350_ = lean_string_append(v___x_2348_, v___x_2349_);
v___y_2267_ = v___x_2350_;
goto v___jp_2266_;
}
else
{
lean_object* v___x_2351_; 
lean_dec_ref(v_sourceString_2264_);
v___x_2351_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___y_2267_ = v___x_2351_;
goto v___jp_2266_;
}
v___jp_2266_:
{
lean_object* v_ref_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
v_ref_2268_ = lean_ctor_get(v___y_2246_, 2);
v___x_2269_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__4));
lean_inc(v_fst_2258_);
lean_inc(v_sp_2240_);
v___x_2270_ = l_Lean_SearchPath_findWithExt(v_sp_2240_, v___x_2269_, v_fst_2258_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v_a_2271_; 
v_a_2271_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_a_2271_);
lean_dec_ref_known(v___x_2270_, 1);
if (lean_obj_tag(v_a_2271_) == 0)
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2272_ = l_Lean_MessageData_toString(v_snd_2259_);
v___x_2273_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__0));
lean_inc(v_fst_2258_);
v___x_2274_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2258_, v___y_2241_);
v___x_2275_ = lean_string_append(v___x_2273_, v___x_2274_);
lean_dec_ref(v___x_2274_);
v___x_2276_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__1));
v___x_2277_ = lean_string_append(v___x_2275_, v___x_2276_);
v___x_2278_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_2263_);
v___x_2279_ = lean_string_append(v___x_2277_, v___x_2278_);
lean_dec_ref(v___x_2278_);
v___x_2280_ = lean_string_append(v___x_2279_, v___y_2267_);
lean_dec_ref(v___y_2267_);
v___x_2281_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__2));
v___x_2282_ = lean_string_append(v___x_2280_, v___x_2281_);
v___x_2283_ = lean_string_append(v___x_2282_, v___x_2272_);
lean_dec_ref(v___x_2272_);
v___x_2284_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2283_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_dec_ref_known(v___x_2284_, 1);
lean_del_object(v___x_2261_);
v_a_2249_ = v___x_2265_;
goto v___jp_2248_;
}
else
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2298_; 
lean_dec(v_sp_2240_);
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2287_ = v___x_2284_;
v_isShared_2288_ = v_isSharedCheck_2298_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2284_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2298_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2293_; 
v___x_2289_ = lean_io_error_to_string(v_a_2285_);
v___x_2290_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2289_);
v___x_2291_ = l_Lean_MessageData_ofFormat(v___x_2290_);
lean_inc(v_ref_2268_);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 1, v___x_2291_);
lean_ctor_set(v___x_2261_, 0, v_ref_2268_);
v___x_2293_ = v___x_2261_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_ref_2268_);
lean_ctor_set(v_reuseFailAlloc_2297_, 1, v___x_2291_);
v___x_2293_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
lean_object* v___x_2295_; 
if (v_isShared_2288_ == 0)
{
lean_ctor_set(v___x_2287_, 0, v___x_2293_);
v___x_2295_ = v___x_2287_;
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
else
{
lean_object* v_val_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2329_; 
v_val_2299_ = lean_ctor_get(v_a_2271_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v_a_2271_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2301_ = v_a_2271_;
v_isShared_2302_ = v_isSharedCheck_2329_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_val_2299_);
lean_dec(v_a_2271_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2329_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2303_ = l_Lean_MessageData_toString(v_snd_2259_);
v___x_2304_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__3));
v___x_2305_ = lean_string_append(v_val_2299_, v___x_2304_);
v___x_2306_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_2263_);
v___x_2307_ = lean_string_append(v___x_2305_, v___x_2306_);
lean_dec_ref(v___x_2306_);
v___x_2308_ = lean_string_append(v___x_2307_, v___y_2267_);
lean_dec_ref(v___y_2267_);
v___x_2309_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__2));
v___x_2310_ = lean_string_append(v___x_2308_, v___x_2309_);
v___x_2311_ = lean_string_append(v___x_2310_, v___x_2303_);
lean_dec_ref(v___x_2303_);
v___x_2312_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2311_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_dec_ref_known(v___x_2312_, 1);
lean_del_object(v___x_2301_);
lean_del_object(v___x_2261_);
v_a_2249_ = v___x_2265_;
goto v___jp_2248_;
}
else
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2328_; 
lean_dec(v_sp_2240_);
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2315_ = v___x_2312_;
v_isShared_2316_ = v_isSharedCheck_2328_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2312_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2328_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2317_; lean_object* v___x_2319_; 
v___x_2317_ = lean_io_error_to_string(v_a_2313_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set_tag(v___x_2301_, 3);
lean_ctor_set(v___x_2301_, 0, v___x_2317_);
v___x_2319_ = v___x_2301_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2317_);
v___x_2319_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
lean_object* v___x_2320_; lean_object* v___x_2322_; 
v___x_2320_ = l_Lean_MessageData_ofFormat(v___x_2319_);
lean_inc(v_ref_2268_);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 1, v___x_2320_);
lean_ctor_set(v___x_2261_, 0, v_ref_2268_);
v___x_2322_ = v___x_2261_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_ref_2268_);
lean_ctor_set(v_reuseFailAlloc_2326_, 1, v___x_2320_);
v___x_2322_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
lean_object* v___x_2324_; 
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 0, v___x_2322_);
v___x_2324_ = v___x_2315_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v___x_2322_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
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
lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2343_; 
lean_dec_ref(v___y_2267_);
lean_dec_ref(v_site_2263_);
lean_dec(v_snd_2259_);
lean_dec(v_sp_2240_);
v_a_2330_ = lean_ctor_get(v___x_2270_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2332_ = v___x_2270_;
v_isShared_2333_ = v_isSharedCheck_2343_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2270_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2343_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2338_; 
v___x_2334_ = lean_io_error_to_string(v_a_2330_);
v___x_2335_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2334_);
v___x_2336_ = l_Lean_MessageData_ofFormat(v___x_2335_);
lean_inc(v_ref_2268_);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 1, v___x_2336_);
lean_ctor_set(v___x_2261_, 0, v_ref_2268_);
v___x_2338_ = v___x_2261_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_ref_2268_);
lean_ctor_set(v_reuseFailAlloc_2342_, 1, v___x_2336_);
v___x_2338_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
lean_object* v___x_2340_; 
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 0, v___x_2338_);
v___x_2340_ = v___x_2332_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2338_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
}
}
}
v___jp_2248_:
{
size_t v___x_2250_; size_t v___x_2251_; 
v___x_2250_ = ((size_t)1ULL);
v___x_2251_ = lean_usize_add(v_i_2244_, v___x_2250_);
v_i_2244_ = v___x_2251_;
v_b_2245_ = v_a_2249_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_sp_2240_ = stack[0].m_obj;
uint8_t v___y_2241_ = stack[1].m_num;
lean_object* v_as_2242_ = stack[2].m_obj;
size_t v_sz_2243_ = stack[3].m_num;
size_t v_i_2244_ = stack[4].m_num;
lean_object* v_b_2245_ = stack[5].m_obj;
lean_object* v___y_2246_ = stack[6].m_obj;
lean_object* v_res_2354_;
v_res_2354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg(v_sp_2240_, v___y_2241_, v_as_2242_, v_sz_2243_, v_i_2244_, v_b_2245_, v___y_2246_);
stack->m_obj
 = v_res_2354_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___boxed(lean_object* v_sp_2355_, lean_object* v___y_2356_, lean_object* v_as_2357_, lean_object* v_sz_2358_, lean_object* v_i_2359_, lean_object* v_b_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
uint8_t v___y_8032__boxed_2363_; size_t v_sz_boxed_2364_; size_t v_i_boxed_2365_; lean_object* v_res_2366_; 
v___y_8032__boxed_2363_ = lean_unbox(v___y_2356_);
v_sz_boxed_2364_ = lean_unbox_usize(v_sz_2358_);
lean_dec(v_sz_2358_);
v_i_boxed_2365_ = lean_unbox_usize(v_i_2359_);
lean_dec(v_i_2359_);
v_res_2366_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg(v_sp_2355_, v___y_8032__boxed_2363_, v_as_2357_, v_sz_boxed_2364_, v_i_boxed_2365_, v_b_2360_, v___y_2361_);
lean_dec_ref(v___y_2361_);
lean_dec_ref(v_as_2357_);
return v_res_2366_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(lean_object* v_pkgRoot_2367_, lean_object* v_as_2368_, size_t v_sz_2369_, size_t v_i_2370_, lean_object* v_b_2371_){
_start:
{
lean_object* v_a_2374_; uint8_t v___x_2378_; 
v___x_2378_ = lean_usize_dec_lt(v_i_2370_, v_sz_2369_);
if (v___x_2378_ == 0)
{
lean_object* v___x_2379_; 
v___x_2379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2379_, 0, v_b_2371_);
return v___x_2379_;
}
else
{
lean_object* v_a_2380_; uint8_t v___x_2381_; 
v_a_2380_ = lean_array_uget_borrowed(v_as_2368_, v_i_2370_);
v___x_2381_ = l_Lean_Name_isPrefixOf(v_pkgRoot_2367_, v_a_2380_);
if (v___x_2381_ == 0)
{
v_a_2374_ = v_b_2371_;
goto v___jp_2373_;
}
else
{
lean_object* v___x_2382_; 
lean_inc(v_a_2380_);
v___x_2382_ = l_Lean_NameSet_insert(v_b_2371_, v_a_2380_);
v_a_2374_ = v___x_2382_;
goto v___jp_2373_;
}
}
v___jp_2373_:
{
size_t v___x_2375_; size_t v___x_2376_; 
v___x_2375_ = ((size_t)1ULL);
v___x_2376_ = lean_usize_add(v_i_2370_, v___x_2375_);
v_i_2370_ = v___x_2376_;
v_b_2371_ = v_a_2374_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_pkgRoot_2367_ = stack[0].m_obj;
lean_object* v_as_2368_ = stack[1].m_obj;
size_t v_sz_2369_ = stack[2].m_num;
size_t v_i_2370_ = stack[3].m_num;
lean_object* v_b_2371_ = stack[4].m_obj;
lean_object* v_res_2383_;
v_res_2383_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(v_pkgRoot_2367_, v_as_2368_, v_sz_2369_, v_i_2370_, v_b_2371_);
stack->m_obj
 = v_res_2383_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1___boxed(lean_object* v_pkgRoot_2384_, lean_object* v_as_2385_, lean_object* v_sz_2386_, lean_object* v_i_2387_, lean_object* v_b_2388_, lean_object* v___y_2389_){
_start:
{
size_t v_sz_boxed_2390_; size_t v_i_boxed_2391_; lean_object* v_res_2392_; 
v_sz_boxed_2390_ = lean_unbox_usize(v_sz_2386_);
lean_dec(v_sz_2386_);
v_i_boxed_2391_ = lean_unbox_usize(v_i_2387_);
lean_dec(v_i_2387_);
v_res_2392_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(v_pkgRoot_2384_, v_as_2385_, v_sz_boxed_2390_, v_i_boxed_2391_, v_b_2388_);
lean_dec_ref(v_as_2385_);
lean_dec(v_pkgRoot_2384_);
return v_res_2392_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5(void){
_start:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2399_ = l_Lean_Options_empty;
v___x_2400_ = l_Lean_Core_getMaxHeartbeats(v___x_2399_);
return v___x_2400_;
}
}
static uint16_t _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6(void){
_start:
{
lean_object* v___x_2401_; uint16_t v___x_2402_; 
v___x_2401_ = l_Lean_Options_empty;
v___x_2402_ = l_Lean_OptionFlags_ofOptions(v___x_2401_);
return v___x_2402_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7(void){
_start:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2403_ = lean_unsigned_to_nat(1u);
v___x_2404_ = l_Lean_firstFrontendMacroScope;
v___x_2405_ = lean_nat_add(v___x_2404_, v___x_2403_);
return v___x_2405_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12(void){
_start:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2416_ = lean_unsigned_to_nat(32u);
v___x_2417_ = lean_mk_empty_array_with_capacity(v___x_2416_);
v___x_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2417_);
return v___x_2418_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13(void){
_start:
{
size_t v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2419_ = ((size_t)5ULL);
v___x_2420_ = lean_unsigned_to_nat(0u);
v___x_2421_ = lean_unsigned_to_nat(32u);
v___x_2422_ = lean_mk_empty_array_with_capacity(v___x_2421_);
v___x_2423_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12);
v___x_2424_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2424_, 0, v___x_2423_);
lean_ctor_set(v___x_2424_, 1, v___x_2422_);
lean_ctor_set(v___x_2424_, 2, v___x_2420_);
lean_ctor_set(v___x_2424_, 3, v___x_2420_);
lean_ctor_set_usize(v___x_2424_, 4, v___x_2419_);
return v___x_2424_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14(void){
_start:
{
lean_object* v___x_2425_; uint64_t v___x_2426_; lean_object* v___x_2427_; 
v___x_2425_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13);
v___x_2426_ = 0ULL;
v___x_2427_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2427_, 0, v___x_2425_);
lean_ctor_set_uint64(v___x_2427_, sizeof(void*)*1, v___x_2426_);
return v___x_2427_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15(void){
_start:
{
lean_object* v___x_2428_; 
v___x_2428_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2428_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16(void){
_start:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; 
v___x_2429_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15);
v___x_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2429_);
return v___x_2430_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17(void){
_start:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___x_2431_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v___x_2432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2431_);
lean_ctor_set(v___x_2432_, 1, v___x_2431_);
return v___x_2432_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18(void){
_start:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2433_ = lean_unsigned_to_nat(0u);
v___x_2434_ = l_Lean_Options_empty;
v___x_2435_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___closed__0));
v___x_2436_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2435_);
lean_ctor_set(v___x_2436_, 1, v___x_2434_);
lean_ctor_set(v___x_2436_, 2, v___x_2435_);
lean_ctor_set(v___x_2436_, 3, v___x_2433_);
lean_ctor_set(v___x_2436_, 4, v___x_2433_);
lean_ctor_set(v___x_2436_, 5, v___x_2433_);
return v___x_2436_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19(void){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2437_ = l_Lean_NameSet_empty;
v___x_2438_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13);
v___x_2439_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2438_);
lean_ctor_set(v___x_2439_, 1, v___x_2438_);
lean_ctor_set(v___x_2439_, 2, v___x_2437_);
return v___x_2439_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20(void){
_start:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; uint8_t v_unlocated_2442_; lean_object* v___x_2443_; 
v___x_2440_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13);
v___x_2441_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v_unlocated_2442_ = 1;
v___x_2443_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2443_, 0, v___x_2441_);
lean_ctor_set(v___x_2443_, 1, v___x_2441_);
lean_ctor_set(v___x_2443_, 2, v___x_2440_);
lean_ctor_set_uint8(v___x_2443_, sizeof(void*)*3, v_unlocated_2442_);
return v___x_2443_;
}
}
static uint16_t _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__21(void){
_start:
{
uint16_t v___x_2444_; uint16_t v___x_2445_; uint16_t v___x_2446_; 
v___x_2444_ = 512;
v___x_2445_ = lean_uint16_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_2446_ = lean_uint16_land(v___x_2445_, v___x_2444_);
return v___x_2446_;
}
}
static uint8_t _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22(void){
_start:
{
uint16_t v___x_2447_; uint16_t v___x_2448_; uint8_t v___x_2449_; 
v___x_2447_ = 0;
v___x_2448_ = lean_uint16_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__21, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__21_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__21);
v___x_2449_ = lean_uint16_dec_eq(v___x_2448_, v___x_2447_);
return v___x_2449_;
}
}
lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(lean_object* v_args_2450_, lean_object* v_linterOpts_2451_, lean_object* v_sp_2452_, lean_object* v_env_2453_, lean_object* v_pkgRoot_2454_, lean_object* v_docCheckedModules_2455_){
_start:
{
lean_object* v___y_2458_; lean_object* v_a_2462_; uint8_t v___y_2466_; lean_object* v_a_2467_; lean_object* v___y_2484_; lean_object* v_a_2485_; lean_object* v___y_2510_; uint8_t v___y_2511_; uint8_t v_lintOnly_2513_; uint8_t v_mode_2514_; lean_object* v___f_2515_; uint8_t v___y_2517_; lean_object* v___y_2518_; uint8_t v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2522_; uint16_t v___y_2523_; lean_object* v_fileName_2524_; lean_object* v_fileMap_2525_; lean_object* v_currNamespace_2526_; lean_object* v_openDecls_2527_; lean_object* v_initHeartbeats_2528_; lean_object* v_maxHeartbeats_2529_; lean_object* v_quotContext_2530_; lean_object* v_currMacroScope_2531_; lean_object* v_cancelTk_x3f_2532_; lean_object* v_inheritedTraceOptions_2533_; lean_object* v_currRecDepth_2534_; lean_object* v_ref_2535_; uint8_t v_suppressElabErrors_2536_; uint8_t v_isRecordingDeps_2537_; lean_object* v___y_2538_; uint8_t v___y_2568_; lean_object* v___y_2569_; uint8_t v___y_2570_; lean_object* v___y_2571_; uint8_t v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; uint16_t v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; uint8_t v___y_2614_; 
v_lintOnly_2513_ = lean_ctor_get_uint8(v_args_2450_, sizeof(void*)*4);
v_mode_2514_ = lean_ctor_get_uint8(v_args_2450_, sizeof(void*)*4 + 1);
v___f_2515_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__3));
if (v_lintOnly_2513_ == 0)
{
lean_object* v___x_2655_; uint8_t v___x_2656_; 
v___x_2655_ = l_Lean_linter_doc_deferred;
v___x_2656_ = l_Lean_Linter_getLinterValue(v___x_2655_, v_linterOpts_2451_);
v___y_2614_ = v___x_2656_;
goto v___jp_2613_;
}
else
{
lean_object* v___x_2657_; lean_object* v_name_2658_; uint8_t v___x_2659_; 
v___x_2657_ = l_Lean_linter_doc_deferred;
v_name_2658_ = lean_ctor_get(v___x_2657_, 0);
v___x_2659_ = l_Lean_Linter_isLinterEnabledByOptions(v_name_2658_, v_linterOpts_2451_);
v___y_2614_ = v___x_2659_;
goto v___jp_2613_;
}
v___jp_2457_:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2459_, 0, v___y_2458_);
lean_ctor_set(v___x_2459_, 1, v_docCheckedModules_2455_);
v___x_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2459_);
return v___x_2460_;
}
v___jp_2461_:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2463_ = lean_mk_io_user_error(v_a_2462_);
v___x_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2463_);
return v___x_2464_;
}
v___jp_2465_:
{
if (lean_obj_tag(v_a_2467_) == 0)
{
lean_object* v_msg_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v_msg_2468_ = lean_ctor_get(v_a_2467_, 1);
lean_inc_ref(v_msg_2468_);
lean_dec_ref_known(v_a_2467_, 2);
v___x_2469_ = l_Lean_MessageData_toString(v_msg_2468_);
v___x_2470_ = lean_mk_io_user_error(v___x_2469_);
v___x_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2470_);
return v___x_2471_;
}
else
{
lean_object* v_id_2472_; lean_object* v___x_2473_; 
v_id_2472_ = lean_ctor_get(v_a_2467_, 0);
lean_inc(v_id_2472_);
lean_dec_ref_known(v_a_2467_, 2);
v___x_2473_ = l_Lean_InternalExceptionId_getName(v_id_2472_);
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_object* v_a_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
lean_dec(v_id_2472_);
v_a_2474_ = lean_ctor_get(v___x_2473_, 0);
lean_inc(v_a_2474_);
lean_dec_ref_known(v___x_2473_, 1);
v___x_2475_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_2476_ = l_Lean_Name_toString(v_a_2474_, v___y_2466_);
v___x_2477_ = lean_string_append(v___x_2475_, v___x_2476_);
lean_dec_ref(v___x_2476_);
v_a_2462_ = v___x_2477_;
goto v___jp_2461_;
}
else
{
lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
lean_dec_ref_known(v___x_2473_, 1);
v___x_2478_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_2479_ = l_Nat_reprFast(v_id_2472_);
v___x_2480_ = lean_string_append(v___x_2478_, v___x_2479_);
lean_dec_ref(v___x_2479_);
v___x_2481_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_2482_ = lean_string_append(v___x_2480_, v___x_2481_);
v_a_2462_ = v___x_2482_;
goto v___jp_2461_;
}
}
}
v___jp_2483_:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v_moduleNames_2488_; size_t v_sz_2489_; size_t v___x_2490_; lean_object* v___x_2491_; 
v___x_2486_ = lean_st_ref_get(v___y_2484_);
lean_dec(v___y_2484_);
lean_dec(v___x_2486_);
v___x_2487_ = l_Lean_Environment_header(v_env_2453_);
lean_dec_ref(v_env_2453_);
v_moduleNames_2488_ = lean_ctor_get(v___x_2487_, 4);
lean_inc_ref(v_moduleNames_2488_);
lean_dec_ref(v___x_2487_);
v_sz_2489_ = lean_array_size(v_moduleNames_2488_);
v___x_2490_ = ((size_t)0ULL);
v___x_2491_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(v_pkgRoot_2454_, v_moduleNames_2488_, v_sz_2489_, v___x_2490_, v_docCheckedModules_2455_);
lean_dec_ref(v_moduleNames_2488_);
lean_dec(v_pkgRoot_2454_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v_a_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2500_; 
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2494_ = v___x_2491_;
v_isShared_2495_ = v_isSharedCheck_2500_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_a_2492_);
lean_dec(v___x_2491_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2500_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v___x_2496_; lean_object* v___x_2498_; 
v___x_2496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2496_, 0, v_a_2485_);
lean_ctor_set(v___x_2496_, 1, v_a_2492_);
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 0, v___x_2496_);
v___x_2498_ = v___x_2494_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___x_2496_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
else
{
lean_object* v_a_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2508_; 
lean_dec_ref(v_a_2485_);
v_a_2501_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2503_ = v___x_2491_;
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_a_2501_);
lean_dec(v___x_2491_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2506_; 
if (v_isShared_2504_ == 0)
{
v___x_2506_ = v___x_2503_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_a_2501_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
}
v___jp_2509_:
{
lean_object* v___x_2512_; 
v___x_2512_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2512_, 0, v___y_2511_);
v___y_2484_ = v___y_2510_;
v_a_2485_ = v___x_2512_;
goto v___jp_2483_;
}
v___jp_2516_:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2539_ = l_Lean_maxRecDepth;
v___x_2540_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(v___y_2521_, v___x_2539_);
lean_inc_ref(v___y_2521_);
v___x_2541_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2541_, 0, v_fileName_2524_);
lean_ctor_set(v___x_2541_, 1, v_fileMap_2525_);
lean_ctor_set(v___x_2541_, 2, v___y_2521_);
lean_ctor_set(v___x_2541_, 3, v___x_2540_);
lean_ctor_set(v___x_2541_, 4, v_currNamespace_2526_);
lean_ctor_set(v___x_2541_, 5, v_openDecls_2527_);
lean_ctor_set(v___x_2541_, 6, v_initHeartbeats_2528_);
lean_ctor_set(v___x_2541_, 7, v_maxHeartbeats_2529_);
lean_ctor_set(v___x_2541_, 8, v_quotContext_2530_);
lean_ctor_set(v___x_2541_, 9, v_currMacroScope_2531_);
lean_ctor_set(v___x_2541_, 10, v_cancelTk_x3f_2532_);
lean_ctor_set(v___x_2541_, 11, v_inheritedTraceOptions_2533_);
v___x_2542_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2542_, 0, v___x_2541_);
lean_ctor_set(v___x_2542_, 1, v_currRecDepth_2534_);
lean_ctor_set(v___x_2542_, 2, v_ref_2535_);
lean_ctor_set_uint16(v___x_2542_, sizeof(void*)*3, v___y_2523_);
lean_ctor_set_uint8(v___x_2542_, sizeof(void*)*3 + 2, v_suppressElabErrors_2536_);
lean_ctor_set_uint8(v___x_2542_, sizeof(void*)*3 + 3, v_isRecordingDeps_2537_);
v___x_2543_ = l_Lean_Doc_DeferredCheck_run(v___y_2518_, v___f_2515_, v___x_2542_, v___y_2538_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_a_2544_; uint8_t v___x_2545_; uint8_t v___x_2546_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_a_2544_);
lean_dec_ref_known(v___x_2543_, 1);
v___x_2545_ = 1;
v___x_2546_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_2514_, v___x_2545_);
if (v___x_2546_ == 0)
{
lean_object* v___x_2547_; size_t v_sz_2548_; size_t v___x_2549_; lean_object* v___x_2550_; 
lean_dec(v___y_2538_);
v___x_2547_ = lean_box(0);
v_sz_2548_ = lean_array_size(v_a_2544_);
v___x_2549_ = ((size_t)0ULL);
v___x_2550_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg(v_sp_2452_, v___y_2519_, v_a_2544_, v_sz_2548_, v___x_2549_, v___x_2547_, v___x_2542_);
lean_dec_ref_known(v___x_2542_, 3);
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_object* v___x_2551_; uint8_t v___x_2552_; 
lean_dec_ref_known(v___x_2550_, 1);
v___x_2551_ = lean_array_get_size(v_a_2544_);
lean_dec(v_a_2544_);
v___x_2552_ = lean_nat_dec_eq(v___x_2551_, v___y_2520_);
lean_dec(v___y_2520_);
if (v___x_2552_ == 0)
{
v___y_2510_ = v___y_2522_;
v___y_2511_ = v___y_2519_;
goto v___jp_2509_;
}
else
{
v___y_2510_ = v___y_2522_;
v___y_2511_ = v___x_2546_;
goto v___jp_2509_;
}
}
else
{
lean_object* v_a_2553_; 
lean_dec(v_a_2544_);
lean_dec(v___y_2522_);
lean_dec(v___y_2520_);
lean_dec(v_docCheckedModules_2455_);
lean_dec(v_pkgRoot_2454_);
lean_dec_ref(v_env_2453_);
v_a_2553_ = lean_ctor_get(v___x_2550_, 0);
lean_inc(v_a_2553_);
lean_dec_ref_known(v___x_2550_, 1);
v___y_2466_ = v___y_2519_;
v_a_2467_ = v_a_2553_;
goto v___jp_2465_;
}
}
else
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; size_t v_sz_2557_; size_t v___x_2558_; lean_object* v___x_2559_; 
v___x_2554_ = lean_mk_empty_array_with_capacity(v___y_2520_);
lean_dec(v___y_2520_);
v___x_2555_ = lean_box(v___y_2517_);
v___x_2556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2554_);
lean_ctor_set(v___x_2556_, 1, v___x_2555_);
v_sz_2557_ = lean_array_size(v_a_2544_);
v___x_2558_ = ((size_t)0ULL);
v___x_2559_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(v___x_2546_, v_sp_2452_, v_a_2544_, v_sz_2557_, v___x_2558_, v___x_2556_, v___x_2542_, v___y_2538_);
lean_dec(v___y_2538_);
lean_dec_ref_known(v___x_2542_, 3);
lean_dec(v_a_2544_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; lean_object* v_fst_2561_; lean_object* v_snd_2562_; lean_object* v___x_2563_; uint8_t v___x_2564_; 
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
lean_inc(v_a_2560_);
lean_dec_ref_known(v___x_2559_, 1);
v_fst_2561_ = lean_ctor_get(v_a_2560_, 0);
lean_inc(v_fst_2561_);
v_snd_2562_ = lean_ctor_get(v_a_2560_, 1);
lean_inc(v_snd_2562_);
lean_dec(v_a_2560_);
v___x_2563_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2563_, 0, v_fst_2561_);
v___x_2564_ = lean_unbox(v_snd_2562_);
lean_dec(v_snd_2562_);
lean_ctor_set_uint8(v___x_2563_, sizeof(void*)*1, v___x_2564_);
v___y_2484_ = v___y_2522_;
v_a_2485_ = v___x_2563_;
goto v___jp_2483_;
}
else
{
lean_object* v_a_2565_; 
lean_dec(v___y_2522_);
lean_dec(v_docCheckedModules_2455_);
lean_dec(v_pkgRoot_2454_);
lean_dec_ref(v_env_2453_);
v_a_2565_ = lean_ctor_get(v___x_2559_, 0);
lean_inc(v_a_2565_);
lean_dec_ref_known(v___x_2559_, 1);
v___y_2466_ = v___y_2519_;
v_a_2467_ = v_a_2565_;
goto v___jp_2465_;
}
}
}
else
{
lean_object* v_a_2566_; 
lean_dec_ref_known(v___x_2542_, 3);
lean_dec(v___y_2538_);
lean_dec(v___y_2522_);
lean_dec(v___y_2520_);
lean_dec(v_docCheckedModules_2455_);
lean_dec(v_pkgRoot_2454_);
lean_dec_ref(v_env_2453_);
lean_dec(v_sp_2452_);
v_a_2566_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_a_2566_);
lean_dec_ref_known(v___x_2543_, 1);
v___y_2466_ = v___y_2519_;
v_a_2467_ = v_a_2566_;
goto v___jp_2465_;
}
}
v___jp_2567_:
{
lean_object* v___x_2578_; lean_object* v_env_2579_; lean_object* v_nextMacroScope_2580_; lean_object* v_ngen_2581_; lean_object* v_auxDeclNGen_2582_; lean_object* v_traceState_2583_; lean_object* v_recordedDeps_2584_; lean_object* v_messages_2585_; lean_object* v_infoState_2586_; lean_object* v_snapshotTasks_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2611_; 
v___x_2578_ = lean_st_ref_take(v___y_2576_);
v_env_2579_ = lean_ctor_get(v___x_2578_, 0);
v_nextMacroScope_2580_ = lean_ctor_get(v___x_2578_, 1);
v_ngen_2581_ = lean_ctor_get(v___x_2578_, 2);
v_auxDeclNGen_2582_ = lean_ctor_get(v___x_2578_, 3);
v_traceState_2583_ = lean_ctor_get(v___x_2578_, 4);
v_recordedDeps_2584_ = lean_ctor_get(v___x_2578_, 6);
v_messages_2585_ = lean_ctor_get(v___x_2578_, 7);
v_infoState_2586_ = lean_ctor_get(v___x_2578_, 8);
v_snapshotTasks_2587_ = lean_ctor_get(v___x_2578_, 9);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2611_ == 0)
{
lean_object* v_unused_2612_; 
v_unused_2612_ = lean_ctor_get(v___x_2578_, 5);
lean_dec(v_unused_2612_);
v___x_2589_ = v___x_2578_;
v_isShared_2590_ = v_isSharedCheck_2611_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_snapshotTasks_2587_);
lean_inc(v_infoState_2586_);
lean_inc(v_messages_2585_);
lean_inc(v_recordedDeps_2584_);
lean_inc(v_traceState_2583_);
lean_inc(v_auxDeclNGen_2582_);
lean_inc(v_ngen_2581_);
lean_inc(v_nextMacroScope_2580_);
lean_inc(v_env_2579_);
lean_dec(v___x_2578_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2611_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2591_; lean_object* v___x_2593_; 
v___x_2591_ = l_Lean_Kernel_enableDiag(v_env_2579_, v___y_2572_);
lean_inc_ref(v___y_2577_);
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 5, v___y_2577_);
lean_ctor_set(v___x_2589_, 0, v___x_2591_);
v___x_2593_ = v___x_2589_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v___x_2591_);
lean_ctor_set(v_reuseFailAlloc_2610_, 1, v_nextMacroScope_2580_);
lean_ctor_set(v_reuseFailAlloc_2610_, 2, v_ngen_2581_);
lean_ctor_set(v_reuseFailAlloc_2610_, 3, v_auxDeclNGen_2582_);
lean_ctor_set(v_reuseFailAlloc_2610_, 4, v_traceState_2583_);
lean_ctor_set(v_reuseFailAlloc_2610_, 5, v___y_2577_);
lean_ctor_set(v_reuseFailAlloc_2610_, 6, v_recordedDeps_2584_);
lean_ctor_set(v_reuseFailAlloc_2610_, 7, v_messages_2585_);
lean_ctor_set(v_reuseFailAlloc_2610_, 8, v_infoState_2586_);
lean_ctor_set(v_reuseFailAlloc_2610_, 9, v_snapshotTasks_2587_);
v___x_2593_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
lean_object* v___x_2594_; lean_object* v_toCold_2595_; lean_object* v_currRecDepth_2596_; lean_object* v_ref_2597_; uint8_t v_suppressElabErrors_2598_; uint8_t v_isRecordingDeps_2599_; lean_object* v_fileName_2600_; lean_object* v_fileMap_2601_; lean_object* v_currNamespace_2602_; lean_object* v_openDecls_2603_; lean_object* v_initHeartbeats_2604_; lean_object* v_maxHeartbeats_2605_; lean_object* v_quotContext_2606_; lean_object* v_currMacroScope_2607_; lean_object* v_cancelTk_x3f_2608_; lean_object* v_inheritedTraceOptions_2609_; 
v___x_2594_ = lean_st_ref_put(v___y_2576_, v___x_2593_);
v_toCold_2595_ = lean_ctor_get(v___y_2571_, 0);
lean_inc_ref(v_toCold_2595_);
v_currRecDepth_2596_ = lean_ctor_get(v___y_2571_, 1);
lean_inc(v_currRecDepth_2596_);
v_ref_2597_ = lean_ctor_get(v___y_2571_, 2);
lean_inc(v_ref_2597_);
v_suppressElabErrors_2598_ = lean_ctor_get_uint8(v___y_2571_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2599_ = lean_ctor_get_uint8(v___y_2571_, sizeof(void*)*3 + 3);
lean_dec_ref(v___y_2571_);
v_fileName_2600_ = lean_ctor_get(v_toCold_2595_, 0);
lean_inc_ref(v_fileName_2600_);
v_fileMap_2601_ = lean_ctor_get(v_toCold_2595_, 1);
lean_inc_ref(v_fileMap_2601_);
v_currNamespace_2602_ = lean_ctor_get(v_toCold_2595_, 4);
lean_inc(v_currNamespace_2602_);
v_openDecls_2603_ = lean_ctor_get(v_toCold_2595_, 5);
lean_inc(v_openDecls_2603_);
v_initHeartbeats_2604_ = lean_ctor_get(v_toCold_2595_, 6);
lean_inc(v_initHeartbeats_2604_);
v_maxHeartbeats_2605_ = lean_ctor_get(v_toCold_2595_, 7);
lean_inc(v_maxHeartbeats_2605_);
v_quotContext_2606_ = lean_ctor_get(v_toCold_2595_, 8);
lean_inc(v_quotContext_2606_);
v_currMacroScope_2607_ = lean_ctor_get(v_toCold_2595_, 9);
lean_inc(v_currMacroScope_2607_);
v_cancelTk_x3f_2608_ = lean_ctor_get(v_toCold_2595_, 10);
lean_inc(v_cancelTk_x3f_2608_);
v_inheritedTraceOptions_2609_ = lean_ctor_get(v_toCold_2595_, 11);
lean_inc_ref(v_inheritedTraceOptions_2609_);
lean_dec_ref(v_toCold_2595_);
lean_inc(v___y_2576_);
v___y_2517_ = v___y_2568_;
v___y_2518_ = v___y_2569_;
v___y_2519_ = v___y_2570_;
v___y_2520_ = v___y_2573_;
v___y_2521_ = v___y_2574_;
v___y_2522_ = v___y_2576_;
v___y_2523_ = v___y_2575_;
v_fileName_2524_ = v_fileName_2600_;
v_fileMap_2525_ = v_fileMap_2601_;
v_currNamespace_2526_ = v_currNamespace_2602_;
v_openDecls_2527_ = v_openDecls_2603_;
v_initHeartbeats_2528_ = v_initHeartbeats_2604_;
v_maxHeartbeats_2529_ = v_maxHeartbeats_2605_;
v_quotContext_2530_ = v_quotContext_2606_;
v_currMacroScope_2531_ = v_currMacroScope_2607_;
v_cancelTk_x3f_2532_ = v_cancelTk_x3f_2608_;
v_inheritedTraceOptions_2533_ = v_inheritedTraceOptions_2609_;
v_currRecDepth_2534_ = v_currRecDepth_2596_;
v_ref_2535_ = v_ref_2597_;
v_suppressElabErrors_2536_ = v_suppressElabErrors_2598_;
v_isRecordingDeps_2537_ = v_isRecordingDeps_2599_;
v___y_2538_ = v___y_2576_;
goto v___jp_2516_;
}
}
}
v___jp_2613_:
{
if (v___y_2614_ == 0)
{
uint8_t v___x_2615_; uint8_t v___x_2616_; 
lean_dec(v_pkgRoot_2454_);
lean_dec_ref(v_env_2453_);
lean_dec(v_sp_2452_);
v___x_2615_ = 1;
v___x_2616_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_2514_, v___x_2615_);
if (v___x_2616_ == 0)
{
lean_object* v___x_2617_; 
v___x_2617_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2617_, 0, v___x_2616_);
v___y_2458_ = v___x_2617_;
goto v___jp_2457_;
}
else
{
lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2618_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_2619_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2619_, 0, v___x_2618_);
lean_ctor_set_uint8(v___x_2619_, sizeof(void*)*1, v___y_2614_);
v___y_2458_ = v___x_2619_;
goto v___jp_2457_;
}
}
else
{
lean_object* v___x_2620_; lean_object* v___f_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; uint16_t v___x_2633_; uint8_t v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v_env_2652_; uint8_t v___x_2653_; uint8_t v___x_2654_; 
v___x_2620_ = lean_box(v___y_2614_);
lean_inc(v_docCheckedModules_2455_);
lean_inc(v_pkgRoot_2454_);
v___f_2621_ = lean_alloc_closure((void*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2621_, 0, v_pkgRoot_2454_);
lean_closure_set(v___f_2621_, 1, v_docCheckedModules_2455_);
lean_closure_set(v___f_2621_, 2, v___x_2620_);
v___x_2622_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_2623_ = l_Lean_instInhabitedFileMap_default;
v___x_2624_ = l_Lean_Options_empty;
v___x_2625_ = lean_unsigned_to_nat(1000u);
v___x_2626_ = lean_box(0);
v___x_2627_ = lean_box(0);
v___x_2628_ = lean_unsigned_to_nat(0u);
v___x_2629_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5);
v___x_2630_ = l_Lean_firstFrontendMacroScope;
v___x_2631_ = lean_box(0);
v___x_2632_ = lean_box(0);
v___x_2633_ = lean_uint16_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_2634_ = 0;
v___x_2635_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7);
v___x_2636_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10));
v___x_2637_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11));
v___x_2638_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14);
v___x_2639_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_2640_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___closed__0));
v___x_2641_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18);
v___x_2642_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_2643_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
lean_inc_ref(v_env_2453_);
v___x_2644_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2644_, 0, v_env_2453_);
lean_ctor_set(v___x_2644_, 1, v___x_2635_);
lean_ctor_set(v___x_2644_, 2, v___x_2636_);
lean_ctor_set(v___x_2644_, 3, v___x_2637_);
lean_ctor_set(v___x_2644_, 4, v___x_2638_);
lean_ctor_set(v___x_2644_, 5, v___x_2639_);
lean_ctor_set(v___x_2644_, 6, v___x_2641_);
lean_ctor_set(v___x_2644_, 7, v___x_2642_);
lean_ctor_set(v___x_2644_, 8, v___x_2643_);
lean_ctor_set(v___x_2644_, 9, v___x_2640_);
v___x_2645_ = lean_io_get_num_heartbeats();
v___x_2646_ = lean_st_mk_ref(v___x_2644_);
v___x_2647_ = l_Lean_inheritedTraceOptions;
v___x_2648_ = lean_st_ref_get(v___x_2647_);
lean_inc(v___x_2648_);
lean_inc(v___x_2645_);
v___x_2649_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2622_);
lean_ctor_set(v___x_2649_, 1, v___x_2623_);
lean_ctor_set(v___x_2649_, 2, v___x_2624_);
lean_ctor_set(v___x_2649_, 3, v___x_2625_);
lean_ctor_set(v___x_2649_, 4, v___x_2626_);
lean_ctor_set(v___x_2649_, 5, v___x_2627_);
lean_ctor_set(v___x_2649_, 6, v___x_2645_);
lean_ctor_set(v___x_2649_, 7, v___x_2629_);
lean_ctor_set(v___x_2649_, 8, v___x_2626_);
lean_ctor_set(v___x_2649_, 9, v___x_2630_);
lean_ctor_set(v___x_2649_, 10, v___x_2631_);
lean_ctor_set(v___x_2649_, 11, v___x_2648_);
v___x_2650_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2650_, 0, v___x_2649_);
lean_ctor_set(v___x_2650_, 1, v___x_2628_);
lean_ctor_set(v___x_2650_, 2, v___x_2632_);
lean_ctor_set_uint16(v___x_2650_, sizeof(void*)*3, v___x_2633_);
lean_ctor_set_uint8(v___x_2650_, sizeof(void*)*3 + 2, v___x_2634_);
lean_ctor_set_uint8(v___x_2650_, sizeof(void*)*3 + 3, v___x_2634_);
v___x_2651_ = lean_st_ref_get(v___x_2646_);
v_env_2652_ = lean_ctor_get(v___x_2651_, 0);
lean_inc_ref(v_env_2652_);
lean_dec(v___x_2651_);
v___x_2653_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2652_);
lean_dec_ref(v_env_2652_);
v___x_2654_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22);
if (v___x_2654_ == 0)
{
if (v___x_2653_ == 0)
{
lean_dec(v___x_2648_);
lean_dec(v___x_2645_);
v___y_2568_ = v___x_2634_;
v___y_2569_ = v___f_2621_;
v___y_2570_ = v___y_2614_;
v___y_2571_ = v___x_2650_;
v___y_2572_ = v___y_2614_;
v___y_2573_ = v___x_2628_;
v___y_2574_ = v___x_2624_;
v___y_2575_ = v___x_2633_;
v___y_2576_ = v___x_2646_;
v___y_2577_ = v___x_2639_;
goto v___jp_2567_;
}
else
{
lean_dec_ref_known(v___x_2650_, 3);
lean_inc(v___x_2646_);
v___y_2517_ = v___x_2634_;
v___y_2518_ = v___f_2621_;
v___y_2519_ = v___y_2614_;
v___y_2520_ = v___x_2628_;
v___y_2521_ = v___x_2624_;
v___y_2522_ = v___x_2646_;
v___y_2523_ = v___x_2633_;
v_fileName_2524_ = v___x_2622_;
v_fileMap_2525_ = v___x_2623_;
v_currNamespace_2526_ = v___x_2626_;
v_openDecls_2527_ = v___x_2627_;
v_initHeartbeats_2528_ = v___x_2645_;
v_maxHeartbeats_2529_ = v___x_2629_;
v_quotContext_2530_ = v___x_2626_;
v_currMacroScope_2531_ = v___x_2630_;
v_cancelTk_x3f_2532_ = v___x_2631_;
v_inheritedTraceOptions_2533_ = v___x_2648_;
v_currRecDepth_2534_ = v___x_2628_;
v_ref_2535_ = v___x_2632_;
v_suppressElabErrors_2536_ = v___x_2634_;
v_isRecordingDeps_2537_ = v___x_2634_;
v___y_2538_ = v___x_2646_;
goto v___jp_2516_;
}
}
else
{
if (v___x_2653_ == 0)
{
lean_dec_ref_known(v___x_2650_, 3);
lean_inc(v___x_2646_);
v___y_2517_ = v___x_2634_;
v___y_2518_ = v___f_2621_;
v___y_2519_ = v___y_2614_;
v___y_2520_ = v___x_2628_;
v___y_2521_ = v___x_2624_;
v___y_2522_ = v___x_2646_;
v___y_2523_ = v___x_2633_;
v_fileName_2524_ = v___x_2622_;
v_fileMap_2525_ = v___x_2623_;
v_currNamespace_2526_ = v___x_2626_;
v_openDecls_2527_ = v___x_2627_;
v_initHeartbeats_2528_ = v___x_2645_;
v_maxHeartbeats_2529_ = v___x_2629_;
v_quotContext_2530_ = v___x_2626_;
v_currMacroScope_2531_ = v___x_2630_;
v_cancelTk_x3f_2532_ = v___x_2631_;
v_inheritedTraceOptions_2533_ = v___x_2648_;
v_currRecDepth_2534_ = v___x_2628_;
v_ref_2535_ = v___x_2632_;
v_suppressElabErrors_2536_ = v___x_2634_;
v_isRecordingDeps_2537_ = v___x_2634_;
v___y_2538_ = v___x_2646_;
goto v___jp_2516_;
}
else
{
lean_dec(v___x_2648_);
lean_dec(v___x_2645_);
v___y_2568_ = v___x_2634_;
v___y_2569_ = v___f_2621_;
v___y_2570_ = v___y_2614_;
v___y_2571_ = v___x_2650_;
v___y_2572_ = v___x_2634_;
v___y_2573_ = v___x_2628_;
v___y_2574_ = v___x_2624_;
v___y_2575_ = v___x_2633_;
v___y_2576_ = v___x_2646_;
v___y_2577_ = v___x_2639_;
goto v___jp_2567_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_2450_ = stack[0].m_obj;
lean_object* v_linterOpts_2451_ = stack[1].m_obj;
lean_object* v_sp_2452_ = stack[2].m_obj;
lean_object* v_env_2453_ = stack[3].m_obj;
lean_object* v_pkgRoot_2454_ = stack[4].m_obj;
lean_object* v_docCheckedModules_2455_ = stack[5].m_obj;
lean_object* v_res_2660_;
v_res_2660_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(v_args_2450_, v_linterOpts_2451_, v_sp_2452_, v_env_2453_, v_pkgRoot_2454_, v_docCheckedModules_2455_);
stack->m_obj
 = v_res_2660_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___boxed(lean_object* v_args_2661_, lean_object* v_linterOpts_2662_, lean_object* v_sp_2663_, lean_object* v_env_2664_, lean_object* v_pkgRoot_2665_, lean_object* v_docCheckedModules_2666_, lean_object* v_a_2667_){
_start:
{
lean_object* v_res_2668_; 
v_res_2668_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(v_args_2661_, v_linterOpts_2662_, v_sp_2663_, v_env_2664_, v_pkgRoot_2665_, v_docCheckedModules_2666_);
lean_dec_ref(v_linterOpts_2662_);
lean_dec_ref(v_args_2661_);
return v_res_2668_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(lean_object* v_sp_2669_, uint8_t v___y_2670_, lean_object* v_as_2671_, size_t v_sz_2672_, size_t v_i_2673_, lean_object* v_b_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
lean_object* v___x_2678_; 
v___x_2678_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg(v_sp_2669_, v___y_2670_, v_as_2671_, v_sz_2672_, v_i_2673_, v_b_2674_, v___y_2675_);
return v___x_2678_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_sp_2669_ = stack[0].m_obj;
uint8_t v___y_2670_ = stack[1].m_num;
lean_object* v_as_2671_ = stack[2].m_obj;
size_t v_sz_2672_ = stack[3].m_num;
size_t v_i_2673_ = stack[4].m_num;
lean_object* v_b_2674_ = stack[5].m_obj;
lean_object* v___y_2675_ = stack[6].m_obj;
lean_object* v___y_2676_ = stack[7].m_obj;
lean_object* v_res_2679_;
v_res_2679_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(v_sp_2669_, v___y_2670_, v_as_2671_, v_sz_2672_, v_i_2673_, v_b_2674_, v___y_2675_, v___y_2676_);
stack->m_obj
 = v_res_2679_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___boxed(lean_object* v_sp_2680_, lean_object* v___y_2681_, lean_object* v_as_2682_, lean_object* v_sz_2683_, lean_object* v_i_2684_, lean_object* v_b_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_){
_start:
{
uint8_t v___y_9114__boxed_2689_; size_t v_sz_boxed_2690_; size_t v_i_boxed_2691_; lean_object* v_res_2692_; 
v___y_9114__boxed_2689_ = lean_unbox(v___y_2681_);
v_sz_boxed_2690_ = lean_unbox_usize(v_sz_2683_);
lean_dec(v_sz_2683_);
v_i_boxed_2691_ = lean_unbox_usize(v_i_2684_);
lean_dec(v_i_2684_);
v_res_2692_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(v_sp_2680_, v___y_9114__boxed_2689_, v_as_2682_, v_sz_boxed_2690_, v_i_boxed_2691_, v_b_2685_, v___y_2686_, v___y_2687_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec_ref(v_as_2682_);
return v_res_2692_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(lean_object* v_linterOpts_2693_, lean_object* v_as_2694_, size_t v_i_2695_, size_t v_stop_2696_, lean_object* v_b_2697_){
_start:
{
lean_object* v___y_2699_; uint8_t v___x_2703_; 
v___x_2703_ = lean_usize_dec_eq(v_i_2695_, v_stop_2696_);
if (v___x_2703_ == 0)
{
lean_object* v___x_2704_; lean_object* v_linter_2705_; uint8_t v___x_2706_; 
v___x_2704_ = lean_array_uget_borrowed(v_as_2694_, v_i_2695_);
v_linter_2705_ = lean_ctor_get(v___x_2704_, 0);
v___x_2706_ = l_Lean_Linter_isLinterEnabledByOptions(v_linter_2705_, v_linterOpts_2693_);
if (v___x_2706_ == 0)
{
v___y_2699_ = v_b_2697_;
goto v___jp_2698_;
}
else
{
lean_object* v___x_2707_; 
lean_inc(v___x_2704_);
v___x_2707_ = lean_array_push(v_b_2697_, v___x_2704_);
v___y_2699_ = v___x_2707_;
goto v___jp_2698_;
}
}
else
{
return v_b_2697_;
}
v___jp_2698_:
{
size_t v___x_2700_; size_t v___x_2701_; 
v___x_2700_ = ((size_t)1ULL);
v___x_2701_ = lean_usize_add(v_i_2695_, v___x_2700_);
v_i_2695_ = v___x_2701_;
v_b_2697_ = v___y_2699_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_linterOpts_2693_ = stack[0].m_obj;
lean_object* v_as_2694_ = stack[1].m_obj;
size_t v_i_2695_ = stack[2].m_num;
size_t v_stop_2696_ = stack[3].m_num;
lean_object* v_b_2697_ = stack[4].m_obj;
lean_object* v_res_2708_;
v_res_2708_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(v_linterOpts_2693_, v_as_2694_, v_i_2695_, v_stop_2696_, v_b_2697_);
stack->m_obj
 = v_res_2708_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1___boxed(lean_object* v_linterOpts_2709_, lean_object* v_as_2710_, lean_object* v_i_2711_, lean_object* v_stop_2712_, lean_object* v_b_2713_){
_start:
{
size_t v_i_boxed_2714_; size_t v_stop_boxed_2715_; lean_object* v_res_2716_; 
v_i_boxed_2714_ = lean_unbox_usize(v_i_2711_);
lean_dec(v_i_2711_);
v_stop_boxed_2715_ = lean_unbox_usize(v_stop_2712_);
lean_dec(v_stop_2712_);
v_res_2716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(v_linterOpts_2709_, v_as_2710_, v_i_boxed_2714_, v_stop_boxed_2715_, v_b_2713_);
lean_dec_ref(v_as_2710_);
lean_dec_ref(v_linterOpts_2709_);
return v_res_2716_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(lean_object* v_linterOpts_2719_, lean_object* v_as_2720_, size_t v_i_2721_, size_t v_stop_2722_, lean_object* v_b_2723_){
_start:
{
lean_object* v___y_2725_; uint8_t v___x_2729_; 
v___x_2729_ = lean_usize_dec_eq(v_i_2721_, v_stop_2722_);
if (v___x_2729_ == 0)
{
lean_object* v___x_2730_; lean_object* v_fst_2731_; lean_object* v_snd_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2756_; 
v___x_2730_ = lean_array_uget(v_as_2720_, v_i_2721_);
v_fst_2731_ = lean_ctor_get(v___x_2730_, 0);
v_snd_2732_ = lean_ctor_get(v___x_2730_, 1);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2734_ = v___x_2730_;
v_isShared_2735_ = v_isSharedCheck_2756_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_snd_2732_);
lean_inc(v_fst_2731_);
lean_dec(v___x_2730_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2756_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___y_2737_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; uint8_t v___x_2748_; 
v___x_2745_ = lean_unsigned_to_nat(0u);
v___x_2746_ = lean_array_get_size(v_snd_2732_);
v___x_2747_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9___closed__0));
v___x_2748_ = lean_nat_dec_lt(v___x_2745_, v___x_2746_);
if (v___x_2748_ == 0)
{
lean_dec(v_snd_2732_);
v___y_2737_ = v___x_2747_;
goto v___jp_2736_;
}
else
{
uint8_t v___x_2749_; 
v___x_2749_ = lean_nat_dec_le(v___x_2746_, v___x_2746_);
if (v___x_2749_ == 0)
{
if (v___x_2748_ == 0)
{
lean_dec(v_snd_2732_);
v___y_2737_ = v___x_2747_;
goto v___jp_2736_;
}
else
{
size_t v___x_2750_; size_t v___x_2751_; lean_object* v___x_2752_; 
v___x_2750_ = ((size_t)0ULL);
v___x_2751_ = lean_usize_of_nat(v___x_2746_);
v___x_2752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(v_linterOpts_2719_, v_snd_2732_, v___x_2750_, v___x_2751_, v___x_2747_);
lean_dec(v_snd_2732_);
v___y_2737_ = v___x_2752_;
goto v___jp_2736_;
}
}
else
{
size_t v___x_2753_; size_t v___x_2754_; lean_object* v___x_2755_; 
v___x_2753_ = ((size_t)0ULL);
v___x_2754_ = lean_usize_of_nat(v___x_2746_);
v___x_2755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(v_linterOpts_2719_, v_snd_2732_, v___x_2753_, v___x_2754_, v___x_2747_);
lean_dec(v_snd_2732_);
v___y_2737_ = v___x_2755_;
goto v___jp_2736_;
}
}
v___jp_2736_:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; uint8_t v___x_2740_; 
v___x_2738_ = lean_array_get_size(v___y_2737_);
v___x_2739_ = lean_unsigned_to_nat(0u);
v___x_2740_ = lean_nat_dec_eq(v___x_2738_, v___x_2739_);
if (v___x_2740_ == 0)
{
lean_object* v___x_2742_; 
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 1, v___y_2737_);
v___x_2742_ = v___x_2734_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_fst_2731_);
lean_ctor_set(v_reuseFailAlloc_2744_, 1, v___y_2737_);
v___x_2742_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
lean_object* v___x_2743_; 
v___x_2743_ = lean_array_push(v_b_2723_, v___x_2742_);
v___y_2725_ = v___x_2743_;
goto v___jp_2724_;
}
}
else
{
lean_dec_ref(v___y_2737_);
lean_del_object(v___x_2734_);
lean_dec(v_fst_2731_);
v___y_2725_ = v_b_2723_;
goto v___jp_2724_;
}
}
}
}
else
{
return v_b_2723_;
}
v___jp_2724_:
{
size_t v___x_2726_; size_t v___x_2727_; 
v___x_2726_ = ((size_t)1ULL);
v___x_2727_ = lean_usize_add(v_i_2721_, v___x_2726_);
v_i_2721_ = v___x_2727_;
v_b_2723_ = v___y_2725_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_linterOpts_2719_ = stack[0].m_obj;
lean_object* v_as_2720_ = stack[1].m_obj;
size_t v_i_2721_ = stack[2].m_num;
size_t v_stop_2722_ = stack[3].m_num;
lean_object* v_b_2723_ = stack[4].m_obj;
lean_object* v_res_2757_;
v_res_2757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2719_, v_as_2720_, v_i_2721_, v_stop_2722_, v_b_2723_);
stack->m_obj
 = v_res_2757_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9___boxed(lean_object* v_linterOpts_2758_, lean_object* v_as_2759_, lean_object* v_i_2760_, lean_object* v_stop_2761_, lean_object* v_b_2762_){
_start:
{
size_t v_i_boxed_2763_; size_t v_stop_boxed_2764_; lean_object* v_res_2765_; 
v_i_boxed_2763_ = lean_unbox_usize(v_i_2760_);
lean_dec(v_i_2760_);
v_stop_boxed_2764_ = lean_unbox_usize(v_stop_2761_);
lean_dec(v_stop_2761_);
v_res_2765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2758_, v_as_2759_, v_i_boxed_2763_, v_stop_boxed_2764_, v_b_2762_);
lean_dec_ref(v_as_2759_);
lean_dec_ref(v_linterOpts_2758_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(lean_object* v_linterOpts_2766_, lean_object* v_as_2767_, lean_object* v_start_2768_, lean_object* v_stop_2769_){
_start:
{
lean_object* v___x_2770_; uint8_t v___x_2771_; 
v___x_2770_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0));
v___x_2771_ = lean_nat_dec_lt(v_start_2768_, v_stop_2769_);
if (v___x_2771_ == 0)
{
return v___x_2770_;
}
else
{
lean_object* v___x_2772_; uint8_t v___x_2773_; 
v___x_2772_ = lean_array_get_size(v_as_2767_);
v___x_2773_ = lean_nat_dec_le(v_stop_2769_, v___x_2772_);
if (v___x_2773_ == 0)
{
uint8_t v___x_2774_; 
v___x_2774_ = lean_nat_dec_lt(v_start_2768_, v___x_2772_);
if (v___x_2774_ == 0)
{
return v___x_2770_;
}
else
{
size_t v___x_2775_; size_t v___x_2776_; lean_object* v___x_2777_; 
v___x_2775_ = lean_usize_of_nat(v_start_2768_);
v___x_2776_ = lean_usize_of_nat(v___x_2772_);
v___x_2777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2766_, v_as_2767_, v___x_2775_, v___x_2776_, v___x_2770_);
return v___x_2777_;
}
}
else
{
size_t v___x_2778_; size_t v___x_2779_; lean_object* v___x_2780_; 
v___x_2778_ = lean_usize_of_nat(v_start_2768_);
v___x_2779_ = lean_usize_of_nat(v_stop_2769_);
v___x_2780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2766_, v_as_2767_, v___x_2778_, v___x_2779_, v___x_2770_);
return v___x_2780_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9___boxed(lean_object* v_linterOpts_2781_, lean_object* v_as_2782_, lean_object* v_start_2783_, lean_object* v_stop_2784_){
_start:
{
lean_object* v_res_2785_; 
v_res_2785_ = l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(v_linterOpts_2781_, v_as_2782_, v_start_2783_, v_stop_2784_);
lean_dec(v_stop_2784_);
lean_dec(v_start_2783_);
lean_dec_ref(v_as_2782_);
lean_dec_ref(v_linterOpts_2781_);
return v_res_2785_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(lean_object* v_fst_2786_, lean_object* v_init_2787_, lean_object* v_x_2788_){
_start:
{
if (lean_obj_tag(v_x_2788_) == 0)
{
lean_object* v_k_2790_; lean_object* v_v_2791_; lean_object* v_l_2792_; lean_object* v_r_2793_; uint8_t v_anyUnlocated_2794_; lean_object* v___x_2795_; lean_object* v_a_2796_; lean_object* v_a_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2810_; 
v_k_2790_ = lean_ctor_get(v_x_2788_, 1);
lean_inc(v_k_2790_);
v_v_2791_ = lean_ctor_get(v_x_2788_, 2);
lean_inc(v_v_2791_);
v_l_2792_ = lean_ctor_get(v_x_2788_, 3);
lean_inc(v_l_2792_);
v_r_2793_ = lean_ctor_get(v_x_2788_, 4);
lean_inc(v_r_2793_);
lean_dec_ref_known(v_x_2788_, 5);
v_anyUnlocated_2794_ = 1;
lean_inc(v_fst_2786_);
v___x_2795_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2786_, v_init_2787_, v_l_2792_);
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
lean_inc(v_a_2796_);
lean_dec_ref(v___x_2795_);
v_a_2797_ = lean_ctor_get(v_a_2796_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v_a_2796_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2799_ = v_a_2796_;
v_isShared_2800_ = v_isSharedCheck_2810_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_a_2797_);
lean_dec(v_a_2796_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2810_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2801_; lean_object* v___x_2803_; 
v___x_2801_ = l_Lean_Name_toString(v_k_2790_, v_anyUnlocated_2794_);
lean_inc(v_fst_2786_);
if (v_isShared_2800_ == 0)
{
lean_ctor_set_tag(v___x_2799_, 0);
lean_ctor_set(v___x_2799_, 0, v_fst_2786_);
v___x_2803_ = v___x_2799_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_fst_2786_);
v___x_2803_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
double v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2804_ = lean_float_of_nat(v_v_2791_);
v___x_2805_ = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_float(v___x_2805_, 0, v___x_2804_);
v___x_2806_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2801_);
lean_ctor_set(v___x_2806_, 1, v___x_2803_);
lean_ctor_set(v___x_2806_, 2, v___x_2805_);
v___x_2807_ = lean_array_push(v_a_2797_, v___x_2806_);
v_init_2787_ = v___x_2807_;
v_x_2788_ = v_r_2793_;
goto _start;
}
}
}
else
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
lean_dec(v_fst_2786_);
v___x_2811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2811_, 0, v_init_2787_);
v___x_2812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2811_);
return v___x_2812_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_2786_ = stack[0].m_obj;
lean_object* v_init_2787_ = stack[1].m_obj;
lean_object* v_x_2788_ = stack[2].m_obj;
lean_object* v_res_2813_;
v_res_2813_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2786_, v_init_2787_, v_x_2788_);
stack->m_obj
 = v_res_2813_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3___boxed(lean_object* v_fst_2814_, lean_object* v_init_2815_, lean_object* v_x_2816_, lean_object* v___y_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2814_, v_init_2815_, v_x_2816_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(lean_object* v_t_2819_, lean_object* v_k_2820_, lean_object* v_fallback_2821_){
_start:
{
if (lean_obj_tag(v_t_2819_) == 0)
{
lean_object* v_k_2822_; lean_object* v_v_2823_; lean_object* v_l_2824_; lean_object* v_r_2825_; uint8_t v___x_2826_; 
v_k_2822_ = lean_ctor_get(v_t_2819_, 1);
v_v_2823_ = lean_ctor_get(v_t_2819_, 2);
v_l_2824_ = lean_ctor_get(v_t_2819_, 3);
v_r_2825_ = lean_ctor_get(v_t_2819_, 4);
v___x_2826_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2820_, v_k_2822_);
switch(v___x_2826_)
{
case 0:
{
v_t_2819_ = v_l_2824_;
goto _start;
}
case 1:
{
lean_inc(v_v_2823_);
return v_v_2823_;
}
default: 
{
v_t_2819_ = v_r_2825_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2821_);
return v_fallback_2821_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg___boxed(lean_object* v_t_2829_, lean_object* v_k_2830_, lean_object* v_fallback_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(v_t_2829_, v_k_2830_, v_fallback_2831_);
lean_dec(v_fallback_2831_);
lean_dec(v_k_2830_);
lean_dec(v_t_2829_);
return v_res_2832_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(lean_object* v_as_2833_, size_t v_i_2834_, size_t v_stop_2835_, lean_object* v_b_2836_){
_start:
{
uint8_t v___x_2837_; 
v___x_2837_ = lean_usize_dec_eq(v_i_2834_, v_stop_2835_);
if (v___x_2837_ == 0)
{
lean_object* v___x_2838_; lean_object* v_linter_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; size_t v___x_2845_; size_t v___x_2846_; 
v___x_2838_ = lean_array_uget_borrowed(v_as_2833_, v_i_2834_);
v_linter_2839_ = lean_ctor_get(v___x_2838_, 0);
v___x_2840_ = lean_unsigned_to_nat(0u);
v___x_2841_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(v_b_2836_, v_linter_2839_, v___x_2840_);
v___x_2842_ = lean_unsigned_to_nat(1u);
v___x_2843_ = lean_nat_add(v___x_2841_, v___x_2842_);
lean_dec(v___x_2841_);
lean_inc(v_linter_2839_);
v___x_2844_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_linter_2839_, v___x_2843_, v_b_2836_);
v___x_2845_ = ((size_t)1ULL);
v___x_2846_ = lean_usize_add(v_i_2834_, v___x_2845_);
v_i_2834_ = v___x_2846_;
v_b_2836_ = v___x_2844_;
goto _start;
}
else
{
return v_b_2836_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2833_ = stack[0].m_obj;
size_t v_i_2834_ = stack[1].m_num;
size_t v_stop_2835_ = stack[2].m_num;
lean_object* v_b_2836_ = stack[3].m_obj;
lean_object* v_res_2848_;
v_res_2848_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_as_2833_, v_i_2834_, v_stop_2835_, v_b_2836_);
stack->m_obj
 = v_res_2848_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4___boxed(lean_object* v_as_2849_, lean_object* v_i_2850_, lean_object* v_stop_2851_, lean_object* v_b_2852_){
_start:
{
size_t v_i_boxed_2853_; size_t v_stop_boxed_2854_; lean_object* v_res_2855_; 
v_i_boxed_2853_ = lean_unbox_usize(v_i_2850_);
lean_dec(v_i_2850_);
v_stop_boxed_2854_ = lean_unbox_usize(v_stop_2851_);
lean_dec(v_stop_2851_);
v_res_2855_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_as_2849_, v_i_boxed_2853_, v_stop_boxed_2854_, v_b_2852_);
lean_dec_ref(v_as_2849_);
return v_res_2855_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(lean_object* v_as_2856_, size_t v_sz_2857_, size_t v_i_2858_, lean_object* v_b_2859_){
_start:
{
lean_object* v_a_2862_; uint8_t v___x_2866_; 
v___x_2866_ = lean_usize_dec_lt(v_i_2858_, v_sz_2857_);
if (v___x_2866_ == 0)
{
lean_object* v___x_2867_; 
v___x_2867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2867_, 0, v_b_2859_);
return v___x_2867_;
}
else
{
lean_object* v_a_2868_; lean_object* v_fst_2869_; lean_object* v_snd_2870_; lean_object* v___y_2872_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; uint8_t v___x_2897_; 
v_a_2868_ = lean_array_uget_borrowed(v_as_2856_, v_i_2858_);
v_fst_2869_ = lean_ctor_get(v_a_2868_, 0);
v_snd_2870_ = lean_ctor_get(v_a_2868_, 1);
v___x_2894_ = lean_box(1);
v___x_2895_ = lean_unsigned_to_nat(0u);
v___x_2896_ = lean_array_get_size(v_snd_2870_);
v___x_2897_ = lean_nat_dec_lt(v___x_2895_, v___x_2896_);
if (v___x_2897_ == 0)
{
v___y_2872_ = v___x_2894_;
goto v___jp_2871_;
}
else
{
uint8_t v___x_2898_; 
v___x_2898_ = lean_nat_dec_le(v___x_2896_, v___x_2896_);
if (v___x_2898_ == 0)
{
if (v___x_2897_ == 0)
{
v___y_2872_ = v___x_2894_;
goto v___jp_2871_;
}
else
{
size_t v___x_2899_; size_t v___x_2900_; lean_object* v___x_2901_; 
v___x_2899_ = ((size_t)0ULL);
v___x_2900_ = lean_usize_of_nat(v___x_2896_);
v___x_2901_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_snd_2870_, v___x_2899_, v___x_2900_, v___x_2894_);
v___y_2872_ = v___x_2901_;
goto v___jp_2871_;
}
}
else
{
size_t v___x_2902_; size_t v___x_2903_; lean_object* v___x_2904_; 
v___x_2902_ = ((size_t)0ULL);
v___x_2903_ = lean_usize_of_nat(v___x_2896_);
v___x_2904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_snd_2870_, v___x_2902_, v___x_2903_, v___x_2894_);
v___y_2872_ = v___x_2904_;
goto v___jp_2871_;
}
}
v___jp_2871_:
{
lean_object* v___x_2873_; 
lean_inc(v_fst_2869_);
v___x_2873_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2869_, v_b_2859_, v___y_2872_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; lean_object* v_a_2875_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
lean_dec_ref_known(v___x_2873_, 1);
v_a_2875_ = lean_ctor_get(v_a_2874_, 0);
lean_inc(v_a_2875_);
lean_dec(v_a_2874_);
v_a_2862_ = v_a_2875_;
goto v___jp_2861_;
}
else
{
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2885_; 
v_a_2876_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2878_ = v___x_2873_;
v_isShared_2879_ = v_isSharedCheck_2885_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2873_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2885_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
if (lean_obj_tag(v_a_2876_) == 0)
{
lean_object* v_a_2880_; lean_object* v___x_2882_; 
v_a_2880_ = lean_ctor_get(v_a_2876_, 0);
lean_inc(v_a_2880_);
lean_dec_ref_known(v_a_2876_, 1);
if (v_isShared_2879_ == 0)
{
lean_ctor_set_tag(v___x_2878_, 0);
lean_ctor_set(v___x_2878_, 0, v_a_2880_);
v___x_2882_ = v___x_2878_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_a_2880_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
return v___x_2882_;
}
}
else
{
lean_object* v_a_2884_; 
lean_del_object(v___x_2878_);
v_a_2884_ = lean_ctor_get(v_a_2876_, 0);
lean_inc(v_a_2884_);
lean_dec_ref_known(v_a_2876_, 1);
v_a_2862_ = v_a_2884_;
goto v___jp_2861_;
}
}
}
else
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
v_a_2886_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2888_ = v___x_2873_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2873_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2886_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
}
}
}
v___jp_2861_:
{
size_t v___x_2863_; size_t v___x_2864_; 
v___x_2863_ = ((size_t)1ULL);
v___x_2864_ = lean_usize_add(v_i_2858_, v___x_2863_);
v_i_2858_ = v___x_2864_;
v_b_2859_ = v_a_2862_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2856_ = stack[0].m_obj;
size_t v_sz_2857_ = stack[1].m_num;
size_t v_i_2858_ = stack[2].m_num;
lean_object* v_b_2859_ = stack[3].m_obj;
lean_object* v_res_2905_;
v_res_2905_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(v_as_2856_, v_sz_2857_, v_i_2858_, v_b_2859_);
stack->m_obj
 = v_res_2905_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8___boxed(lean_object* v_as_2906_, lean_object* v_sz_2907_, lean_object* v_i_2908_, lean_object* v_b_2909_, lean_object* v___y_2910_){
_start:
{
size_t v_sz_boxed_2911_; size_t v_i_boxed_2912_; lean_object* v_res_2913_; 
v_sz_boxed_2911_ = lean_unbox_usize(v_sz_2907_);
lean_dec(v_sz_2907_);
v_i_boxed_2912_ = lean_unbox_usize(v_i_2908_);
lean_dec(v_i_2908_);
v_res_2913_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(v_as_2906_, v_sz_boxed_2911_, v_i_boxed_2912_, v_b_2909_);
lean_dec_ref(v_as_2906_);
return v_res_2913_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(lean_object* v_fst_2917_, lean_object* v_as_2918_, size_t v_sz_2919_, size_t v_i_2920_, lean_object* v_b_2921_){
_start:
{
lean_object* v_a_2924_; uint8_t v_anyUnlocated_2928_; 
v_anyUnlocated_2928_ = lean_usize_dec_lt(v_i_2920_, v_sz_2919_);
if (v_anyUnlocated_2928_ == 0)
{
lean_object* v___x_2929_; 
lean_dec(v_fst_2917_);
v___x_2929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2929_, 0, v_b_2921_);
return v___x_2929_;
}
else
{
lean_object* v_fst_2930_; lean_object* v_snd_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2968_; 
v_fst_2930_ = lean_ctor_get(v_b_2921_, 0);
v_snd_2931_ = lean_ctor_get(v_b_2921_, 1);
v_isSharedCheck_2968_ = !lean_is_exclusive(v_b_2921_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2933_ = v_b_2921_;
v_isShared_2934_ = v_isSharedCheck_2968_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_snd_2931_);
lean_inc(v_fst_2930_);
lean_dec(v_b_2921_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2968_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v_a_2935_; lean_object* v_position_x3f_2936_; 
v_a_2935_ = lean_array_uget_borrowed(v_as_2918_, v_i_2920_);
v_position_x3f_2936_ = lean_ctor_get(v_a_2935_, 2);
if (lean_obj_tag(v_position_x3f_2936_) == 0)
{
lean_object* v_linter_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; 
lean_dec(v_snd_2931_);
v_linter_2937_ = lean_ctor_get(v_a_2935_, 0);
v___x_2938_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__0));
lean_inc(v_linter_2937_);
v___x_2939_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_linter_2937_, v_anyUnlocated_2928_);
v___x_2940_ = lean_string_append(v___x_2938_, v___x_2939_);
lean_dec_ref(v___x_2939_);
v___x_2941_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__1));
v___x_2942_ = lean_string_append(v___x_2940_, v___x_2941_);
lean_inc(v_fst_2917_);
v___x_2943_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2917_, v_anyUnlocated_2928_);
v___x_2944_ = lean_string_append(v___x_2942_, v___x_2943_);
lean_dec_ref(v___x_2943_);
v___x_2945_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__2));
v___x_2946_ = lean_string_append(v___x_2944_, v___x_2945_);
v___x_2947_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2946_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v___x_2948_; lean_object* v___x_2950_; 
lean_dec_ref_known(v___x_2947_, 1);
v___x_2948_ = lean_box(v_anyUnlocated_2928_);
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 1, v___x_2948_);
v___x_2950_ = v___x_2933_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_fst_2930_);
lean_ctor_set(v_reuseFailAlloc_2951_, 1, v___x_2948_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
v_a_2924_ = v___x_2950_;
goto v___jp_2923_;
}
}
else
{
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2959_; 
lean_del_object(v___x_2933_);
lean_dec(v_fst_2930_);
lean_dec(v_fst_2917_);
v_a_2952_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2954_ = v___x_2947_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2947_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2952_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
else
{
lean_object* v_linter_2960_; lean_object* v_file_2961_; lean_object* v_val_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2966_; 
v_linter_2960_ = lean_ctor_get(v_a_2935_, 0);
v_file_2961_ = lean_ctor_get(v_a_2935_, 3);
v_val_2962_ = lean_ctor_get(v_position_x3f_2936_, 0);
lean_inc(v_linter_2960_);
lean_inc(v_val_2962_);
lean_inc_ref(v_file_2961_);
v___x_2963_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2963_, 0, v_file_2961_);
lean_ctor_set(v___x_2963_, 1, v_val_2962_);
lean_ctor_set(v___x_2963_, 2, v_linter_2960_);
v___x_2964_ = lean_array_push(v_fst_2930_, v___x_2963_);
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 0, v___x_2964_);
v___x_2966_ = v___x_2933_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v___x_2964_);
lean_ctor_set(v_reuseFailAlloc_2967_, 1, v_snd_2931_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
v_a_2924_ = v___x_2966_;
goto v___jp_2923_;
}
}
}
}
v___jp_2923_:
{
size_t v___x_2925_; size_t v___x_2926_; 
v___x_2925_ = ((size_t)1ULL);
v___x_2926_ = lean_usize_add(v_i_2920_, v___x_2925_);
v_i_2920_ = v___x_2926_;
v_b_2921_ = v_a_2924_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_2917_ = stack[0].m_obj;
lean_object* v_as_2918_ = stack[1].m_obj;
size_t v_sz_2919_ = stack[2].m_num;
size_t v_i_2920_ = stack[3].m_num;
lean_object* v_b_2921_ = stack[4].m_obj;
lean_object* v_res_2969_;
v_res_2969_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(v_fst_2917_, v_as_2918_, v_sz_2919_, v_i_2920_, v_b_2921_);
stack->m_obj
 = v_res_2969_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___boxed(lean_object* v_fst_2970_, lean_object* v_as_2971_, lean_object* v_sz_2972_, lean_object* v_i_2973_, lean_object* v_b_2974_, lean_object* v___y_2975_){
_start:
{
size_t v_sz_boxed_2976_; size_t v_i_boxed_2977_; lean_object* v_res_2978_; 
v_sz_boxed_2976_ = lean_unbox_usize(v_sz_2972_);
lean_dec(v_sz_2972_);
v_i_boxed_2977_ = lean_unbox_usize(v_i_2973_);
lean_dec(v_i_2973_);
v_res_2978_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(v_fst_2970_, v_as_2971_, v_sz_boxed_2976_, v_i_boxed_2977_, v_b_2974_);
lean_dec_ref(v_as_2971_);
return v_res_2978_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(lean_object* v_as_2979_, size_t v_sz_2980_, size_t v_i_2981_, lean_object* v_b_2982_){
_start:
{
uint8_t v___x_2984_; 
v___x_2984_ = lean_usize_dec_lt(v_i_2981_, v_sz_2980_);
if (v___x_2984_ == 0)
{
lean_object* v___x_2985_; 
v___x_2985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2985_, 0, v_b_2982_);
return v___x_2985_;
}
else
{
lean_object* v_a_2986_; lean_object* v_fst_2987_; lean_object* v_snd_2988_; lean_object* v_fst_2989_; lean_object* v_snd_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3013_; 
v_a_2986_ = lean_array_uget_borrowed(v_as_2979_, v_i_2981_);
v_fst_2987_ = lean_ctor_get(v_a_2986_, 0);
v_snd_2988_ = lean_ctor_get(v_a_2986_, 1);
v_fst_2989_ = lean_ctor_get(v_b_2982_, 0);
v_snd_2990_ = lean_ctor_get(v_b_2982_, 1);
v_isSharedCheck_3013_ = !lean_is_exclusive(v_b_2982_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_2992_ = v_b_2982_;
v_isShared_2993_ = v_isSharedCheck_3013_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_snd_2990_);
lean_inc(v_fst_2989_);
lean_dec(v_b_2982_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3013_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2995_; 
if (v_isShared_2993_ == 0)
{
v___x_2995_ = v___x_2992_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_fst_2989_);
lean_ctor_set(v_reuseFailAlloc_3012_, 1, v_snd_2990_);
v___x_2995_ = v_reuseFailAlloc_3012_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
size_t v_sz_2996_; size_t v___x_2997_; lean_object* v___x_2998_; 
v_sz_2996_ = lean_array_size(v_snd_2988_);
v___x_2997_ = ((size_t)0ULL);
lean_inc(v_fst_2987_);
v___x_2998_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(v_fst_2987_, v_snd_2988_, v_sz_2996_, v___x_2997_, v___x_2995_);
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_object* v_a_2999_; lean_object* v_fst_3000_; lean_object* v_snd_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3011_; 
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
lean_inc(v_a_2999_);
lean_dec_ref_known(v___x_2998_, 1);
v_fst_3000_ = lean_ctor_get(v_a_2999_, 0);
v_snd_3001_ = lean_ctor_get(v_a_2999_, 1);
v_isSharedCheck_3011_ = !lean_is_exclusive(v_a_2999_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_3003_ = v_a_2999_;
v_isShared_3004_ = v_isSharedCheck_3011_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_snd_3001_);
lean_inc(v_fst_3000_);
lean_dec(v_a_2999_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3011_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3006_; 
if (v_isShared_3004_ == 0)
{
v___x_3006_ = v___x_3003_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_fst_3000_);
lean_ctor_set(v_reuseFailAlloc_3010_, 1, v_snd_3001_);
v___x_3006_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
size_t v___x_3007_; size_t v___x_3008_; 
v___x_3007_ = ((size_t)1ULL);
v___x_3008_ = lean_usize_add(v_i_2981_, v___x_3007_);
v_i_2981_ = v___x_3008_;
v_b_2982_ = v___x_3006_;
goto _start;
}
}
}
else
{
return v___x_2998_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2979_ = stack[0].m_obj;
size_t v_sz_2980_ = stack[1].m_num;
size_t v_i_2981_ = stack[2].m_num;
lean_object* v_b_2982_ = stack[3].m_obj;
lean_object* v_res_3014_;
v_res_3014_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(v_as_2979_, v_sz_2980_, v_i_2981_, v_b_2982_);
stack->m_obj
 = v_res_3014_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7___boxed(lean_object* v_as_3015_, lean_object* v_sz_3016_, lean_object* v_i_3017_, lean_object* v_b_3018_, lean_object* v___y_3019_){
_start:
{
size_t v_sz_boxed_3020_; size_t v_i_boxed_3021_; lean_object* v_res_3022_; 
v_sz_boxed_3020_ = lean_unbox_usize(v_sz_3016_);
lean_dec(v_sz_3016_);
v_i_boxed_3021_ = lean_unbox_usize(v_i_3017_);
lean_dec(v_i_3017_);
v_res_3022_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(v_as_3015_, v_sz_boxed_3020_, v_i_boxed_3021_, v_b_3018_);
lean_dec_ref(v_as_3015_);
return v_res_3022_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(lean_object* v_as_3023_, size_t v_sz_3024_, size_t v_i_3025_, lean_object* v_b_3026_){
_start:
{
uint8_t v___x_3028_; 
v___x_3028_ = lean_usize_dec_lt(v_i_3025_, v_sz_3024_);
if (v___x_3028_ == 0)
{
lean_object* v___x_3029_; 
v___x_3029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3029_, 0, v_b_3026_);
return v___x_3029_;
}
else
{
lean_object* v_a_3030_; lean_object* v_message_3031_; lean_object* v___x_3032_; uint8_t v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v_a_3030_ = lean_array_uget_borrowed(v_as_3023_, v_i_3025_);
v_message_3031_ = lean_ctor_get(v_a_3030_, 1);
v___x_3032_ = lean_box(0);
v___x_3033_ = 0;
lean_inc_ref(v_message_3031_);
v___x_3034_ = l_Lean_SerialMessage_toString(v_message_3031_, v___x_3033_);
v___x_3035_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_3034_);
if (lean_obj_tag(v___x_3035_) == 0)
{
size_t v___x_3036_; size_t v___x_3037_; 
lean_dec_ref_known(v___x_3035_, 1);
v___x_3036_ = ((size_t)1ULL);
v___x_3037_ = lean_usize_add(v_i_3025_, v___x_3036_);
v_i_3025_ = v___x_3037_;
v_b_3026_ = v___x_3032_;
goto _start;
}
else
{
return v___x_3035_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3023_ = stack[0].m_obj;
size_t v_sz_3024_ = stack[1].m_num;
size_t v_i_3025_ = stack[2].m_num;
lean_object* v_b_3026_ = stack[3].m_obj;
lean_object* v_res_3039_;
v_res_3039_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(v_as_3023_, v_sz_3024_, v_i_3025_, v_b_3026_);
stack->m_obj
 = v_res_3039_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5___boxed(lean_object* v_as_3040_, lean_object* v_sz_3041_, lean_object* v_i_3042_, lean_object* v_b_3043_, lean_object* v___y_3044_){
_start:
{
size_t v_sz_boxed_3045_; size_t v_i_boxed_3046_; lean_object* v_res_3047_; 
v_sz_boxed_3045_ = lean_unbox_usize(v_sz_3041_);
lean_dec(v_sz_3041_);
v_i_boxed_3046_ = lean_unbox_usize(v_i_3042_);
lean_dec(v_i_3042_);
v_res_3047_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(v_as_3040_, v_sz_boxed_3045_, v_i_boxed_3046_, v_b_3043_);
lean_dec_ref(v_as_3040_);
return v_res_3047_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(lean_object* v_as_3050_, size_t v_sz_3051_, size_t v_i_3052_, lean_object* v_b_3053_){
_start:
{
uint8_t v___x_3055_; 
v___x_3055_ = lean_usize_dec_lt(v_i_3052_, v_sz_3051_);
if (v___x_3055_ == 0)
{
lean_object* v___x_3056_; 
v___x_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3056_, 0, v_b_3053_);
return v___x_3056_;
}
else
{
lean_object* v_a_3057_; lean_object* v_fst_3058_; lean_object* v_snd_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
v_a_3057_ = lean_array_uget_borrowed(v_as_3050_, v_i_3052_);
v_fst_3058_ = lean_ctor_get(v_a_3057_, 0);
v_snd_3059_ = lean_ctor_get(v_a_3057_, 1);
v___x_3060_ = lean_box(0);
v___x_3061_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___closed__0));
lean_inc(v_fst_3058_);
v___x_3062_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_3058_, v___x_3055_);
v___x_3063_ = lean_string_append(v___x_3061_, v___x_3062_);
lean_dec_ref(v___x_3062_);
v___x_3064_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___closed__1));
v___x_3065_ = lean_string_append(v___x_3063_, v___x_3064_);
v___x_3066_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_3065_);
if (lean_obj_tag(v___x_3066_) == 0)
{
size_t v_sz_3067_; size_t v___x_3068_; lean_object* v___x_3069_; 
lean_dec_ref_known(v___x_3066_, 1);
v_sz_3067_ = lean_array_size(v_snd_3059_);
v___x_3068_ = ((size_t)0ULL);
v___x_3069_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(v_snd_3059_, v_sz_3067_, v___x_3068_, v___x_3060_);
if (lean_obj_tag(v___x_3069_) == 0)
{
size_t v___x_3070_; size_t v___x_3071_; 
lean_dec_ref_known(v___x_3069_, 1);
v___x_3070_ = ((size_t)1ULL);
v___x_3071_ = lean_usize_add(v_i_3052_, v___x_3070_);
v_i_3052_ = v___x_3071_;
v_b_3053_ = v___x_3060_;
goto _start;
}
else
{
return v___x_3069_;
}
}
else
{
return v___x_3066_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3050_ = stack[0].m_obj;
size_t v_sz_3051_ = stack[1].m_num;
size_t v_i_3052_ = stack[2].m_num;
lean_object* v_b_3053_ = stack[3].m_obj;
lean_object* v_res_3073_;
v_res_3073_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(v_as_3050_, v_sz_3051_, v_i_3052_, v_b_3053_);
stack->m_obj
 = v_res_3073_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___boxed(lean_object* v_as_3074_, lean_object* v_sz_3075_, lean_object* v_i_3076_, lean_object* v_b_3077_, lean_object* v___y_3078_){
_start:
{
size_t v_sz_boxed_3079_; size_t v_i_boxed_3080_; lean_object* v_res_3081_; 
v_sz_boxed_3079_ = lean_unbox_usize(v_sz_3075_);
lean_dec(v_sz_3075_);
v_i_boxed_3080_ = lean_unbox_usize(v_i_3076_);
lean_dec(v_i_3076_);
v_res_3081_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(v_as_3074_, v_sz_boxed_3079_, v_i_boxed_3080_, v_b_3077_);
lean_dec_ref(v_as_3074_);
return v_res_3081_;
}
}
lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(lean_object* v_args_3086_, lean_object* v_linterOpts_3087_, lean_object* v_env_3088_, lean_object* v_mod_3089_){
_start:
{
uint8_t v_lintOnly_3091_; uint8_t v_mode_3092_; lean_object* v___y_3094_; uint8_t v___y_3095_; lean_object* v___y_3163_; lean_object* v___x_3169_; lean_object* v_textGroups_3170_; 
v_lintOnly_3091_ = lean_ctor_get_uint8(v_args_3086_, sizeof(void*)*4);
v_mode_3092_ = lean_ctor_get_uint8(v_args_3086_, sizeof(void*)*4 + 1);
v___x_3169_ = l_Lean_Name_getRoot(v_mod_3089_);
v_textGroups_3170_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(v_env_3088_, v___x_3169_);
lean_dec(v___x_3169_);
if (v_lintOnly_3091_ == 0)
{
v___y_3163_ = v_textGroups_3170_;
goto v___jp_3162_;
}
else
{
lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3171_ = lean_unsigned_to_nat(0u);
v___x_3172_ = lean_array_get_size(v_textGroups_3170_);
v___x_3173_ = l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(v_linterOpts_3087_, v_textGroups_3170_, v___x_3171_, v___x_3172_);
lean_dec_ref(v_textGroups_3170_);
v___y_3163_ = v___x_3173_;
goto v___jp_3162_;
}
v___jp_3093_:
{
switch(v_mode_3092_)
{
case 0:
{
lean_object* v___x_3096_; size_t v_sz_3097_; size_t v___x_3098_; lean_object* v___x_3099_; 
v___x_3096_ = lean_box(0);
v_sz_3097_ = lean_array_size(v___y_3094_);
v___x_3098_ = ((size_t)0ULL);
v___x_3099_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(v___y_3094_, v_sz_3097_, v___x_3098_, v___x_3096_);
lean_dec_ref(v___y_3094_);
if (lean_obj_tag(v___x_3099_) == 0)
{
lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3107_; 
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3107_ == 0)
{
lean_object* v_unused_3108_; 
v_unused_3108_ = lean_ctor_get(v___x_3099_, 0);
lean_dec(v_unused_3108_);
v___x_3101_ = v___x_3099_;
v_isShared_3102_ = v_isSharedCheck_3107_;
goto v_resetjp_3100_;
}
else
{
lean_dec(v___x_3099_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3107_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3103_; lean_object* v___x_3105_; 
v___x_3103_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_3103_, 0, v___y_3095_);
if (v_isShared_3102_ == 0)
{
lean_ctor_set(v___x_3101_, 0, v___x_3103_);
v___x_3105_ = v___x_3101_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v___x_3103_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
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
case 1:
{
lean_object* v___x_3117_; size_t v_sz_3118_; size_t v___x_3119_; lean_object* v___x_3120_; 
v___x_3117_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___closed__0));
v_sz_3118_ = lean_array_size(v___y_3094_);
v___x_3119_ = ((size_t)0ULL);
v___x_3120_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(v___y_3094_, v_sz_3118_, v___x_3119_, v___x_3117_);
lean_dec_ref(v___y_3094_);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3132_; 
v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3123_ = v___x_3120_;
v_isShared_3124_ = v_isSharedCheck_3132_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3120_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3132_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v_fst_3125_; lean_object* v_snd_3126_; lean_object* v___x_3127_; uint8_t v___x_3128_; lean_object* v___x_3130_; 
v_fst_3125_ = lean_ctor_get(v_a_3121_, 0);
lean_inc(v_fst_3125_);
v_snd_3126_ = lean_ctor_get(v_a_3121_, 1);
lean_inc(v_snd_3126_);
lean_dec(v_a_3121_);
v___x_3127_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_3127_, 0, v_fst_3125_);
v___x_3128_ = lean_unbox(v_snd_3126_);
lean_dec(v_snd_3126_);
lean_ctor_set_uint8(v___x_3127_, sizeof(void*)*1, v___x_3128_);
if (v_isShared_3124_ == 0)
{
lean_ctor_set(v___x_3123_, 0, v___x_3127_);
v___x_3130_ = v___x_3123_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3127_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
else
{
lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3140_; 
v_a_3133_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3135_ = v___x_3120_;
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v___x_3120_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3138_; 
if (v_isShared_3136_ == 0)
{
v___x_3138_ = v___x_3135_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_a_3133_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
}
default: 
{
lean_object* v_codeQualityEntries_3141_; size_t v_sz_3142_; size_t v___x_3143_; lean_object* v___x_3144_; 
v_codeQualityEntries_3141_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality___closed__0));
v_sz_3142_ = lean_array_size(v___y_3094_);
v___x_3143_ = ((size_t)0ULL);
v___x_3144_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(v___y_3094_, v_sz_3142_, v___x_3143_, v_codeQualityEntries_3141_);
lean_dec_ref(v___y_3094_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3153_; 
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3147_ = v___x_3144_;
v_isShared_3148_ = v_isSharedCheck_3153_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v___x_3144_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3153_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3149_; lean_object* v___x_3151_; 
v___x_3149_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3149_, 0, v_a_3145_);
if (v_isShared_3148_ == 0)
{
lean_ctor_set(v___x_3147_, 0, v___x_3149_);
v___x_3151_ = v___x_3147_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v___x_3149_);
v___x_3151_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
return v___x_3151_;
}
}
}
else
{
lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3161_; 
v_a_3154_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3156_ = v___x_3144_;
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_dec(v___x_3144_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3159_; 
if (v_isShared_3157_ == 0)
{
v___x_3159_ = v___x_3156_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3154_);
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
}
}
v___jp_3162_:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; uint8_t v___x_3166_; 
v___x_3164_ = lean_array_get_size(v___y_3163_);
v___x_3165_ = lean_unsigned_to_nat(0u);
v___x_3166_ = lean_nat_dec_eq(v___x_3164_, v___x_3165_);
if (v___x_3166_ == 0)
{
uint8_t v___x_3167_; 
v___x_3167_ = 1;
v___y_3094_ = v___y_3163_;
v___y_3095_ = v___x_3167_;
goto v___jp_3093_;
}
else
{
uint8_t v___x_3168_; 
v___x_3168_ = 0;
v___y_3094_ = v___y_3163_;
v___y_3095_ = v___x_3168_;
goto v___jp_3093_;
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_3086_ = stack[0].m_obj;
lean_object* v_linterOpts_3087_ = stack[1].m_obj;
lean_object* v_env_3088_ = stack[2].m_obj;
lean_object* v_mod_3089_ = stack[3].m_obj;
lean_object* v_res_3174_;
v_res_3174_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(v_args_3086_, v_linterOpts_3087_, v_env_3088_, v_mod_3089_);
stack->m_obj
 = v_res_3174_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___boxed(lean_object* v_args_3175_, lean_object* v_linterOpts_3176_, lean_object* v_env_3177_, lean_object* v_mod_3178_, lean_object* v_a_3179_){
_start:
{
lean_object* v_res_3180_; 
v_res_3180_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(v_args_3175_, v_linterOpts_3176_, v_env_3177_, v_mod_3178_);
lean_dec(v_mod_3178_);
lean_dec_ref(v_env_3177_);
lean_dec_ref(v_linterOpts_3176_);
lean_dec_ref(v_args_3175_);
return v_res_3180_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0(lean_object* v_00_u03b4_3181_, lean_object* v_t_3182_, lean_object* v_k_3183_, lean_object* v_fallback_3184_){
_start:
{
lean_object* v___x_3185_; 
v___x_3185_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(v_t_3182_, v_k_3183_, v_fallback_3184_);
return v___x_3185_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___boxed(lean_object* v_00_u03b4_3186_, lean_object* v_t_3187_, lean_object* v_k_3188_, lean_object* v_fallback_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0(v_00_u03b4_3186_, v_t_3187_, v_k_3188_, v_fallback_3189_);
lean_dec(v_fallback_3189_);
lean_dec(v_k_3188_);
lean_dec(v_t_3187_);
return v_res_3190_;
}
}
lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(uint8_t v___y_3191_, lean_object* v_____r_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_){
_start:
{
lean_object* v___x_3196_; lean_object* v___x_3197_; 
v___x_3196_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_3196_, 0, v___y_3191_);
v___x_3197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3196_);
return v___x_3197_;
}
}
LEAN_EXPORT void l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___y_3191_ = stack[0].m_num;
lean_object* v_____r_3192_ = stack[1].m_obj;
lean_object* v___y_3193_ = stack[2].m_obj;
lean_object* v___y_3194_ = stack[3].m_obj;
lean_object* v_res_3198_;
v_res_3198_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_3191_, v_____r_3192_, v___y_3193_, v___y_3194_);
stack->m_obj
 = v_res_3198_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0___boxed(lean_object* v___y_3199_, lean_object* v_____r_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_){
_start:
{
uint8_t v___y_16494__boxed_3204_; lean_object* v_res_3205_; 
v___y_16494__boxed_3204_ = lean_unbox(v___y_3199_);
v_res_3205_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_16494__boxed_3204_, v_____r_3200_, v___y_3201_, v___y_3202_);
lean_dec(v___y_3202_);
lean_dec_ref(v___y_3201_);
return v_res_3205_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0(void){
_start:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3206_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15);
v___x_3207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3206_);
return v___x_3207_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1(void){
_start:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
v___x_3208_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_3209_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0);
v___x_3210_ = lean_unsigned_to_nat(0u);
v___x_3211_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3210_);
lean_ctor_set(v___x_3211_, 1, v___x_3210_);
lean_ctor_set(v___x_3211_, 2, v___x_3210_);
lean_ctor_set(v___x_3211_, 3, v___x_3210_);
lean_ctor_set(v___x_3211_, 4, v___x_3209_);
lean_ctor_set(v___x_3211_, 5, v___x_3209_);
lean_ctor_set(v___x_3211_, 6, v___x_3209_);
lean_ctor_set(v___x_3211_, 7, v___x_3209_);
lean_ctor_set(v___x_3211_, 8, v___x_3209_);
lean_ctor_set(v___x_3211_, 9, v___x_3209_);
lean_ctor_set(v___x_3211_, 10, v___x_3209_);
lean_ctor_set(v___x_3211_, 11, v___x_3208_);
return v___x_3211_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2(void){
_start:
{
lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3212_ = lean_unsigned_to_nat(32u);
v___x_3213_ = lean_mk_empty_array_with_capacity(v___x_3212_);
v___x_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3213_);
return v___x_3214_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3(void){
_start:
{
size_t v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3215_ = ((size_t)5ULL);
v___x_3216_ = lean_unsigned_to_nat(0u);
v___x_3217_ = lean_unsigned_to_nat(32u);
v___x_3218_ = lean_mk_empty_array_with_capacity(v___x_3217_);
v___x_3219_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2);
v___x_3220_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3220_, 0, v___x_3219_);
lean_ctor_set(v___x_3220_, 1, v___x_3218_);
lean_ctor_set(v___x_3220_, 2, v___x_3216_);
lean_ctor_set(v___x_3220_, 3, v___x_3216_);
lean_ctor_set_usize(v___x_3220_, 4, v___x_3215_);
return v___x_3220_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4(void){
_start:
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3221_ = lean_box(1);
v___x_3222_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3);
v___x_3223_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0);
v___x_3224_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3223_);
lean_ctor_set(v___x_3224_, 1, v___x_3222_);
lean_ctor_set(v___x_3224_, 2, v___x_3221_);
return v___x_3224_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(lean_object* v_msgData_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_){
_start:
{
lean_object* v___x_3229_; lean_object* v_toCold_3230_; lean_object* v_env_3231_; lean_object* v_options_3232_; uint8_t v___x_3233_; lean_object* v_env_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3229_ = lean_st_ref_get(v___y_3227_);
v_toCold_3230_ = lean_ctor_get(v___y_3226_, 0);
v_env_3231_ = lean_ctor_get(v___x_3229_, 0);
lean_inc_ref(v_env_3231_);
lean_dec(v___x_3229_);
v_options_3232_ = lean_ctor_get(v_toCold_3230_, 2);
v___x_3233_ = 0;
v_env_3234_ = l_Lean_Environment_setRecordingDeps(v_env_3231_, v___x_3233_);
v___x_3235_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1);
v___x_3236_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4);
lean_inc_ref(v_options_3232_);
v___x_3237_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3237_, 0, v_env_3234_);
lean_ctor_set(v___x_3237_, 1, v___x_3235_);
lean_ctor_set(v___x_3237_, 2, v___x_3236_);
lean_ctor_set(v___x_3237_, 3, v_options_3232_);
v___x_3238_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3237_);
lean_ctor_set(v___x_3238_, 1, v_msgData_3225_);
v___x_3239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3238_);
return v___x_3239_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_3225_ = stack[0].m_obj;
lean_object* v___y_3226_ = stack[1].m_obj;
lean_object* v___y_3227_ = stack[2].m_obj;
lean_object* v_res_3240_;
v_res_3240_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(v_msgData_3225_, v___y_3226_, v___y_3227_);
stack->m_obj
 = v_res_3240_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___boxed(lean_object* v_msgData_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_){
_start:
{
lean_object* v_res_3245_; 
v_res_3245_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(v_msgData_3241_, v___y_3242_, v___y_3243_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
return v_res_3245_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(lean_object* v_msg_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
lean_object* v_ref_3250_; lean_object* v___x_3251_; lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3260_; 
v_ref_3250_ = lean_ctor_get(v___y_3247_, 2);
v___x_3251_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(v_msg_3246_, v___y_3247_, v___y_3248_);
v_a_3252_ = lean_ctor_get(v___x_3251_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3251_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3254_ = v___x_3251_;
v_isShared_3255_ = v_isSharedCheck_3260_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___x_3251_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3260_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3256_; lean_object* v___x_3258_; 
lean_inc(v_ref_3250_);
v___x_3256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3256_, 0, v_ref_3250_);
lean_ctor_set(v___x_3256_, 1, v_a_3252_);
if (v_isShared_3255_ == 0)
{
lean_ctor_set_tag(v___x_3254_, 1);
lean_ctor_set(v___x_3254_, 0, v___x_3256_);
v___x_3258_ = v___x_3254_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v___x_3256_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3246_ = stack[0].m_obj;
lean_object* v___y_3247_ = stack[1].m_obj;
lean_object* v___y_3248_ = stack[2].m_obj;
lean_object* v_res_3261_;
v_res_3261_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_3246_, v___y_3247_, v___y_3248_);
stack->m_obj
 = v_res_3261_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg___boxed(lean_object* v_msg_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_){
_start:
{
lean_object* v_res_3266_; 
v_res_3266_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_3262_, v___y_3263_, v___y_3264_);
lean_dec(v___y_3264_);
lean_dec_ref(v___y_3263_);
return v_res_3266_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(lean_object* v_ref_3267_, lean_object* v_msg_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_){
_start:
{
lean_object* v_toCold_3272_; lean_object* v_currRecDepth_3273_; lean_object* v_ref_3274_; uint16_t v_optionFlags_3275_; uint8_t v_suppressElabErrors_3276_; uint8_t v_isRecordingDeps_3277_; lean_object* v_ref_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; 
v_toCold_3272_ = lean_ctor_get(v___y_3269_, 0);
v_currRecDepth_3273_ = lean_ctor_get(v___y_3269_, 1);
v_ref_3274_ = lean_ctor_get(v___y_3269_, 2);
v_optionFlags_3275_ = lean_ctor_get_uint16(v___y_3269_, sizeof(void*)*3);
v_suppressElabErrors_3276_ = lean_ctor_get_uint8(v___y_3269_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3277_ = lean_ctor_get_uint8(v___y_3269_, sizeof(void*)*3 + 3);
v_ref_3278_ = l_Lean_replaceRef(v_ref_3267_, v_ref_3274_);
lean_inc(v_currRecDepth_3273_);
lean_inc_ref(v_toCold_3272_);
v___x_3279_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3279_, 0, v_toCold_3272_);
lean_ctor_set(v___x_3279_, 1, v_currRecDepth_3273_);
lean_ctor_set(v___x_3279_, 2, v_ref_3278_);
lean_ctor_set_uint16(v___x_3279_, sizeof(void*)*3, v_optionFlags_3275_);
lean_ctor_set_uint8(v___x_3279_, sizeof(void*)*3 + 2, v_suppressElabErrors_3276_);
lean_ctor_set_uint8(v___x_3279_, sizeof(void*)*3 + 3, v_isRecordingDeps_3277_);
v___x_3280_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_3268_, v___x_3279_, v___y_3270_);
lean_dec_ref_known(v___x_3279_, 3);
return v___x_3280_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3267_ = stack[0].m_obj;
lean_object* v_msg_3268_ = stack[1].m_obj;
lean_object* v___y_3269_ = stack[2].m_obj;
lean_object* v___y_3270_ = stack[3].m_obj;
lean_object* v_res_3281_;
v_res_3281_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_3267_, v_msg_3268_, v___y_3269_, v___y_3270_);
stack->m_obj
 = v_res_3281_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg___boxed(lean_object* v_ref_3282_, lean_object* v_msg_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
lean_object* v_res_3287_; 
v_res_3287_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_3282_, v_msg_3283_, v___y_3284_, v___y_3285_);
lean_dec(v___y_3285_);
lean_dec_ref(v___y_3284_);
lean_dec(v_ref_3282_);
return v_res_3287_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3289_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__0));
v___x_3290_ = l_Lean_stringToMessageData(v___x_3289_);
return v___x_3290_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3292_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__2));
v___x_3293_ = l_Lean_stringToMessageData(v___x_3292_);
return v___x_3293_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5(void){
_start:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3295_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__4));
v___x_3296_ = l_Lean_stringToMessageData(v___x_3295_);
return v___x_3296_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7(void){
_start:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3298_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__6));
v___x_3299_ = l_Lean_stringToMessageData(v___x_3298_);
return v___x_3299_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9(void){
_start:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3301_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__8));
v___x_3302_ = l_Lean_stringToMessageData(v___x_3301_);
return v___x_3302_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11(void){
_start:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3304_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__10));
v___x_3305_ = l_Lean_stringToMessageData(v___x_3304_);
return v___x_3305_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13(void){
_start:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3307_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__12));
v___x_3308_ = l_Lean_stringToMessageData(v___x_3307_);
return v___x_3308_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__15(void){
_start:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3310_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__14));
v___x_3311_ = l_Lean_stringToMessageData(v___x_3310_);
return v___x_3311_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__17(void){
_start:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___x_3313_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__16));
v___x_3314_ = l_Lean_stringToMessageData(v___x_3313_);
return v___x_3314_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__19(void){
_start:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3316_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__18));
v___x_3317_ = l_Lean_stringToMessageData(v___x_3316_);
return v___x_3317_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__21(void){
_start:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3319_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__20));
v___x_3320_ = l_Lean_stringToMessageData(v___x_3319_);
return v___x_3320_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(lean_object* v_msg_3321_, lean_object* v_declHint_3322_, lean_object* v___y_3323_){
_start:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v_env_3327_; uint8_t v___x_3328_; 
v___x_3325_ = lean_box(0);
v___x_3326_ = lean_st_ref_get(v___y_3323_);
v_env_3327_ = lean_ctor_get(v___x_3326_, 0);
lean_inc_ref(v_env_3327_);
lean_dec(v___x_3326_);
v___x_3328_ = l_Lean_Name_isAnonymous(v_declHint_3322_);
if (v___x_3328_ == 0)
{
uint8_t v_isExporting_3329_; 
v_isExporting_3329_ = lean_ctor_get_uint8(v_env_3327_, sizeof(void*)*13);
if (v_isExporting_3329_ == 0)
{
lean_object* v___x_3330_; 
lean_dec_ref(v_env_3327_);
lean_dec(v_declHint_3322_);
v___x_3330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3330_, 0, v_msg_3321_);
return v___x_3330_;
}
else
{
lean_object* v___x_3331_; uint8_t v___x_3332_; 
lean_inc_ref(v_env_3327_);
v___x_3331_ = l_Lean_Environment_setExporting(v_env_3327_, v___x_3328_);
lean_inc(v_declHint_3322_);
lean_inc_ref(v___x_3331_);
v___x_3332_ = l_Lean_Environment_contains(v___x_3331_, v_declHint_3322_, v_isExporting_3329_);
if (v___x_3332_ == 0)
{
lean_object* v___x_3333_; 
lean_dec_ref(v___x_3331_);
lean_dec_ref(v_env_3327_);
lean_dec(v_declHint_3322_);
v___x_3333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3333_, 0, v_msg_3321_);
return v___x_3333_;
}
else
{
lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v_c_3339_; lean_object* v___x_3340_; 
v___x_3334_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1);
v___x_3335_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4);
v___x_3336_ = l_Lean_Options_empty;
v___x_3337_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3331_);
lean_ctor_set(v___x_3337_, 1, v___x_3334_);
lean_ctor_set(v___x_3337_, 2, v___x_3335_);
lean_ctor_set(v___x_3337_, 3, v___x_3336_);
lean_inc(v_declHint_3322_);
v___x_3338_ = l_Lean_MessageData_ofConstName(v_declHint_3322_, v___x_3328_);
v_c_3339_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3339_, 0, v___x_3337_);
lean_ctor_set(v_c_3339_, 1, v___x_3338_);
v___x_3340_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3327_, v_declHint_3322_);
if (lean_obj_tag(v___x_3340_) == 0)
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
lean_dec_ref(v_env_3327_);
lean_dec(v_declHint_3322_);
v___x_3341_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1);
v___x_3342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3341_);
lean_ctor_set(v___x_3342_, 1, v_c_3339_);
v___x_3343_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3);
v___x_3344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3342_);
lean_ctor_set(v___x_3344_, 1, v___x_3343_);
v___x_3345_ = l_Lean_MessageData_note(v___x_3344_);
v___x_3346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3346_, 0, v_msg_3321_);
lean_ctor_set(v___x_3346_, 1, v___x_3345_);
v___x_3347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3346_);
return v___x_3347_;
}
else
{
lean_object* v_val_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3404_; 
v_val_3348_ = lean_ctor_get(v___x_3340_, 0);
v_isSharedCheck_3404_ = !lean_is_exclusive(v___x_3340_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3350_ = v___x_3340_;
v_isShared_3351_ = v_isSharedCheck_3404_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_val_3348_);
lean_dec(v___x_3340_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3404_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3352_; lean_object* v_modules_3353_; lean_object* v_moduleNames_3354_; lean_object* v_mod_3355_; uint8_t v___y_3357_; uint8_t v___x_3387_; 
v___x_3352_ = l_Lean_Environment_header(v_env_3327_);
lean_dec_ref(v_env_3327_);
v_modules_3353_ = lean_ctor_get(v___x_3352_, 3);
lean_inc_ref(v_modules_3353_);
v_moduleNames_3354_ = lean_ctor_get(v___x_3352_, 4);
lean_inc_ref(v_moduleNames_3354_);
lean_dec_ref(v___x_3352_);
v_mod_3355_ = lean_array_get(v___x_3325_, v_moduleNames_3354_, v_val_3348_);
lean_dec_ref(v_moduleNames_3354_);
v___x_3387_ = l_Lean_isPrivateName(v_declHint_3322_);
lean_dec(v_declHint_3322_);
if (v___x_3387_ == 0)
{
lean_object* v___x_3388_; uint8_t v___x_3389_; 
v___x_3388_ = lean_array_get_size(v_modules_3353_);
v___x_3389_ = lean_nat_dec_lt(v_val_3348_, v___x_3388_);
if (v___x_3389_ == 0)
{
lean_dec_ref(v_modules_3353_);
lean_dec(v_val_3348_);
v___y_3357_ = v___x_3387_;
goto v___jp_3356_;
}
else
{
lean_object* v___x_3390_; lean_object* v_toImport_3391_; uint8_t v_isExported_3392_; 
v___x_3390_ = lean_array_fget(v_modules_3353_, v_val_3348_);
lean_dec(v_val_3348_);
lean_dec_ref(v_modules_3353_);
v_toImport_3391_ = lean_ctor_get(v___x_3390_, 0);
lean_inc_ref(v_toImport_3391_);
lean_dec(v___x_3390_);
v_isExported_3392_ = lean_ctor_get_uint8(v_toImport_3391_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_3391_);
v___y_3357_ = v_isExported_3392_;
goto v___jp_3356_;
}
}
else
{
lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
lean_dec_ref(v_modules_3353_);
lean_del_object(v___x_3350_);
lean_dec(v_val_3348_);
v___x_3393_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1);
v___x_3394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3393_);
lean_ctor_set(v___x_3394_, 1, v_c_3339_);
v___x_3395_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__19);
v___x_3396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3394_);
lean_ctor_set(v___x_3396_, 1, v___x_3395_);
v___x_3397_ = l_Lean_MessageData_ofName(v_mod_3355_);
v___x_3398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3396_);
lean_ctor_set(v___x_3398_, 1, v___x_3397_);
v___x_3399_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__21);
v___x_3400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3400_, 0, v___x_3398_);
lean_ctor_set(v___x_3400_, 1, v___x_3399_);
v___x_3401_ = l_Lean_MessageData_note(v___x_3400_);
v___x_3402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3402_, 0, v_msg_3321_);
lean_ctor_set(v___x_3402_, 1, v___x_3401_);
v___x_3403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3402_);
return v___x_3403_;
}
v___jp_3356_:
{
if (v___y_3357_ == 0)
{
lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3369_; 
v___x_3358_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5);
v___x_3359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3358_);
lean_ctor_set(v___x_3359_, 1, v_c_3339_);
v___x_3360_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7);
v___x_3361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3359_);
lean_ctor_set(v___x_3361_, 1, v___x_3360_);
v___x_3362_ = l_Lean_MessageData_ofName(v_mod_3355_);
v___x_3363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3363_, 0, v___x_3361_);
lean_ctor_set(v___x_3363_, 1, v___x_3362_);
v___x_3364_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9);
v___x_3365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3363_);
lean_ctor_set(v___x_3365_, 1, v___x_3364_);
v___x_3366_ = l_Lean_MessageData_note(v___x_3365_);
v___x_3367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3367_, 0, v_msg_3321_);
lean_ctor_set(v___x_3367_, 1, v___x_3366_);
if (v_isShared_3351_ == 0)
{
lean_ctor_set_tag(v___x_3350_, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3367_);
v___x_3369_ = v___x_3350_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v___x_3367_);
v___x_3369_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
return v___x_3369_;
}
}
else
{
lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3385_; 
v___x_3371_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11);
v___x_3372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3371_);
lean_ctor_set(v___x_3372_, 1, v_c_3339_);
v___x_3373_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13);
v___x_3374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3372_);
lean_ctor_set(v___x_3374_, 1, v___x_3373_);
v___x_3375_ = l_Lean_MessageData_ofName(v_mod_3355_);
lean_inc_ref(v___x_3375_);
v___x_3376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3374_);
lean_ctor_set(v___x_3376_, 1, v___x_3375_);
v___x_3377_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__15);
v___x_3378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3376_);
lean_ctor_set(v___x_3378_, 1, v___x_3377_);
v___x_3379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3379_, 0, v___x_3378_);
lean_ctor_set(v___x_3379_, 1, v___x_3375_);
v___x_3380_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__17);
v___x_3381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3379_);
lean_ctor_set(v___x_3381_, 1, v___x_3380_);
v___x_3382_ = l_Lean_MessageData_note(v___x_3381_);
v___x_3383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3383_, 0, v_msg_3321_);
lean_ctor_set(v___x_3383_, 1, v___x_3382_);
if (v_isShared_3351_ == 0)
{
lean_ctor_set_tag(v___x_3350_, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3383_);
v___x_3385_ = v___x_3350_;
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
}
}
}
}
}
}
else
{
lean_object* v___x_3405_; 
lean_dec_ref(v_env_3327_);
lean_dec(v_declHint_3322_);
v___x_3405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3405_, 0, v_msg_3321_);
return v___x_3405_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3321_ = stack[0].m_obj;
lean_object* v_declHint_3322_ = stack[1].m_obj;
lean_object* v___y_3323_ = stack[2].m_obj;
lean_object* v_res_3406_;
v_res_3406_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_3321_, v_declHint_3322_, v___y_3323_);
stack->m_obj
 = v_res_3406_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___boxed(lean_object* v_msg_3407_, lean_object* v_declHint_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_){
_start:
{
lean_object* v_res_3411_; 
v_res_3411_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_3407_, v_declHint_3408_, v___y_3409_);
lean_dec(v___y_3409_);
return v_res_3411_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(lean_object* v_msg_3412_, lean_object* v_declHint_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_){
_start:
{
lean_object* v___x_3417_; lean_object* v_a_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3427_; 
v___x_3417_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_3412_, v_declHint_3413_, v___y_3415_);
v_a_3418_ = lean_ctor_get(v___x_3417_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3420_ = v___x_3417_;
v_isShared_3421_ = v_isSharedCheck_3427_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_a_3418_);
lean_dec(v___x_3417_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3427_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3425_; 
v___x_3422_ = l_Lean_unknownIdentifierMessageTag;
v___x_3423_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3422_);
lean_ctor_set(v___x_3423_, 1, v_a_3418_);
if (v_isShared_3421_ == 0)
{
lean_ctor_set(v___x_3420_, 0, v___x_3423_);
v___x_3425_ = v___x_3420_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v___x_3423_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
return v___x_3425_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3412_ = stack[0].m_obj;
lean_object* v_declHint_3413_ = stack[1].m_obj;
lean_object* v___y_3414_ = stack[2].m_obj;
lean_object* v___y_3415_ = stack[3].m_obj;
lean_object* v_res_3428_;
v_res_3428_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(v_msg_3412_, v_declHint_3413_, v___y_3414_, v___y_3415_);
stack->m_obj
 = v_res_3428_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14___boxed(lean_object* v_msg_3429_, lean_object* v_declHint_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_){
_start:
{
lean_object* v_res_3434_; 
v_res_3434_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(v_msg_3429_, v_declHint_3430_, v___y_3431_, v___y_3432_);
lean_dec(v___y_3432_);
lean_dec_ref(v___y_3431_);
return v_res_3434_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(lean_object* v_ref_3435_, lean_object* v_msg_3436_, lean_object* v_declHint_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_){
_start:
{
lean_object* v___x_3441_; lean_object* v_a_3442_; lean_object* v___x_3443_; 
v___x_3441_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(v_msg_3436_, v_declHint_3437_, v___y_3438_, v___y_3439_);
v_a_3442_ = lean_ctor_get(v___x_3441_, 0);
lean_inc(v_a_3442_);
lean_dec_ref(v___x_3441_);
v___x_3443_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_3435_, v_a_3442_, v___y_3438_, v___y_3439_);
return v___x_3443_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3435_ = stack[0].m_obj;
lean_object* v_msg_3436_ = stack[1].m_obj;
lean_object* v_declHint_3437_ = stack[2].m_obj;
lean_object* v___y_3438_ = stack[3].m_obj;
lean_object* v___y_3439_ = stack[4].m_obj;
lean_object* v_res_3444_;
v_res_3444_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_3435_, v_msg_3436_, v_declHint_3437_, v___y_3438_, v___y_3439_);
stack->m_obj
 = v_res_3444_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg___boxed(lean_object* v_ref_3445_, lean_object* v_msg_3446_, lean_object* v_declHint_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_){
_start:
{
lean_object* v_res_3451_; 
v_res_3451_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_3445_, v_msg_3446_, v_declHint_3447_, v___y_3448_, v___y_3449_);
lean_dec(v___y_3449_);
lean_dec_ref(v___y_3448_);
lean_dec(v_ref_3445_);
return v_res_3451_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_3453_; lean_object* v___x_3454_; 
v___x_3453_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__0));
v___x_3454_ = l_Lean_stringToMessageData(v___x_3453_);
return v___x_3454_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3455_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__1));
v___x_3456_ = l_Lean_stringToMessageData(v___x_3455_);
return v___x_3456_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(lean_object* v_ref_3457_, lean_object* v_constName_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
lean_object* v___x_3462_; uint8_t v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; 
v___x_3462_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1);
v___x_3463_ = 0;
lean_inc(v_constName_3458_);
v___x_3464_ = l_Lean_MessageData_ofConstName(v_constName_3458_, v___x_3463_);
v___x_3465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3462_);
lean_ctor_set(v___x_3465_, 1, v___x_3464_);
v___x_3466_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2);
v___x_3467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3465_);
lean_ctor_set(v___x_3467_, 1, v___x_3466_);
v___x_3468_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_3457_, v___x_3467_, v_constName_3458_, v___y_3459_, v___y_3460_);
return v___x_3468_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3457_ = stack[0].m_obj;
lean_object* v_constName_3458_ = stack[1].m_obj;
lean_object* v___y_3459_ = stack[2].m_obj;
lean_object* v___y_3460_ = stack[3].m_obj;
lean_object* v_res_3469_;
v_res_3469_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_3457_, v_constName_3458_, v___y_3459_, v___y_3460_);
stack->m_obj
 = v_res_3469_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___boxed(lean_object* v_ref_3470_, lean_object* v_constName_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_){
_start:
{
lean_object* v_res_3475_; 
v_res_3475_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_3470_, v_constName_3471_, v___y_3472_, v___y_3473_);
lean_dec(v___y_3473_);
lean_dec_ref(v___y_3472_);
lean_dec(v_ref_3470_);
return v_res_3475_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_){
_start:
{
lean_object* v_ref_3480_; lean_object* v___x_3481_; 
v_ref_3480_ = lean_ctor_get(v___y_3477_, 2);
v___x_3481_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_3480_, v_constName_3476_, v___y_3477_, v___y_3478_);
return v___x_3481_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_3476_ = stack[0].m_obj;
lean_object* v___y_3477_ = stack[1].m_obj;
lean_object* v___y_3478_ = stack[2].m_obj;
lean_object* v_res_3482_;
v_res_3482_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_3476_, v___y_3477_, v___y_3478_);
stack->m_obj
 = v_res_3482_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_){
_start:
{
lean_object* v_res_3487_; 
v_res_3487_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_3483_, v___y_3484_, v___y_3485_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
return v_res_3487_;
}
}
lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(lean_object* v_constName_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_){
_start:
{
lean_object* v___x_3492_; lean_object* v_env_3493_; uint8_t v___x_3494_; lean_object* v___x_3495_; 
v___x_3492_ = lean_st_ref_get(v___y_3490_);
v_env_3493_ = lean_ctor_get(v___x_3492_, 0);
lean_inc_ref(v_env_3493_);
lean_dec(v___x_3492_);
v___x_3494_ = 0;
lean_inc(v_constName_3488_);
v___x_3495_ = l_Lean_Environment_find_x3f(v_env_3493_, v_constName_3488_, v___x_3494_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v___x_3496_; 
v___x_3496_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_3488_, v___y_3489_, v___y_3490_);
return v___x_3496_;
}
else
{
lean_object* v_val_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3504_; 
lean_dec(v_constName_3488_);
v_val_3497_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3499_ = v___x_3495_;
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_val_3497_);
lean_dec(v___x_3495_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3502_; 
if (v_isShared_3500_ == 0)
{
lean_ctor_set_tag(v___x_3499_, 0);
v___x_3502_ = v___x_3499_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_val_3497_);
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
LEAN_EXPORT void l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_3488_ = stack[0].m_obj;
lean_object* v___y_3489_ = stack[1].m_obj;
lean_object* v___y_3490_ = stack[2].m_obj;
lean_object* v_res_3505_;
v_res_3505_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(v_constName_3488_, v___y_3489_, v___y_3490_);
stack->m_obj
 = v_res_3505_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0___boxed(lean_object* v_constName_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
lean_object* v_res_3510_; 
v_res_3510_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(v_constName_3506_, v___y_3507_, v___y_3508_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
return v_res_3510_;
}
}
lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(lean_object* v_declName_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_){
_start:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; 
v___x_3515_ = lean_box(0);
lean_inc(v_declName_3511_);
v___x_3516_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(v_declName_3511_, v___y_3512_, v___y_3513_);
if (lean_obj_tag(v___x_3516_) == 0)
{
lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3542_; 
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3542_ == 0)
{
lean_object* v_unused_3543_; 
v_unused_3543_ = lean_ctor_get(v___x_3516_, 0);
lean_dec(v_unused_3543_);
v___x_3518_ = v___x_3516_;
v_isShared_3519_ = v_isSharedCheck_3542_;
goto v_resetjp_3517_;
}
else
{
lean_dec(v___x_3516_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3542_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3520_; lean_object* v_env_3521_; lean_object* v___x_3522_; 
v___x_3520_ = lean_st_ref_get(v___y_3513_);
v_env_3521_ = lean_ctor_get(v___x_3520_, 0);
lean_inc_ref(v_env_3521_);
lean_dec(v___x_3520_);
v___x_3522_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3521_, v_declName_3511_);
lean_dec(v_declName_3511_);
lean_dec_ref(v_env_3521_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_object* v___x_3523_; lean_object* v___x_3525_; 
v___x_3523_ = lean_box(0);
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 0, v___x_3523_);
v___x_3525_ = v___x_3518_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v___x_3523_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
else
{
lean_object* v_val_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3541_; 
v_val_3527_ = lean_ctor_get(v___x_3522_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3529_ = v___x_3522_;
v_isShared_3530_ = v_isSharedCheck_3541_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_val_3527_);
lean_dec(v___x_3522_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3541_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v___x_3531_; lean_object* v_env_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3536_; 
v___x_3531_ = lean_st_ref_get(v___y_3513_);
v_env_3532_ = lean_ctor_get(v___x_3531_, 0);
lean_inc_ref(v_env_3532_);
lean_dec(v___x_3531_);
v___x_3533_ = l_Lean_Environment_allImportedModuleNames(v_env_3532_);
lean_dec_ref(v_env_3532_);
v___x_3534_ = lean_array_get(v___x_3515_, v___x_3533_, v_val_3527_);
lean_dec(v_val_3527_);
lean_dec_ref(v___x_3533_);
if (v_isShared_3530_ == 0)
{
lean_ctor_set(v___x_3529_, 0, v___x_3534_);
v___x_3536_ = v___x_3529_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v___x_3534_);
v___x_3536_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
lean_object* v___x_3538_; 
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 0, v___x_3536_);
v___x_3538_ = v___x_3518_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v___x_3536_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
}
}
}
else
{
lean_object* v_a_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3551_; 
lean_dec(v_declName_3511_);
v_a_3544_ = lean_ctor_get(v___x_3516_, 0);
v_isSharedCheck_3551_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3551_ == 0)
{
v___x_3546_ = v___x_3516_;
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_a_3544_);
lean_dec(v___x_3516_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v___x_3549_; 
if (v_isShared_3547_ == 0)
{
v___x_3549_ = v___x_3546_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v_a_3544_);
v___x_3549_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
return v___x_3549_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_3511_ = stack[0].m_obj;
lean_object* v___y_3512_ = stack[1].m_obj;
lean_object* v___y_3513_ = stack[2].m_obj;
lean_object* v_res_3552_;
v_res_3552_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_declName_3511_, v___y_3512_, v___y_3513_);
stack->m_obj
 = v_res_3552_;
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0___boxed(lean_object* v_declName_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_){
_start:
{
lean_object* v_res_3557_; 
v_res_3557_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_declName_3553_, v___y_3554_, v___y_3555_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
return v_res_3557_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(lean_object* v_fst_3559_, lean_object* v_sp_3560_, lean_object* v___x_3561_, lean_object* v_as_3562_, size_t v_sz_3563_, size_t v_i_3564_, lean_object* v_b_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_){
_start:
{
lean_object* v_a_3570_; uint8_t v___x_3574_; 
v___x_3574_ = lean_usize_dec_lt(v_i_3564_, v_sz_3563_);
if (v___x_3574_ == 0)
{
lean_object* v___x_3575_; 
lean_dec(v___x_3561_);
lean_dec(v_sp_3560_);
lean_dec_ref(v_fst_3559_);
v___x_3575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3575_, 0, v_b_3565_);
return v___x_3575_;
}
else
{
lean_object* v_a_3576_; lean_object* v_fst_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3705_; 
v_a_3576_ = lean_array_uget(v_as_3562_, v_i_3564_);
v_fst_3577_ = lean_ctor_get(v_a_3576_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v_a_3576_);
if (v_isSharedCheck_3705_ == 0)
{
lean_object* v_unused_3706_; 
v_unused_3706_ = lean_ctor_get(v_a_3576_, 1);
lean_dec(v_unused_3706_);
v___x_3579_ = v_a_3576_;
v_isShared_3580_ = v_isSharedCheck_3705_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_fst_3577_);
lean_dec(v_a_3576_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3705_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v_fst_3581_; lean_object* v_snd_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3704_; 
v_fst_3581_ = lean_ctor_get(v_b_3565_, 0);
v_snd_3582_ = lean_ctor_get(v_b_3565_, 1);
v_isSharedCheck_3704_ = !lean_is_exclusive(v_b_3565_);
if (v_isSharedCheck_3704_ == 0)
{
v___x_3584_ = v_b_3565_;
v_isShared_3585_ = v_isSharedCheck_3704_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_snd_3582_);
lean_inc(v_fst_3581_);
lean_dec(v_b_3565_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3704_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3586_; 
lean_inc(v_fst_3577_);
v___x_3586_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_fst_3577_, v___y_3566_, v___y_3567_);
if (lean_obj_tag(v___x_3586_) == 0)
{
lean_object* v_a_3587_; 
v_a_3587_ = lean_ctor_get(v___x_3586_, 0);
lean_inc(v_a_3587_);
lean_dec_ref_known(v___x_3586_, 1);
if (lean_obj_tag(v_a_3587_) == 0)
{
lean_object* v_optName_3588_; lean_object* v_ref_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
lean_dec(v_snd_3582_);
v_optName_3588_ = lean_ctor_get(v_fst_3559_, 1);
v_ref_3589_ = lean_ctor_get(v___y_3566_, 2);
v___x_3590_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_3577_, v___x_3574_);
v___x_3591_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1___closed__0));
v___x_3592_ = lean_string_append(v___x_3591_, v___x_3590_);
lean_dec_ref(v___x_3590_);
v___x_3593_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__2));
v___x_3594_ = lean_string_append(v___x_3592_, v___x_3593_);
lean_inc(v_optName_3588_);
v___x_3595_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_optName_3588_, v___x_3574_);
v___x_3596_ = lean_string_append(v___x_3594_, v___x_3595_);
lean_dec_ref(v___x_3595_);
v___x_3597_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__3));
v___x_3598_ = lean_string_append(v___x_3596_, v___x_3597_);
v___x_3599_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_3598_);
if (lean_obj_tag(v___x_3599_) == 0)
{
lean_object* v___x_3600_; lean_object* v___x_3602_; 
lean_dec_ref_known(v___x_3599_, 1);
lean_del_object(v___x_3579_);
v___x_3600_ = lean_box(v___x_3574_);
if (v_isShared_3585_ == 0)
{
lean_ctor_set(v___x_3584_, 1, v___x_3600_);
v___x_3602_ = v___x_3584_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v_fst_3581_);
lean_ctor_set(v_reuseFailAlloc_3603_, 1, v___x_3600_);
v___x_3602_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
v_a_3570_ = v___x_3602_;
goto v___jp_3569_;
}
}
else
{
lean_object* v_a_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3617_; 
lean_del_object(v___x_3584_);
lean_dec(v_fst_3581_);
lean_dec(v___x_3561_);
lean_dec(v_sp_3560_);
lean_dec_ref(v_fst_3559_);
v_a_3604_ = lean_ctor_get(v___x_3599_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3606_ = v___x_3599_;
v_isShared_3607_ = v_isSharedCheck_3617_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_a_3604_);
lean_dec(v___x_3599_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3617_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3612_; 
v___x_3608_ = lean_io_error_to_string(v_a_3604_);
v___x_3609_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3608_);
v___x_3610_ = l_Lean_MessageData_ofFormat(v___x_3609_);
lean_inc(v_ref_3589_);
if (v_isShared_3580_ == 0)
{
lean_ctor_set(v___x_3579_, 1, v___x_3610_);
lean_ctor_set(v___x_3579_, 0, v_ref_3589_);
v___x_3612_ = v___x_3579_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_ref_3589_);
lean_ctor_set(v_reuseFailAlloc_3616_, 1, v___x_3610_);
v___x_3612_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
lean_object* v___x_3614_; 
if (v_isShared_3607_ == 0)
{
lean_ctor_set(v___x_3606_, 0, v___x_3612_);
v___x_3614_ = v___x_3606_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v___x_3612_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
}
}
}
else
{
lean_object* v_val_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3695_; 
v_val_3618_ = lean_ctor_get(v_a_3587_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v_a_3587_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3620_ = v_a_3587_;
v_isShared_3621_ = v_isSharedCheck_3695_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_val_3618_);
lean_dec(v_a_3587_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3695_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3622_; 
v___x_3622_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_fst_3577_, v___y_3566_, v___y_3567_);
if (lean_obj_tag(v___x_3622_) == 0)
{
lean_object* v_a_3623_; lean_object* v___y_3625_; 
v_a_3623_ = lean_ctor_get(v___x_3622_, 0);
lean_inc(v_a_3623_);
lean_dec_ref_known(v___x_3622_, 1);
if (lean_obj_tag(v_a_3623_) == 0)
{
lean_inc(v___x_3561_);
v___y_3625_ = v___x_3561_;
goto v___jp_3624_;
}
else
{
lean_object* v_val_3686_; 
v_val_3686_ = lean_ctor_get(v_a_3623_, 0);
lean_inc(v_val_3686_);
lean_dec_ref_known(v_a_3623_, 1);
v___y_3625_ = v_val_3686_;
goto v___jp_3624_;
}
v___jp_3624_:
{
lean_object* v_ref_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; 
v_ref_3626_ = lean_ctor_get(v___y_3566_, 2);
v___x_3627_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__4));
lean_inc(v___y_3625_);
lean_inc(v_sp_3560_);
v___x_3628_ = l_Lean_SearchPath_findWithExt(v_sp_3560_, v___x_3627_, v___y_3625_);
if (lean_obj_tag(v___x_3628_) == 0)
{
lean_object* v_a_3629_; 
v_a_3629_ = lean_ctor_get(v___x_3628_, 0);
lean_inc(v_a_3629_);
lean_dec_ref_known(v___x_3628_, 1);
if (lean_obj_tag(v_a_3629_) == 0)
{
lean_object* v_optName_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; 
lean_dec(v_val_3618_);
lean_dec(v_snd_3582_);
v_optName_3630_ = lean_ctor_get(v_fst_3559_, 1);
v___x_3631_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__5));
v___x_3632_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_3625_, v___x_3574_);
v___x_3633_ = lean_string_append(v___x_3631_, v___x_3632_);
lean_dec_ref(v___x_3632_);
v___x_3634_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__6));
v___x_3635_ = lean_string_append(v___x_3633_, v___x_3634_);
lean_inc(v_optName_3630_);
v___x_3636_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_optName_3630_, v___x_3574_);
v___x_3637_ = lean_string_append(v___x_3635_, v___x_3636_);
lean_dec_ref(v___x_3636_);
v___x_3638_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__3));
v___x_3639_ = lean_string_append(v___x_3637_, v___x_3638_);
v___x_3640_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_3639_);
if (lean_obj_tag(v___x_3640_) == 0)
{
lean_object* v___x_3641_; lean_object* v___x_3643_; 
lean_dec_ref_known(v___x_3640_, 1);
lean_del_object(v___x_3620_);
lean_del_object(v___x_3579_);
v___x_3641_ = lean_box(v___x_3574_);
if (v_isShared_3585_ == 0)
{
lean_ctor_set(v___x_3584_, 1, v___x_3641_);
v___x_3643_ = v___x_3584_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_fst_3581_);
lean_ctor_set(v_reuseFailAlloc_3644_, 1, v___x_3641_);
v___x_3643_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
v_a_3570_ = v___x_3643_;
goto v___jp_3569_;
}
}
else
{
lean_object* v_a_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3660_; 
lean_del_object(v___x_3584_);
lean_dec(v_fst_3581_);
lean_dec(v___x_3561_);
lean_dec(v_sp_3560_);
lean_dec_ref(v_fst_3559_);
v_a_3645_ = lean_ctor_get(v___x_3640_, 0);
v_isSharedCheck_3660_ = !lean_is_exclusive(v___x_3640_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3647_ = v___x_3640_;
v_isShared_3648_ = v_isSharedCheck_3660_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_a_3645_);
lean_dec(v___x_3640_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3660_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___x_3649_; lean_object* v___x_3651_; 
v___x_3649_ = lean_io_error_to_string(v_a_3645_);
if (v_isShared_3621_ == 0)
{
lean_ctor_set_tag(v___x_3620_, 3);
lean_ctor_set(v___x_3620_, 0, v___x_3649_);
v___x_3651_ = v___x_3620_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v___x_3649_);
v___x_3651_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
lean_object* v___x_3652_; lean_object* v___x_3654_; 
v___x_3652_ = l_Lean_MessageData_ofFormat(v___x_3651_);
lean_inc(v_ref_3626_);
if (v_isShared_3580_ == 0)
{
lean_ctor_set(v___x_3579_, 1, v___x_3652_);
lean_ctor_set(v___x_3579_, 0, v_ref_3626_);
v___x_3654_ = v___x_3579_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_ref_3626_);
lean_ctor_set(v_reuseFailAlloc_3658_, 1, v___x_3652_);
v___x_3654_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
lean_object* v___x_3656_; 
if (v_isShared_3648_ == 0)
{
lean_ctor_set(v___x_3647_, 0, v___x_3654_);
v___x_3656_ = v___x_3647_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v___x_3654_);
v___x_3656_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
return v___x_3656_;
}
}
}
}
}
}
else
{
lean_object* v_range_3661_; lean_object* v_val_3662_; lean_object* v_pos_3663_; lean_object* v_optName_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3668_; 
lean_dec(v___y_3625_);
lean_del_object(v___x_3620_);
lean_del_object(v___x_3579_);
v_range_3661_ = lean_ctor_get(v_val_3618_, 0);
lean_inc_ref(v_range_3661_);
lean_dec(v_val_3618_);
v_val_3662_ = lean_ctor_get(v_a_3629_, 0);
lean_inc(v_val_3662_);
lean_dec_ref_known(v_a_3629_, 1);
v_pos_3663_ = lean_ctor_get(v_range_3661_, 0);
lean_inc_ref(v_pos_3663_);
lean_dec_ref(v_range_3661_);
v_optName_3664_ = lean_ctor_get(v_fst_3559_, 1);
lean_inc(v_optName_3664_);
v___x_3665_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3665_, 0, v_val_3662_);
lean_ctor_set(v___x_3665_, 1, v_pos_3663_);
lean_ctor_set(v___x_3665_, 2, v_optName_3664_);
v___x_3666_ = lean_array_push(v_fst_3581_, v___x_3665_);
if (v_isShared_3585_ == 0)
{
lean_ctor_set(v___x_3584_, 0, v___x_3666_);
v___x_3668_ = v___x_3584_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v___x_3666_);
lean_ctor_set(v_reuseFailAlloc_3669_, 1, v_snd_3582_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
v_a_3570_ = v___x_3668_;
goto v___jp_3569_;
}
}
}
else
{
lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3685_; 
lean_dec(v___y_3625_);
lean_dec(v_val_3618_);
lean_del_object(v___x_3584_);
lean_dec(v_snd_3582_);
lean_dec(v_fst_3581_);
lean_dec(v___x_3561_);
lean_dec(v_sp_3560_);
lean_dec_ref(v_fst_3559_);
v_a_3670_ = lean_ctor_get(v___x_3628_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3628_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3672_ = v___x_3628_;
v_isShared_3673_ = v_isSharedCheck_3685_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v___x_3628_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3685_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3674_; lean_object* v___x_3676_; 
v___x_3674_ = lean_io_error_to_string(v_a_3670_);
if (v_isShared_3621_ == 0)
{
lean_ctor_set_tag(v___x_3620_, 3);
lean_ctor_set(v___x_3620_, 0, v___x_3674_);
v___x_3676_ = v___x_3620_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v___x_3674_);
v___x_3676_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
lean_object* v___x_3677_; lean_object* v___x_3679_; 
v___x_3677_ = l_Lean_MessageData_ofFormat(v___x_3676_);
lean_inc(v_ref_3626_);
if (v_isShared_3580_ == 0)
{
lean_ctor_set(v___x_3579_, 1, v___x_3677_);
lean_ctor_set(v___x_3579_, 0, v_ref_3626_);
v___x_3679_ = v___x_3579_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_ref_3626_);
lean_ctor_set(v_reuseFailAlloc_3683_, 1, v___x_3677_);
v___x_3679_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
lean_object* v___x_3681_; 
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 0, v___x_3679_);
v___x_3681_ = v___x_3672_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v___x_3679_);
v___x_3681_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
return v___x_3681_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3694_; 
lean_del_object(v___x_3620_);
lean_dec(v_val_3618_);
lean_del_object(v___x_3584_);
lean_dec(v_snd_3582_);
lean_dec(v_fst_3581_);
lean_del_object(v___x_3579_);
lean_dec(v___x_3561_);
lean_dec(v_sp_3560_);
lean_dec_ref(v_fst_3559_);
v_a_3687_ = lean_ctor_get(v___x_3622_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3622_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3689_ = v___x_3622_;
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_a_3687_);
lean_dec(v___x_3622_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v___x_3692_; 
if (v_isShared_3690_ == 0)
{
v___x_3692_ = v___x_3689_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_a_3687_);
v___x_3692_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
return v___x_3692_;
}
}
}
}
}
}
else
{
lean_object* v_a_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3703_; 
lean_del_object(v___x_3584_);
lean_dec(v_snd_3582_);
lean_dec(v_fst_3581_);
lean_del_object(v___x_3579_);
lean_dec(v_fst_3577_);
lean_dec(v___x_3561_);
lean_dec(v_sp_3560_);
lean_dec_ref(v_fst_3559_);
v_a_3696_ = lean_ctor_get(v___x_3586_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3586_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3698_ = v___x_3586_;
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_a_3696_);
lean_dec(v___x_3586_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3703_;
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
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_a_3696_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
}
}
v___jp_3569_:
{
size_t v___x_3571_; size_t v___x_3572_; 
v___x_3571_ = ((size_t)1ULL);
v___x_3572_ = lean_usize_add(v_i_3564_, v___x_3571_);
v_i_3564_ = v___x_3572_;
v_b_3565_ = v_a_3570_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_3559_ = stack[0].m_obj;
lean_object* v_sp_3560_ = stack[1].m_obj;
lean_object* v___x_3561_ = stack[2].m_obj;
lean_object* v_as_3562_ = stack[3].m_obj;
size_t v_sz_3563_ = stack[4].m_num;
size_t v_i_3564_ = stack[5].m_num;
lean_object* v_b_3565_ = stack[6].m_obj;
lean_object* v___y_3566_ = stack[7].m_obj;
lean_object* v___y_3567_ = stack[8].m_obj;
lean_object* v_res_3707_;
v_res_3707_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(v_fst_3559_, v_sp_3560_, v___x_3561_, v_as_3562_, v_sz_3563_, v_i_3564_, v_b_3565_, v___y_3566_, v___y_3567_);
stack->m_obj
 = v_res_3707_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1___boxed(lean_object* v_fst_3708_, lean_object* v_sp_3709_, lean_object* v___x_3710_, lean_object* v_as_3711_, lean_object* v_sz_3712_, lean_object* v_i_3713_, lean_object* v_b_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_){
_start:
{
size_t v_sz_boxed_3718_; size_t v_i_boxed_3719_; lean_object* v_res_3720_; 
v_sz_boxed_3718_ = lean_unbox_usize(v_sz_3712_);
lean_dec(v_sz_3712_);
v_i_boxed_3719_ = lean_unbox_usize(v_i_3713_);
lean_dec(v_i_3713_);
v_res_3720_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(v_fst_3708_, v_sp_3709_, v___x_3710_, v_as_3711_, v_sz_boxed_3718_, v_i_boxed_3719_, v_b_3714_, v___y_3715_, v___y_3716_);
lean_dec(v___y_3716_);
lean_dec_ref(v___y_3715_);
lean_dec_ref(v_as_3711_);
return v_res_3720_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(lean_object* v_x_3721_, lean_object* v_x_3722_){
_start:
{
if (lean_obj_tag(v_x_3722_) == 0)
{
return v_x_3721_;
}
else
{
lean_object* v_key_3723_; lean_object* v_value_3724_; lean_object* v_tail_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; 
v_key_3723_ = lean_ctor_get(v_x_3722_, 0);
v_value_3724_ = lean_ctor_get(v_x_3722_, 1);
v_tail_3725_ = lean_ctor_get(v_x_3722_, 2);
lean_inc(v_value_3724_);
lean_inc(v_key_3723_);
v___x_3726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3726_, 0, v_key_3723_);
lean_ctor_set(v___x_3726_, 1, v_value_3724_);
v___x_3727_ = lean_array_push(v_x_3721_, v___x_3726_);
v_x_3721_ = v___x_3727_;
v_x_3722_ = v_tail_3725_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2___boxed(lean_object* v_x_3729_, lean_object* v_x_3730_){
_start:
{
lean_object* v_res_3731_; 
v_res_3731_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(v_x_3729_, v_x_3730_);
lean_dec(v_x_3730_);
return v_res_3731_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(lean_object* v_as_3732_, size_t v_i_3733_, size_t v_stop_3734_, lean_object* v_b_3735_){
_start:
{
uint8_t v___x_3736_; 
v___x_3736_ = lean_usize_dec_eq(v_i_3733_, v_stop_3734_);
if (v___x_3736_ == 0)
{
lean_object* v___x_3737_; lean_object* v___x_3738_; size_t v___x_3739_; size_t v___x_3740_; 
v___x_3737_ = lean_array_uget_borrowed(v_as_3732_, v_i_3733_);
v___x_3738_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(v_b_3735_, v___x_3737_);
v___x_3739_ = ((size_t)1ULL);
v___x_3740_ = lean_usize_add(v_i_3733_, v___x_3739_);
v_i_3733_ = v___x_3740_;
v_b_3735_ = v___x_3738_;
goto _start;
}
else
{
return v_b_3735_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3732_ = stack[0].m_obj;
size_t v_i_3733_ = stack[1].m_num;
size_t v_stop_3734_ = stack[2].m_num;
lean_object* v_b_3735_ = stack[3].m_obj;
lean_object* v_res_3742_;
v_res_3742_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_as_3732_, v_i_3733_, v_stop_3734_, v_b_3735_);
stack->m_obj
 = v_res_3742_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3___boxed(lean_object* v_as_3743_, lean_object* v_i_3744_, lean_object* v_stop_3745_, lean_object* v_b_3746_){
_start:
{
size_t v_i_boxed_3747_; size_t v_stop_boxed_3748_; lean_object* v_res_3749_; 
v_i_boxed_3747_ = lean_unbox_usize(v_i_3744_);
lean_dec(v_i_3744_);
v_stop_boxed_3748_ = lean_unbox_usize(v_stop_3745_);
lean_dec(v_stop_3745_);
v_res_3749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_as_3743_, v_i_boxed_3747_, v_stop_boxed_3748_, v_b_3746_);
lean_dec_ref(v_as_3743_);
return v_res_3749_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(lean_object* v_sp_3750_, lean_object* v___x_3751_, lean_object* v_as_3752_, size_t v_sz_3753_, size_t v_i_3754_, lean_object* v_b_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
uint8_t v___x_3759_; 
v___x_3759_ = lean_usize_dec_lt(v_i_3754_, v_sz_3753_);
if (v___x_3759_ == 0)
{
lean_object* v___x_3760_; 
lean_dec(v___x_3751_);
lean_dec(v_sp_3750_);
v___x_3760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3760_, 0, v_b_3755_);
return v___x_3760_;
}
else
{
lean_object* v_a_3761_; lean_object* v_fst_3762_; lean_object* v_snd_3763_; lean_object* v_fst_3764_; lean_object* v_snd_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3799_; 
v_a_3761_ = lean_array_uget_borrowed(v_as_3752_, v_i_3754_);
v_fst_3762_ = lean_ctor_get(v_a_3761_, 0);
v_snd_3763_ = lean_ctor_get(v_a_3761_, 1);
v_fst_3764_ = lean_ctor_get(v_b_3755_, 0);
v_snd_3765_ = lean_ctor_get(v_b_3755_, 1);
v_isSharedCheck_3799_ = !lean_is_exclusive(v_b_3755_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3767_ = v_b_3755_;
v_isShared_3768_ = v_isSharedCheck_3799_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_snd_3765_);
lean_inc(v_fst_3764_);
lean_dec(v_b_3755_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3799_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v___y_3770_; lean_object* v_size_3790_; lean_object* v_buckets_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; uint8_t v___x_3795_; 
v_size_3790_ = lean_ctor_get(v_snd_3763_, 0);
v_buckets_3791_ = lean_ctor_get(v_snd_3763_, 1);
v___x_3792_ = lean_mk_empty_array_with_capacity(v_size_3790_);
v___x_3793_ = lean_unsigned_to_nat(0u);
v___x_3794_ = lean_array_get_size(v_buckets_3791_);
v___x_3795_ = lean_nat_dec_lt(v___x_3793_, v___x_3794_);
if (v___x_3795_ == 0)
{
v___y_3770_ = v___x_3792_;
goto v___jp_3769_;
}
else
{
size_t v___x_3796_; size_t v___x_3797_; lean_object* v___x_3798_; 
v___x_3796_ = ((size_t)0ULL);
v___x_3797_ = lean_usize_of_nat(v___x_3794_);
v___x_3798_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_buckets_3791_, v___x_3796_, v___x_3797_, v___x_3792_);
v___y_3770_ = v___x_3798_;
goto v___jp_3769_;
}
v___jp_3769_:
{
lean_object* v___x_3772_; 
if (v_isShared_3768_ == 0)
{
v___x_3772_ = v___x_3767_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_fst_3764_);
lean_ctor_set(v_reuseFailAlloc_3789_, 1, v_snd_3765_);
v___x_3772_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
size_t v_sz_3773_; size_t v___x_3774_; lean_object* v___x_3775_; 
v_sz_3773_ = lean_array_size(v___y_3770_);
v___x_3774_ = ((size_t)0ULL);
lean_inc(v___x_3751_);
lean_inc(v_sp_3750_);
lean_inc(v_fst_3762_);
v___x_3775_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(v_fst_3762_, v_sp_3750_, v___x_3751_, v___y_3770_, v_sz_3773_, v___x_3774_, v___x_3772_, v___y_3756_, v___y_3757_);
lean_dec_ref(v___y_3770_);
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_object* v_a_3776_; lean_object* v_fst_3777_; lean_object* v_snd_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3788_; 
v_a_3776_ = lean_ctor_get(v___x_3775_, 0);
lean_inc(v_a_3776_);
lean_dec_ref_known(v___x_3775_, 1);
v_fst_3777_ = lean_ctor_get(v_a_3776_, 0);
v_snd_3778_ = lean_ctor_get(v_a_3776_, 1);
v_isSharedCheck_3788_ = !lean_is_exclusive(v_a_3776_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3780_ = v_a_3776_;
v_isShared_3781_ = v_isSharedCheck_3788_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_snd_3778_);
lean_inc(v_fst_3777_);
lean_dec(v_a_3776_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3788_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v___x_3783_; 
if (v_isShared_3781_ == 0)
{
v___x_3783_ = v___x_3780_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_fst_3777_);
lean_ctor_set(v_reuseFailAlloc_3787_, 1, v_snd_3778_);
v___x_3783_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
size_t v___x_3784_; size_t v___x_3785_; 
v___x_3784_ = ((size_t)1ULL);
v___x_3785_ = lean_usize_add(v_i_3754_, v___x_3784_);
v_i_3754_ = v___x_3785_;
v_b_3755_ = v___x_3783_;
goto _start;
}
}
}
else
{
lean_dec(v___x_3751_);
lean_dec(v_sp_3750_);
return v___x_3775_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_sp_3750_ = stack[0].m_obj;
lean_object* v___x_3751_ = stack[1].m_obj;
lean_object* v_as_3752_ = stack[2].m_obj;
size_t v_sz_3753_ = stack[3].m_num;
size_t v_i_3754_ = stack[4].m_num;
lean_object* v_b_3755_ = stack[5].m_obj;
lean_object* v___y_3756_ = stack[6].m_obj;
lean_object* v___y_3757_ = stack[7].m_obj;
lean_object* v_res_3800_;
v_res_3800_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(v_sp_3750_, v___x_3751_, v_as_3752_, v_sz_3753_, v_i_3754_, v_b_3755_, v___y_3756_, v___y_3757_);
stack->m_obj
 = v_res_3800_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4___boxed(lean_object* v_sp_3801_, lean_object* v___x_3802_, lean_object* v_as_3803_, lean_object* v_sz_3804_, lean_object* v_i_3805_, lean_object* v_b_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_){
_start:
{
size_t v_sz_boxed_3810_; size_t v_i_boxed_3811_; lean_object* v_res_3812_; 
v_sz_boxed_3810_ = lean_unbox_usize(v_sz_3804_);
lean_dec(v_sz_3804_);
v_i_boxed_3811_ = lean_unbox_usize(v_i_3805_);
lean_dec(v_i_3805_);
v_res_3812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(v_sp_3801_, v___x_3802_, v_as_3803_, v_sz_boxed_3810_, v_i_boxed_3811_, v_b_3806_, v___y_3807_, v___y_3808_);
lean_dec(v___y_3808_);
lean_dec_ref(v___y_3807_);
lean_dec_ref(v_as_3803_);
return v_res_3812_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(uint8_t v___y_3813_, lean_object* v_as_3814_, size_t v_i_3815_, size_t v_stop_3816_){
_start:
{
uint8_t v___x_3817_; 
v___x_3817_ = lean_usize_dec_eq(v_i_3815_, v_stop_3816_);
if (v___x_3817_ == 0)
{
lean_object* v___x_3818_; lean_object* v_snd_3819_; lean_object* v_size_3820_; uint8_t v___x_3821_; lean_object* v___x_3822_; uint8_t v___x_3823_; 
v___x_3818_ = lean_array_uget_borrowed(v_as_3814_, v_i_3815_);
v_snd_3819_ = lean_ctor_get(v___x_3818_, 1);
v_size_3820_ = lean_ctor_get(v_snd_3819_, 0);
v___x_3821_ = 1;
v___x_3822_ = lean_unsigned_to_nat(0u);
v___x_3823_ = lean_nat_dec_eq(v_size_3820_, v___x_3822_);
if (v___x_3823_ == 0)
{
return v___x_3821_;
}
else
{
if (v___y_3813_ == 0)
{
size_t v___x_3824_; size_t v___x_3825_; 
v___x_3824_ = ((size_t)1ULL);
v___x_3825_ = lean_usize_add(v_i_3815_, v___x_3824_);
v_i_3815_ = v___x_3825_;
goto _start;
}
else
{
return v___x_3821_;
}
}
}
else
{
uint8_t v___x_3827_; 
v___x_3827_ = 0;
return v___x_3827_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10_0interp(lean_interpreter_value* stack)
{
uint8_t v___y_3813_ = stack[0].m_num;
lean_object* v_as_3814_ = stack[1].m_obj;
size_t v_i_3815_ = stack[2].m_num;
size_t v_stop_3816_ = stack[3].m_num;
uint8_t v_res_3828_;
v_res_3828_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(v___y_3813_, v_as_3814_, v_i_3815_, v_stop_3816_);
stack->m_num = v_res_3828_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10___boxed(lean_object* v___y_3829_, lean_object* v_as_3830_, lean_object* v_i_3831_, lean_object* v_stop_3832_){
_start:
{
uint8_t v___y_18027__boxed_3833_; size_t v_i_boxed_3834_; size_t v_stop_boxed_3835_; uint8_t v_res_3836_; lean_object* v_r_3837_; 
v___y_18027__boxed_3833_ = lean_unbox(v___y_3829_);
v_i_boxed_3834_ = lean_unbox_usize(v_i_3831_);
lean_dec(v_i_3831_);
v_stop_boxed_3835_ = lean_unbox_usize(v_stop_3832_);
lean_dec(v_stop_3832_);
v_res_3836_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(v___y_18027__boxed_3833_, v_as_3830_, v_i_boxed_3834_, v_stop_boxed_3835_);
lean_dec_ref(v_as_3830_);
v_r_3837_ = lean_box(v_res_3836_);
return v_r_3837_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(lean_object* v_k_3838_, lean_object* v_v_3839_, lean_object* v_t_3840_){
_start:
{
lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; 
if (lean_obj_tag(v_t_3840_) == 0)
{
lean_object* v_size_3855_; lean_object* v_k_3856_; lean_object* v_v_3857_; lean_object* v_l_3858_; lean_object* v_r_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_4119_; 
v_size_3855_ = lean_ctor_get(v_t_3840_, 0);
v_k_3856_ = lean_ctor_get(v_t_3840_, 1);
v_v_3857_ = lean_ctor_get(v_t_3840_, 2);
v_l_3858_ = lean_ctor_get(v_t_3840_, 3);
v_r_3859_ = lean_ctor_get(v_t_3840_, 4);
v_isSharedCheck_4119_ = !lean_is_exclusive(v_t_3840_);
if (v_isSharedCheck_4119_ == 0)
{
v___x_3861_ = v_t_3840_;
v_isShared_3862_ = v_isSharedCheck_4119_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_r_3859_);
lean_inc(v_l_3858_);
lean_inc(v_v_3857_);
lean_inc(v_k_3856_);
lean_inc(v_size_3855_);
lean_dec(v_t_3840_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_4119_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
lean_object* v___y_3864_; lean_object* v___y_3865_; lean_object* v___y_3866_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v___y_3869_; lean_object* v___y_3870_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v___y_3895_; lean_object* v___y_3896_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___y_3899_; lean_object* v___y_3900_; lean_object* v___y_3901_; lean_object* v___y_3902_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; uint8_t v___y_3913_; lean_object* v_fst_4113_; lean_object* v_snd_4114_; lean_object* v_fst_4115_; lean_object* v_snd_4116_; uint8_t v___x_4117_; 
v_fst_4113_ = lean_ctor_get(v_k_3838_, 0);
v_snd_4114_ = lean_ctor_get(v_k_3838_, 1);
v_fst_4115_ = lean_ctor_get(v_k_3856_, 0);
v_snd_4116_ = lean_ctor_get(v_k_3856_, 1);
v___x_4117_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_fst_4113_, v_fst_4115_);
if (v___x_4117_ == 1)
{
uint8_t v___x_4118_; 
v___x_4118_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_snd_4114_, v_snd_4116_);
v___y_3913_ = v___x_4118_;
goto v___jp_3912_;
}
else
{
v___y_3913_ = v___x_4117_;
goto v___jp_3912_;
}
v___jp_3863_:
{
lean_object* v___x_3871_; lean_object* v___x_3873_; 
v___x_3871_ = lean_nat_add(v___y_3867_, v___y_3870_);
lean_dec(v___y_3870_);
lean_dec(v___y_3867_);
if (v_isShared_3862_ == 0)
{
lean_ctor_set(v___x_3861_, 3, v___y_3868_);
lean_ctor_set(v___x_3861_, 0, v___x_3871_);
v___x_3873_ = v___x_3861_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v___x_3871_);
lean_ctor_set(v_reuseFailAlloc_3875_, 1, v_k_3856_);
lean_ctor_set(v_reuseFailAlloc_3875_, 2, v_v_3857_);
lean_ctor_set(v_reuseFailAlloc_3875_, 3, v___y_3868_);
lean_ctor_set(v_reuseFailAlloc_3875_, 4, v_r_3859_);
v___x_3873_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
lean_object* v___x_3874_; 
v___x_3874_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3874_, 0, v___y_3864_);
lean_ctor_set(v___x_3874_, 1, v___y_3865_);
lean_ctor_set(v___x_3874_, 2, v___y_3866_);
lean_ctor_set(v___x_3874_, 3, v___y_3869_);
lean_ctor_set(v___x_3874_, 4, v___x_3873_);
return v___x_3874_;
}
}
v___jp_3876_:
{
lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; 
v___x_3889_ = lean_nat_add(v___y_3883_, v___y_3888_);
lean_dec(v___y_3888_);
lean_dec(v___y_3883_);
v___x_3890_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3890_, 0, v___x_3889_);
lean_ctor_set(v___x_3890_, 1, v___y_3885_);
lean_ctor_set(v___x_3890_, 2, v___y_3881_);
lean_ctor_set(v___x_3890_, 3, v___y_3880_);
lean_ctor_set(v___x_3890_, 4, v___y_3884_);
v___x_3891_ = lean_nat_add(v___y_3879_, v___y_3887_);
lean_dec(v___y_3887_);
if (lean_obj_tag(v___y_3886_) == 0)
{
lean_object* v_size_3892_; 
v_size_3892_ = lean_ctor_get(v___y_3886_, 0);
lean_inc(v_size_3892_);
v___y_3864_ = v___y_3877_;
v___y_3865_ = v___y_3878_;
v___y_3866_ = v___y_3882_;
v___y_3867_ = v___x_3891_;
v___y_3868_ = v___y_3886_;
v___y_3869_ = v___x_3890_;
v___y_3870_ = v_size_3892_;
goto v___jp_3863_;
}
else
{
lean_object* v___x_3893_; 
v___x_3893_ = lean_unsigned_to_nat(0u);
v___y_3864_ = v___y_3877_;
v___y_3865_ = v___y_3878_;
v___y_3866_ = v___y_3882_;
v___y_3867_ = v___x_3891_;
v___y_3868_ = v___y_3886_;
v___y_3869_ = v___x_3890_;
v___y_3870_ = v___x_3893_;
goto v___jp_3863_;
}
}
v___jp_3894_:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
v___x_3907_ = lean_nat_add(v___y_3905_, v___y_3906_);
lean_dec(v___y_3906_);
lean_dec(v___y_3905_);
v___x_3908_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3907_);
lean_ctor_set(v___x_3908_, 1, v_k_3856_);
lean_ctor_set(v___x_3908_, 2, v_v_3857_);
lean_ctor_set(v___x_3908_, 3, v_l_3858_);
lean_ctor_set(v___x_3908_, 4, v___y_3895_);
v___x_3909_ = lean_nat_add(v___y_3898_, v___y_3903_);
lean_dec(v___y_3903_);
if (lean_obj_tag(v___y_3896_) == 0)
{
lean_object* v_size_3910_; 
v_size_3910_ = lean_ctor_get(v___y_3896_, 0);
lean_inc(v_size_3910_);
v___y_3842_ = v___x_3908_;
v___y_3843_ = v___y_3897_;
v___y_3844_ = v___y_3896_;
v___y_3845_ = v___x_3909_;
v___y_3846_ = v___y_3899_;
v___y_3847_ = v___y_3900_;
v___y_3848_ = v___y_3901_;
v___y_3849_ = v___y_3902_;
v___y_3850_ = v___y_3904_;
v___y_3851_ = v_size_3910_;
goto v___jp_3841_;
}
else
{
lean_object* v___x_3911_; 
v___x_3911_ = lean_unsigned_to_nat(0u);
v___y_3842_ = v___x_3908_;
v___y_3843_ = v___y_3897_;
v___y_3844_ = v___y_3896_;
v___y_3845_ = v___x_3909_;
v___y_3846_ = v___y_3899_;
v___y_3847_ = v___y_3900_;
v___y_3848_ = v___y_3901_;
v___y_3849_ = v___y_3902_;
v___y_3850_ = v___y_3904_;
v___y_3851_ = v___x_3911_;
goto v___jp_3841_;
}
}
v___jp_3912_:
{
switch(v___y_3913_)
{
case 0:
{
lean_object* v_impl_3914_; lean_object* v___x_3915_; 
lean_dec(v_size_3855_);
v_impl_3914_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_3838_, v_v_3839_, v_l_3858_);
v___x_3915_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3859_) == 0)
{
lean_object* v_size_3916_; lean_object* v_size_3917_; lean_object* v_k_3918_; lean_object* v_v_3919_; lean_object* v_l_3920_; lean_object* v_r_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; uint8_t v___x_3924_; 
v_size_3916_ = lean_ctor_get(v_r_3859_, 0);
v_size_3917_ = lean_ctor_get(v_impl_3914_, 0);
v_k_3918_ = lean_ctor_get(v_impl_3914_, 1);
v_v_3919_ = lean_ctor_get(v_impl_3914_, 2);
v_l_3920_ = lean_ctor_get(v_impl_3914_, 3);
v_r_3921_ = lean_ctor_get(v_impl_3914_, 4);
v___x_3922_ = lean_unsigned_to_nat(3u);
v___x_3923_ = lean_nat_mul(v___x_3922_, v_size_3916_);
v___x_3924_ = lean_nat_dec_lt(v___x_3923_, v_size_3917_);
lean_dec(v___x_3923_);
if (v___x_3924_ == 0)
{
lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
lean_del_object(v___x_3861_);
v___x_3925_ = lean_nat_add(v___x_3915_, v_size_3917_);
v___x_3926_ = lean_nat_add(v___x_3925_, v_size_3916_);
lean_dec(v___x_3925_);
v___x_3927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3926_);
lean_ctor_set(v___x_3927_, 1, v_k_3856_);
lean_ctor_set(v___x_3927_, 2, v_v_3857_);
lean_ctor_set(v___x_3927_, 3, v_impl_3914_);
lean_ctor_set(v___x_3927_, 4, v_r_3859_);
return v___x_3927_;
}
else
{
lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3964_; 
lean_inc(v_r_3921_);
lean_inc(v_l_3920_);
lean_inc(v_v_3919_);
lean_inc(v_k_3918_);
lean_inc(v_size_3917_);
v_isSharedCheck_3964_ = !lean_is_exclusive(v_impl_3914_);
if (v_isSharedCheck_3964_ == 0)
{
lean_object* v_unused_3965_; lean_object* v_unused_3966_; lean_object* v_unused_3967_; lean_object* v_unused_3968_; lean_object* v_unused_3969_; 
v_unused_3965_ = lean_ctor_get(v_impl_3914_, 4);
lean_dec(v_unused_3965_);
v_unused_3966_ = lean_ctor_get(v_impl_3914_, 3);
lean_dec(v_unused_3966_);
v_unused_3967_ = lean_ctor_get(v_impl_3914_, 2);
lean_dec(v_unused_3967_);
v_unused_3968_ = lean_ctor_get(v_impl_3914_, 1);
lean_dec(v_unused_3968_);
v_unused_3969_ = lean_ctor_get(v_impl_3914_, 0);
lean_dec(v_unused_3969_);
v___x_3929_ = v_impl_3914_;
v_isShared_3930_ = v_isSharedCheck_3964_;
goto v_resetjp_3928_;
}
else
{
lean_dec(v_impl_3914_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3964_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v_size_3931_; lean_object* v_size_3932_; lean_object* v_k_3933_; lean_object* v_v_3934_; lean_object* v_l_3935_; lean_object* v_r_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; uint8_t v___x_3939_; 
v_size_3931_ = lean_ctor_get(v_l_3920_, 0);
v_size_3932_ = lean_ctor_get(v_r_3921_, 0);
v_k_3933_ = lean_ctor_get(v_r_3921_, 1);
v_v_3934_ = lean_ctor_get(v_r_3921_, 2);
v_l_3935_ = lean_ctor_get(v_r_3921_, 3);
v_r_3936_ = lean_ctor_get(v_r_3921_, 4);
v___x_3937_ = lean_unsigned_to_nat(2u);
v___x_3938_ = lean_nat_mul(v___x_3937_, v_size_3931_);
v___x_3939_ = lean_nat_dec_lt(v_size_3932_, v___x_3938_);
lean_dec(v___x_3938_);
if (v___x_3939_ == 0)
{
lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; 
lean_inc(v_r_3936_);
lean_inc(v_l_3935_);
lean_inc(v_v_3934_);
lean_inc(v_k_3933_);
lean_del_object(v___x_3929_);
lean_dec(v_r_3921_);
v___x_3940_ = lean_nat_add(v___x_3915_, v_size_3917_);
lean_dec(v_size_3917_);
v___x_3941_ = lean_nat_add(v___x_3940_, v_size_3916_);
lean_dec(v___x_3940_);
v___x_3942_ = lean_nat_add(v___x_3915_, v_size_3931_);
if (lean_obj_tag(v_l_3935_) == 0)
{
lean_object* v_size_3943_; 
v_size_3943_ = lean_ctor_get(v_l_3935_, 0);
lean_inc(v_size_3943_);
lean_inc(v_size_3916_);
v___y_3877_ = v___x_3941_;
v___y_3878_ = v_k_3933_;
v___y_3879_ = v___x_3915_;
v___y_3880_ = v_l_3920_;
v___y_3881_ = v_v_3919_;
v___y_3882_ = v_v_3934_;
v___y_3883_ = v___x_3942_;
v___y_3884_ = v_l_3935_;
v___y_3885_ = v_k_3918_;
v___y_3886_ = v_r_3936_;
v___y_3887_ = v_size_3916_;
v___y_3888_ = v_size_3943_;
goto v___jp_3876_;
}
else
{
lean_object* v___x_3944_; 
v___x_3944_ = lean_unsigned_to_nat(0u);
lean_inc(v_size_3916_);
v___y_3877_ = v___x_3941_;
v___y_3878_ = v_k_3933_;
v___y_3879_ = v___x_3915_;
v___y_3880_ = v_l_3920_;
v___y_3881_ = v_v_3919_;
v___y_3882_ = v_v_3934_;
v___y_3883_ = v___x_3942_;
v___y_3884_ = v_l_3935_;
v___y_3885_ = v_k_3918_;
v___y_3886_ = v_r_3936_;
v___y_3887_ = v_size_3916_;
v___y_3888_ = v___x_3944_;
goto v___jp_3876_;
}
}
else
{
lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3950_; 
lean_del_object(v___x_3861_);
v___x_3945_ = lean_nat_add(v___x_3915_, v_size_3917_);
lean_dec(v_size_3917_);
v___x_3946_ = lean_nat_add(v___x_3945_, v_size_3916_);
lean_dec(v___x_3945_);
v___x_3947_ = lean_nat_add(v___x_3915_, v_size_3916_);
v___x_3948_ = lean_nat_add(v___x_3947_, v_size_3932_);
lean_dec(v___x_3947_);
lean_inc_ref(v_r_3859_);
if (v_isShared_3930_ == 0)
{
lean_ctor_set(v___x_3929_, 4, v_r_3859_);
lean_ctor_set(v___x_3929_, 3, v_r_3921_);
lean_ctor_set(v___x_3929_, 2, v_v_3857_);
lean_ctor_set(v___x_3929_, 1, v_k_3856_);
lean_ctor_set(v___x_3929_, 0, v___x_3948_);
v___x_3950_ = v___x_3929_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v___x_3948_);
lean_ctor_set(v_reuseFailAlloc_3963_, 1, v_k_3856_);
lean_ctor_set(v_reuseFailAlloc_3963_, 2, v_v_3857_);
lean_ctor_set(v_reuseFailAlloc_3963_, 3, v_r_3921_);
lean_ctor_set(v_reuseFailAlloc_3963_, 4, v_r_3859_);
v___x_3950_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_3957_; 
v_isSharedCheck_3957_ = !lean_is_exclusive(v_r_3859_);
if (v_isSharedCheck_3957_ == 0)
{
lean_object* v_unused_3958_; lean_object* v_unused_3959_; lean_object* v_unused_3960_; lean_object* v_unused_3961_; lean_object* v_unused_3962_; 
v_unused_3958_ = lean_ctor_get(v_r_3859_, 4);
lean_dec(v_unused_3958_);
v_unused_3959_ = lean_ctor_get(v_r_3859_, 3);
lean_dec(v_unused_3959_);
v_unused_3960_ = lean_ctor_get(v_r_3859_, 2);
lean_dec(v_unused_3960_);
v_unused_3961_ = lean_ctor_get(v_r_3859_, 1);
lean_dec(v_unused_3961_);
v_unused_3962_ = lean_ctor_get(v_r_3859_, 0);
lean_dec(v_unused_3962_);
v___x_3952_ = v_r_3859_;
v_isShared_3953_ = v_isSharedCheck_3957_;
goto v_resetjp_3951_;
}
else
{
lean_dec(v_r_3859_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_3957_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
lean_object* v___x_3955_; 
if (v_isShared_3953_ == 0)
{
lean_ctor_set(v___x_3952_, 4, v___x_3950_);
lean_ctor_set(v___x_3952_, 3, v_l_3920_);
lean_ctor_set(v___x_3952_, 2, v_v_3919_);
lean_ctor_set(v___x_3952_, 1, v_k_3918_);
lean_ctor_set(v___x_3952_, 0, v___x_3946_);
v___x_3955_ = v___x_3952_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v___x_3946_);
lean_ctor_set(v_reuseFailAlloc_3956_, 1, v_k_3918_);
lean_ctor_set(v_reuseFailAlloc_3956_, 2, v_v_3919_);
lean_ctor_set(v_reuseFailAlloc_3956_, 3, v_l_3920_);
lean_ctor_set(v_reuseFailAlloc_3956_, 4, v___x_3950_);
v___x_3955_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
return v___x_3955_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3970_; 
lean_del_object(v___x_3861_);
v_l_3970_ = lean_ctor_get(v_impl_3914_, 3);
if (lean_obj_tag(v_l_3970_) == 0)
{
lean_object* v_r_3971_; lean_object* v_k_3972_; lean_object* v_v_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3982_; 
lean_inc_ref(v_l_3970_);
v_r_3971_ = lean_ctor_get(v_impl_3914_, 4);
v_k_3972_ = lean_ctor_get(v_impl_3914_, 1);
v_v_3973_ = lean_ctor_get(v_impl_3914_, 2);
v_isSharedCheck_3982_ = !lean_is_exclusive(v_impl_3914_);
if (v_isSharedCheck_3982_ == 0)
{
lean_object* v_unused_3983_; lean_object* v_unused_3984_; 
v_unused_3983_ = lean_ctor_get(v_impl_3914_, 3);
lean_dec(v_unused_3983_);
v_unused_3984_ = lean_ctor_get(v_impl_3914_, 0);
lean_dec(v_unused_3984_);
v___x_3975_ = v_impl_3914_;
v_isShared_3976_ = v_isSharedCheck_3982_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_r_3971_);
lean_inc(v_v_3973_);
lean_inc(v_k_3972_);
lean_dec(v_impl_3914_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_3982_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3977_; lean_object* v___x_3979_; 
v___x_3977_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3971_);
if (v_isShared_3976_ == 0)
{
lean_ctor_set(v___x_3975_, 3, v_r_3971_);
lean_ctor_set(v___x_3975_, 2, v_v_3857_);
lean_ctor_set(v___x_3975_, 1, v_k_3856_);
lean_ctor_set(v___x_3975_, 0, v___x_3915_);
v___x_3979_ = v___x_3975_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v___x_3915_);
lean_ctor_set(v_reuseFailAlloc_3981_, 1, v_k_3856_);
lean_ctor_set(v_reuseFailAlloc_3981_, 2, v_v_3857_);
lean_ctor_set(v_reuseFailAlloc_3981_, 3, v_r_3971_);
lean_ctor_set(v_reuseFailAlloc_3981_, 4, v_r_3971_);
v___x_3979_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
lean_object* v___x_3980_; 
v___x_3980_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3980_, 0, v___x_3977_);
lean_ctor_set(v___x_3980_, 1, v_k_3972_);
lean_ctor_set(v___x_3980_, 2, v_v_3973_);
lean_ctor_set(v___x_3980_, 3, v_l_3970_);
lean_ctor_set(v___x_3980_, 4, v___x_3979_);
return v___x_3980_;
}
}
}
else
{
lean_object* v_r_3985_; 
v_r_3985_ = lean_ctor_get(v_impl_3914_, 4);
lean_inc(v_r_3985_);
if (lean_obj_tag(v_r_3985_) == 0)
{
lean_object* v_k_3986_; lean_object* v_v_3987_; lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_4008_; 
lean_inc(v_l_3970_);
v_k_3986_ = lean_ctor_get(v_impl_3914_, 1);
v_v_3987_ = lean_ctor_get(v_impl_3914_, 2);
v_isSharedCheck_4008_ = !lean_is_exclusive(v_impl_3914_);
if (v_isSharedCheck_4008_ == 0)
{
lean_object* v_unused_4009_; lean_object* v_unused_4010_; lean_object* v_unused_4011_; 
v_unused_4009_ = lean_ctor_get(v_impl_3914_, 4);
lean_dec(v_unused_4009_);
v_unused_4010_ = lean_ctor_get(v_impl_3914_, 3);
lean_dec(v_unused_4010_);
v_unused_4011_ = lean_ctor_get(v_impl_3914_, 0);
lean_dec(v_unused_4011_);
v___x_3989_ = v_impl_3914_;
v_isShared_3990_ = v_isSharedCheck_4008_;
goto v_resetjp_3988_;
}
else
{
lean_inc(v_v_3987_);
lean_inc(v_k_3986_);
lean_dec(v_impl_3914_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_4008_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v_k_3991_; lean_object* v_v_3992_; lean_object* v___x_3994_; uint8_t v_isShared_3995_; uint8_t v_isSharedCheck_4004_; 
v_k_3991_ = lean_ctor_get(v_r_3985_, 1);
v_v_3992_ = lean_ctor_get(v_r_3985_, 2);
v_isSharedCheck_4004_ = !lean_is_exclusive(v_r_3985_);
if (v_isSharedCheck_4004_ == 0)
{
lean_object* v_unused_4005_; lean_object* v_unused_4006_; lean_object* v_unused_4007_; 
v_unused_4005_ = lean_ctor_get(v_r_3985_, 4);
lean_dec(v_unused_4005_);
v_unused_4006_ = lean_ctor_get(v_r_3985_, 3);
lean_dec(v_unused_4006_);
v_unused_4007_ = lean_ctor_get(v_r_3985_, 0);
lean_dec(v_unused_4007_);
v___x_3994_ = v_r_3985_;
v_isShared_3995_ = v_isSharedCheck_4004_;
goto v_resetjp_3993_;
}
else
{
lean_inc(v_v_3992_);
lean_inc(v_k_3991_);
lean_dec(v_r_3985_);
v___x_3994_ = lean_box(0);
v_isShared_3995_ = v_isSharedCheck_4004_;
goto v_resetjp_3993_;
}
v_resetjp_3993_:
{
lean_object* v___x_3996_; lean_object* v___x_3998_; 
v___x_3996_ = lean_unsigned_to_nat(3u);
if (v_isShared_3995_ == 0)
{
lean_ctor_set(v___x_3994_, 4, v_l_3970_);
lean_ctor_set(v___x_3994_, 3, v_l_3970_);
lean_ctor_set(v___x_3994_, 2, v_v_3987_);
lean_ctor_set(v___x_3994_, 1, v_k_3986_);
lean_ctor_set(v___x_3994_, 0, v___x_3915_);
v___x_3998_ = v___x_3994_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v___x_3915_);
lean_ctor_set(v_reuseFailAlloc_4003_, 1, v_k_3986_);
lean_ctor_set(v_reuseFailAlloc_4003_, 2, v_v_3987_);
lean_ctor_set(v_reuseFailAlloc_4003_, 3, v_l_3970_);
lean_ctor_set(v_reuseFailAlloc_4003_, 4, v_l_3970_);
v___x_3998_ = v_reuseFailAlloc_4003_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
lean_object* v___x_4000_; 
if (v_isShared_3990_ == 0)
{
lean_ctor_set(v___x_3989_, 4, v_l_3970_);
lean_ctor_set(v___x_3989_, 2, v_v_3857_);
lean_ctor_set(v___x_3989_, 1, v_k_3856_);
lean_ctor_set(v___x_3989_, 0, v___x_3915_);
v___x_4000_ = v___x_3989_;
goto v_reusejp_3999_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v___x_3915_);
lean_ctor_set(v_reuseFailAlloc_4002_, 1, v_k_3856_);
lean_ctor_set(v_reuseFailAlloc_4002_, 2, v_v_3857_);
lean_ctor_set(v_reuseFailAlloc_4002_, 3, v_l_3970_);
lean_ctor_set(v_reuseFailAlloc_4002_, 4, v_l_3970_);
v___x_4000_ = v_reuseFailAlloc_4002_;
goto v_reusejp_3999_;
}
v_reusejp_3999_:
{
lean_object* v___x_4001_; 
v___x_4001_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4001_, 0, v___x_3996_);
lean_ctor_set(v___x_4001_, 1, v_k_3991_);
lean_ctor_set(v___x_4001_, 2, v_v_3992_);
lean_ctor_set(v___x_4001_, 3, v___x_3998_);
lean_ctor_set(v___x_4001_, 4, v___x_4000_);
return v___x_4001_;
}
}
}
}
}
else
{
lean_object* v___x_4012_; lean_object* v___x_4013_; 
v___x_4012_ = lean_unsigned_to_nat(2u);
v___x_4013_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4013_, 0, v___x_4012_);
lean_ctor_set(v___x_4013_, 1, v_k_3856_);
lean_ctor_set(v___x_4013_, 2, v_v_3857_);
lean_ctor_set(v___x_4013_, 3, v_impl_3914_);
lean_ctor_set(v___x_4013_, 4, v_r_3985_);
return v___x_4013_;
}
}
}
}
case 1:
{
lean_object* v___x_4014_; 
lean_del_object(v___x_3861_);
lean_dec(v_v_3857_);
lean_dec(v_k_3856_);
v___x_4014_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4014_, 0, v_size_3855_);
lean_ctor_set(v___x_4014_, 1, v_k_3838_);
lean_ctor_set(v___x_4014_, 2, v_v_3839_);
lean_ctor_set(v___x_4014_, 3, v_l_3858_);
lean_ctor_set(v___x_4014_, 4, v_r_3859_);
return v___x_4014_;
}
default: 
{
lean_object* v_impl_4015_; lean_object* v___x_4016_; 
lean_del_object(v___x_3861_);
lean_dec(v_size_3855_);
v_impl_4015_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_3838_, v_v_3839_, v_r_3859_);
v___x_4016_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3858_) == 0)
{
lean_object* v_size_4017_; lean_object* v_size_4018_; lean_object* v_k_4019_; lean_object* v_v_4020_; lean_object* v_l_4021_; lean_object* v_r_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; uint8_t v___x_4025_; 
v_size_4017_ = lean_ctor_get(v_l_3858_, 0);
v_size_4018_ = lean_ctor_get(v_impl_4015_, 0);
v_k_4019_ = lean_ctor_get(v_impl_4015_, 1);
v_v_4020_ = lean_ctor_get(v_impl_4015_, 2);
v_l_4021_ = lean_ctor_get(v_impl_4015_, 3);
v_r_4022_ = lean_ctor_get(v_impl_4015_, 4);
v___x_4023_ = lean_unsigned_to_nat(3u);
v___x_4024_ = lean_nat_mul(v___x_4023_, v_size_4017_);
v___x_4025_ = lean_nat_dec_lt(v___x_4024_, v_size_4018_);
lean_dec(v___x_4024_);
if (v___x_4025_ == 0)
{
lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; 
v___x_4026_ = lean_nat_add(v___x_4016_, v_size_4017_);
v___x_4027_ = lean_nat_add(v___x_4026_, v_size_4018_);
lean_dec(v___x_4026_);
v___x_4028_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4028_, 0, v___x_4027_);
lean_ctor_set(v___x_4028_, 1, v_k_3856_);
lean_ctor_set(v___x_4028_, 2, v_v_3857_);
lean_ctor_set(v___x_4028_, 3, v_l_3858_);
lean_ctor_set(v___x_4028_, 4, v_impl_4015_);
return v___x_4028_;
}
else
{
lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4063_; 
lean_inc(v_r_4022_);
lean_inc(v_l_4021_);
lean_inc(v_v_4020_);
lean_inc(v_k_4019_);
lean_inc(v_size_4018_);
v_isSharedCheck_4063_ = !lean_is_exclusive(v_impl_4015_);
if (v_isSharedCheck_4063_ == 0)
{
lean_object* v_unused_4064_; lean_object* v_unused_4065_; lean_object* v_unused_4066_; lean_object* v_unused_4067_; lean_object* v_unused_4068_; 
v_unused_4064_ = lean_ctor_get(v_impl_4015_, 4);
lean_dec(v_unused_4064_);
v_unused_4065_ = lean_ctor_get(v_impl_4015_, 3);
lean_dec(v_unused_4065_);
v_unused_4066_ = lean_ctor_get(v_impl_4015_, 2);
lean_dec(v_unused_4066_);
v_unused_4067_ = lean_ctor_get(v_impl_4015_, 1);
lean_dec(v_unused_4067_);
v_unused_4068_ = lean_ctor_get(v_impl_4015_, 0);
lean_dec(v_unused_4068_);
v___x_4030_ = v_impl_4015_;
v_isShared_4031_ = v_isSharedCheck_4063_;
goto v_resetjp_4029_;
}
else
{
lean_dec(v_impl_4015_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4063_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v_size_4032_; lean_object* v_k_4033_; lean_object* v_v_4034_; lean_object* v_l_4035_; lean_object* v_r_4036_; lean_object* v_size_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; uint8_t v___x_4040_; 
v_size_4032_ = lean_ctor_get(v_l_4021_, 0);
v_k_4033_ = lean_ctor_get(v_l_4021_, 1);
v_v_4034_ = lean_ctor_get(v_l_4021_, 2);
v_l_4035_ = lean_ctor_get(v_l_4021_, 3);
v_r_4036_ = lean_ctor_get(v_l_4021_, 4);
v_size_4037_ = lean_ctor_get(v_r_4022_, 0);
v___x_4038_ = lean_unsigned_to_nat(2u);
v___x_4039_ = lean_nat_mul(v___x_4038_, v_size_4037_);
v___x_4040_ = lean_nat_dec_lt(v_size_4032_, v___x_4039_);
lean_dec(v___x_4039_);
if (v___x_4040_ == 0)
{
lean_object* v___x_4041_; lean_object* v___x_4042_; 
lean_inc(v_size_4037_);
lean_inc(v_r_4036_);
lean_inc(v_l_4035_);
lean_inc(v_v_4034_);
lean_inc(v_k_4033_);
lean_del_object(v___x_4030_);
lean_dec(v_l_4021_);
v___x_4041_ = lean_nat_add(v___x_4016_, v_size_4017_);
v___x_4042_ = lean_nat_add(v___x_4041_, v_size_4018_);
lean_dec(v_size_4018_);
if (lean_obj_tag(v_l_4035_) == 0)
{
lean_object* v_size_4043_; 
v_size_4043_ = lean_ctor_get(v_l_4035_, 0);
lean_inc(v_size_4043_);
v___y_3895_ = v_l_4035_;
v___y_3896_ = v_r_4036_;
v___y_3897_ = v_r_4022_;
v___y_3898_ = v___x_4016_;
v___y_3899_ = v_k_4019_;
v___y_3900_ = v_k_4033_;
v___y_3901_ = v___x_4042_;
v___y_3902_ = v_v_4034_;
v___y_3903_ = v_size_4037_;
v___y_3904_ = v_v_4020_;
v___y_3905_ = v___x_4041_;
v___y_3906_ = v_size_4043_;
goto v___jp_3894_;
}
else
{
lean_object* v___x_4044_; 
v___x_4044_ = lean_unsigned_to_nat(0u);
v___y_3895_ = v_l_4035_;
v___y_3896_ = v_r_4036_;
v___y_3897_ = v_r_4022_;
v___y_3898_ = v___x_4016_;
v___y_3899_ = v_k_4019_;
v___y_3900_ = v_k_4033_;
v___y_3901_ = v___x_4042_;
v___y_3902_ = v_v_4034_;
v___y_3903_ = v_size_4037_;
v___y_3904_ = v_v_4020_;
v___y_3905_ = v___x_4041_;
v___y_3906_ = v___x_4044_;
goto v___jp_3894_;
}
}
else
{
lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4049_; 
v___x_4045_ = lean_nat_add(v___x_4016_, v_size_4017_);
v___x_4046_ = lean_nat_add(v___x_4045_, v_size_4018_);
lean_dec(v_size_4018_);
v___x_4047_ = lean_nat_add(v___x_4045_, v_size_4032_);
lean_dec(v___x_4045_);
lean_inc_ref(v_l_3858_);
if (v_isShared_4031_ == 0)
{
lean_ctor_set(v___x_4030_, 4, v_l_4021_);
lean_ctor_set(v___x_4030_, 3, v_l_3858_);
lean_ctor_set(v___x_4030_, 2, v_v_3857_);
lean_ctor_set(v___x_4030_, 1, v_k_3856_);
lean_ctor_set(v___x_4030_, 0, v___x_4047_);
v___x_4049_ = v___x_4030_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v___x_4047_);
lean_ctor_set(v_reuseFailAlloc_4062_, 1, v_k_3856_);
lean_ctor_set(v_reuseFailAlloc_4062_, 2, v_v_3857_);
lean_ctor_set(v_reuseFailAlloc_4062_, 3, v_l_3858_);
lean_ctor_set(v_reuseFailAlloc_4062_, 4, v_l_4021_);
v___x_4049_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4056_; 
v_isSharedCheck_4056_ = !lean_is_exclusive(v_l_3858_);
if (v_isSharedCheck_4056_ == 0)
{
lean_object* v_unused_4057_; lean_object* v_unused_4058_; lean_object* v_unused_4059_; lean_object* v_unused_4060_; lean_object* v_unused_4061_; 
v_unused_4057_ = lean_ctor_get(v_l_3858_, 4);
lean_dec(v_unused_4057_);
v_unused_4058_ = lean_ctor_get(v_l_3858_, 3);
lean_dec(v_unused_4058_);
v_unused_4059_ = lean_ctor_get(v_l_3858_, 2);
lean_dec(v_unused_4059_);
v_unused_4060_ = lean_ctor_get(v_l_3858_, 1);
lean_dec(v_unused_4060_);
v_unused_4061_ = lean_ctor_get(v_l_3858_, 0);
lean_dec(v_unused_4061_);
v___x_4051_ = v_l_3858_;
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
else
{
lean_dec(v_l_3858_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v___x_4054_; 
if (v_isShared_4052_ == 0)
{
lean_ctor_set(v___x_4051_, 4, v_r_4022_);
lean_ctor_set(v___x_4051_, 3, v___x_4049_);
lean_ctor_set(v___x_4051_, 2, v_v_4020_);
lean_ctor_set(v___x_4051_, 1, v_k_4019_);
lean_ctor_set(v___x_4051_, 0, v___x_4046_);
v___x_4054_ = v___x_4051_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v___x_4046_);
lean_ctor_set(v_reuseFailAlloc_4055_, 1, v_k_4019_);
lean_ctor_set(v_reuseFailAlloc_4055_, 2, v_v_4020_);
lean_ctor_set(v_reuseFailAlloc_4055_, 3, v___x_4049_);
lean_ctor_set(v_reuseFailAlloc_4055_, 4, v_r_4022_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4069_; 
v_l_4069_ = lean_ctor_get(v_impl_4015_, 3);
lean_inc(v_l_4069_);
if (lean_obj_tag(v_l_4069_) == 0)
{
lean_object* v_r_4070_; lean_object* v_k_4071_; lean_object* v_v_4072_; lean_object* v___x_4074_; uint8_t v_isShared_4075_; uint8_t v_isSharedCheck_4093_; 
v_r_4070_ = lean_ctor_get(v_impl_4015_, 4);
v_k_4071_ = lean_ctor_get(v_impl_4015_, 1);
v_v_4072_ = lean_ctor_get(v_impl_4015_, 2);
v_isSharedCheck_4093_ = !lean_is_exclusive(v_impl_4015_);
if (v_isSharedCheck_4093_ == 0)
{
lean_object* v_unused_4094_; lean_object* v_unused_4095_; 
v_unused_4094_ = lean_ctor_get(v_impl_4015_, 3);
lean_dec(v_unused_4094_);
v_unused_4095_ = lean_ctor_get(v_impl_4015_, 0);
lean_dec(v_unused_4095_);
v___x_4074_ = v_impl_4015_;
v_isShared_4075_ = v_isSharedCheck_4093_;
goto v_resetjp_4073_;
}
else
{
lean_inc(v_r_4070_);
lean_inc(v_v_4072_);
lean_inc(v_k_4071_);
lean_dec(v_impl_4015_);
v___x_4074_ = lean_box(0);
v_isShared_4075_ = v_isSharedCheck_4093_;
goto v_resetjp_4073_;
}
v_resetjp_4073_:
{
lean_object* v_k_4076_; lean_object* v_v_4077_; lean_object* v___x_4079_; uint8_t v_isShared_4080_; uint8_t v_isSharedCheck_4089_; 
v_k_4076_ = lean_ctor_get(v_l_4069_, 1);
v_v_4077_ = lean_ctor_get(v_l_4069_, 2);
v_isSharedCheck_4089_ = !lean_is_exclusive(v_l_4069_);
if (v_isSharedCheck_4089_ == 0)
{
lean_object* v_unused_4090_; lean_object* v_unused_4091_; lean_object* v_unused_4092_; 
v_unused_4090_ = lean_ctor_get(v_l_4069_, 4);
lean_dec(v_unused_4090_);
v_unused_4091_ = lean_ctor_get(v_l_4069_, 3);
lean_dec(v_unused_4091_);
v_unused_4092_ = lean_ctor_get(v_l_4069_, 0);
lean_dec(v_unused_4092_);
v___x_4079_ = v_l_4069_;
v_isShared_4080_ = v_isSharedCheck_4089_;
goto v_resetjp_4078_;
}
else
{
lean_inc(v_v_4077_);
lean_inc(v_k_4076_);
lean_dec(v_l_4069_);
v___x_4079_ = lean_box(0);
v_isShared_4080_ = v_isSharedCheck_4089_;
goto v_resetjp_4078_;
}
v_resetjp_4078_:
{
lean_object* v___x_4081_; lean_object* v___x_4083_; 
v___x_4081_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_4070_, 2);
if (v_isShared_4080_ == 0)
{
lean_ctor_set(v___x_4079_, 4, v_r_4070_);
lean_ctor_set(v___x_4079_, 3, v_r_4070_);
lean_ctor_set(v___x_4079_, 2, v_v_3857_);
lean_ctor_set(v___x_4079_, 1, v_k_3856_);
lean_ctor_set(v___x_4079_, 0, v___x_4016_);
v___x_4083_ = v___x_4079_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v___x_4016_);
lean_ctor_set(v_reuseFailAlloc_4088_, 1, v_k_3856_);
lean_ctor_set(v_reuseFailAlloc_4088_, 2, v_v_3857_);
lean_ctor_set(v_reuseFailAlloc_4088_, 3, v_r_4070_);
lean_ctor_set(v_reuseFailAlloc_4088_, 4, v_r_4070_);
v___x_4083_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
lean_object* v___x_4085_; 
lean_inc(v_r_4070_);
if (v_isShared_4075_ == 0)
{
lean_ctor_set(v___x_4074_, 3, v_r_4070_);
lean_ctor_set(v___x_4074_, 0, v___x_4016_);
v___x_4085_ = v___x_4074_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v___x_4016_);
lean_ctor_set(v_reuseFailAlloc_4087_, 1, v_k_4071_);
lean_ctor_set(v_reuseFailAlloc_4087_, 2, v_v_4072_);
lean_ctor_set(v_reuseFailAlloc_4087_, 3, v_r_4070_);
lean_ctor_set(v_reuseFailAlloc_4087_, 4, v_r_4070_);
v___x_4085_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4084_;
}
v_reusejp_4084_:
{
lean_object* v___x_4086_; 
v___x_4086_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4086_, 0, v___x_4081_);
lean_ctor_set(v___x_4086_, 1, v_k_4076_);
lean_ctor_set(v___x_4086_, 2, v_v_4077_);
lean_ctor_set(v___x_4086_, 3, v___x_4083_);
lean_ctor_set(v___x_4086_, 4, v___x_4085_);
return v___x_4086_;
}
}
}
}
}
else
{
lean_object* v_r_4096_; 
v_r_4096_ = lean_ctor_get(v_impl_4015_, 4);
lean_inc(v_r_4096_);
if (lean_obj_tag(v_r_4096_) == 0)
{
lean_object* v_k_4097_; lean_object* v_v_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4107_; 
v_k_4097_ = lean_ctor_get(v_impl_4015_, 1);
v_v_4098_ = lean_ctor_get(v_impl_4015_, 2);
v_isSharedCheck_4107_ = !lean_is_exclusive(v_impl_4015_);
if (v_isSharedCheck_4107_ == 0)
{
lean_object* v_unused_4108_; lean_object* v_unused_4109_; lean_object* v_unused_4110_; 
v_unused_4108_ = lean_ctor_get(v_impl_4015_, 4);
lean_dec(v_unused_4108_);
v_unused_4109_ = lean_ctor_get(v_impl_4015_, 3);
lean_dec(v_unused_4109_);
v_unused_4110_ = lean_ctor_get(v_impl_4015_, 0);
lean_dec(v_unused_4110_);
v___x_4100_ = v_impl_4015_;
v_isShared_4101_ = v_isSharedCheck_4107_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_v_4098_);
lean_inc(v_k_4097_);
lean_dec(v_impl_4015_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4107_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
lean_object* v___x_4102_; lean_object* v___x_4104_; 
v___x_4102_ = lean_unsigned_to_nat(3u);
if (v_isShared_4101_ == 0)
{
lean_ctor_set(v___x_4100_, 4, v_l_4069_);
lean_ctor_set(v___x_4100_, 2, v_v_3857_);
lean_ctor_set(v___x_4100_, 1, v_k_3856_);
lean_ctor_set(v___x_4100_, 0, v___x_4016_);
v___x_4104_ = v___x_4100_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v___x_4016_);
lean_ctor_set(v_reuseFailAlloc_4106_, 1, v_k_3856_);
lean_ctor_set(v_reuseFailAlloc_4106_, 2, v_v_3857_);
lean_ctor_set(v_reuseFailAlloc_4106_, 3, v_l_4069_);
lean_ctor_set(v_reuseFailAlloc_4106_, 4, v_l_4069_);
v___x_4104_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
lean_object* v___x_4105_; 
v___x_4105_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4105_, 0, v___x_4102_);
lean_ctor_set(v___x_4105_, 1, v_k_4097_);
lean_ctor_set(v___x_4105_, 2, v_v_4098_);
lean_ctor_set(v___x_4105_, 3, v___x_4104_);
lean_ctor_set(v___x_4105_, 4, v_r_4096_);
return v___x_4105_;
}
}
}
else
{
lean_object* v___x_4111_; lean_object* v___x_4112_; 
v___x_4111_ = lean_unsigned_to_nat(2u);
v___x_4112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4112_, 0, v___x_4111_);
lean_ctor_set(v___x_4112_, 1, v_k_3856_);
lean_ctor_set(v___x_4112_, 2, v_v_3857_);
lean_ctor_set(v___x_4112_, 3, v_r_4096_);
lean_ctor_set(v___x_4112_, 4, v_impl_4015_);
return v___x_4112_;
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
lean_object* v___x_4120_; lean_object* v___x_4121_; 
v___x_4120_ = lean_unsigned_to_nat(1u);
v___x_4121_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4121_, 0, v___x_4120_);
lean_ctor_set(v___x_4121_, 1, v_k_3838_);
lean_ctor_set(v___x_4121_, 2, v_v_3839_);
lean_ctor_set(v___x_4121_, 3, v_t_3840_);
lean_ctor_set(v___x_4121_, 4, v_t_3840_);
return v___x_4121_;
}
v___jp_3841_:
{
lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; 
v___x_3852_ = lean_nat_add(v___y_3845_, v___y_3851_);
lean_dec(v___y_3851_);
lean_dec(v___y_3845_);
v___x_3853_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3853_, 0, v___x_3852_);
lean_ctor_set(v___x_3853_, 1, v___y_3846_);
lean_ctor_set(v___x_3853_, 2, v___y_3850_);
lean_ctor_set(v___x_3853_, 3, v___y_3844_);
lean_ctor_set(v___x_3853_, 4, v___y_3843_);
v___x_3854_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3854_, 0, v___y_3848_);
lean_ctor_set(v___x_3854_, 1, v___y_3847_);
lean_ctor_set(v___x_3854_, 2, v___y_3849_);
lean_ctor_set(v___x_3854_, 3, v___y_3842_);
lean_ctor_set(v___x_3854_, 4, v___x_3853_);
return v___x_3854_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(lean_object* v_t_4122_, lean_object* v_k_4123_, lean_object* v_fallback_4124_){
_start:
{
if (lean_obj_tag(v_t_4122_) == 0)
{
lean_object* v_k_4125_; lean_object* v_v_4126_; lean_object* v_l_4127_; lean_object* v_r_4128_; uint8_t v___y_4130_; lean_object* v_fst_4133_; lean_object* v_snd_4134_; lean_object* v_fst_4135_; lean_object* v_snd_4136_; uint8_t v___x_4137_; 
v_k_4125_ = lean_ctor_get(v_t_4122_, 1);
v_v_4126_ = lean_ctor_get(v_t_4122_, 2);
v_l_4127_ = lean_ctor_get(v_t_4122_, 3);
v_r_4128_ = lean_ctor_get(v_t_4122_, 4);
v_fst_4133_ = lean_ctor_get(v_k_4123_, 0);
v_snd_4134_ = lean_ctor_get(v_k_4123_, 1);
v_fst_4135_ = lean_ctor_get(v_k_4125_, 0);
v_snd_4136_ = lean_ctor_get(v_k_4125_, 1);
v___x_4137_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_fst_4133_, v_fst_4135_);
if (v___x_4137_ == 1)
{
uint8_t v___x_4138_; 
v___x_4138_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_snd_4134_, v_snd_4136_);
v___y_4130_ = v___x_4138_;
goto v___jp_4129_;
}
else
{
v___y_4130_ = v___x_4137_;
goto v___jp_4129_;
}
v___jp_4129_:
{
switch(v___y_4130_)
{
case 0:
{
v_t_4122_ = v_l_4127_;
goto _start;
}
case 1:
{
lean_inc(v_v_4126_);
return v_v_4126_;
}
default: 
{
v_t_4122_ = v_r_4128_;
goto _start;
}
}
}
}
else
{
lean_inc(v_fallback_4124_);
return v_fallback_4124_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg___boxed(lean_object* v_t_4139_, lean_object* v_k_4140_, lean_object* v_fallback_4141_){
_start:
{
lean_object* v_res_4142_; 
v_res_4142_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_t_4139_, v_k_4140_, v_fallback_4141_);
lean_dec(v_fallback_4141_);
lean_dec_ref(v_k_4140_);
lean_dec(v_t_4139_);
return v_res_4142_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(lean_object* v___x_4143_, lean_object* v_as_4144_, size_t v_sz_4145_, size_t v_i_4146_, lean_object* v_b_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_){
_start:
{
uint8_t v___x_4151_; 
v___x_4151_ = lean_usize_dec_lt(v_i_4146_, v_sz_4145_);
if (v___x_4151_ == 0)
{
lean_object* v___x_4152_; 
lean_dec(v___x_4143_);
v___x_4152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4152_, 0, v_b_4147_);
return v___x_4152_;
}
else
{
lean_object* v_a_4153_; lean_object* v_fst_4154_; lean_object* v___x_4156_; uint8_t v_isShared_4157_; uint8_t v_isSharedCheck_4182_; 
v_a_4153_ = lean_array_uget(v_as_4144_, v_i_4146_);
v_fst_4154_ = lean_ctor_get(v_a_4153_, 0);
v_isSharedCheck_4182_ = !lean_is_exclusive(v_a_4153_);
if (v_isSharedCheck_4182_ == 0)
{
lean_object* v_unused_4183_; 
v_unused_4183_ = lean_ctor_get(v_a_4153_, 1);
lean_dec(v_unused_4183_);
v___x_4156_ = v_a_4153_;
v_isShared_4157_ = v_isSharedCheck_4182_;
goto v_resetjp_4155_;
}
else
{
lean_inc(v_fst_4154_);
lean_dec(v_a_4153_);
v___x_4156_ = lean_box(0);
v_isShared_4157_ = v_isSharedCheck_4182_;
goto v_resetjp_4155_;
}
v_resetjp_4155_:
{
lean_object* v___x_4158_; lean_object* v___x_4159_; 
v___x_4158_ = lean_unsigned_to_nat(0u);
lean_inc(v_fst_4154_);
v___x_4159_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_fst_4154_, v___y_4148_, v___y_4149_);
if (lean_obj_tag(v___x_4159_) == 0)
{
lean_object* v_a_4160_; lean_object* v___y_4162_; 
v_a_4160_ = lean_ctor_get(v___x_4159_, 0);
lean_inc(v_a_4160_);
lean_dec_ref_known(v___x_4159_, 1);
if (lean_obj_tag(v_a_4160_) == 0)
{
lean_inc(v___x_4143_);
v___y_4162_ = v___x_4143_;
goto v___jp_4161_;
}
else
{
lean_object* v_val_4173_; 
v_val_4173_ = lean_ctor_get(v_a_4160_, 0);
lean_inc(v_val_4173_);
lean_dec_ref_known(v_a_4160_, 1);
v___y_4162_ = v_val_4173_;
goto v___jp_4161_;
}
v___jp_4161_:
{
lean_object* v___x_4164_; 
if (v_isShared_4157_ == 0)
{
lean_ctor_set(v___x_4156_, 1, v_fst_4154_);
lean_ctor_set(v___x_4156_, 0, v___y_4162_);
v___x_4164_ = v___x_4156_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v___y_4162_);
lean_ctor_set(v_reuseFailAlloc_4172_, 1, v_fst_4154_);
v___x_4164_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; size_t v___x_4169_; size_t v___x_4170_; 
v___x_4165_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_b_4147_, v___x_4164_, v___x_4158_);
v___x_4166_ = lean_unsigned_to_nat(1u);
v___x_4167_ = lean_nat_add(v___x_4165_, v___x_4166_);
lean_dec(v___x_4165_);
v___x_4168_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v___x_4164_, v___x_4167_, v_b_4147_);
v___x_4169_ = ((size_t)1ULL);
v___x_4170_ = lean_usize_add(v_i_4146_, v___x_4169_);
v_i_4146_ = v___x_4170_;
v_b_4147_ = v___x_4168_;
goto _start;
}
}
}
else
{
lean_object* v_a_4174_; lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4181_; 
lean_del_object(v___x_4156_);
lean_dec(v_fst_4154_);
lean_dec(v_b_4147_);
lean_dec(v___x_4143_);
v_a_4174_ = lean_ctor_get(v___x_4159_, 0);
v_isSharedCheck_4181_ = !lean_is_exclusive(v___x_4159_);
if (v_isSharedCheck_4181_ == 0)
{
v___x_4176_ = v___x_4159_;
v_isShared_4177_ = v_isSharedCheck_4181_;
goto v_resetjp_4175_;
}
else
{
lean_inc(v_a_4174_);
lean_dec(v___x_4159_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4181_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
lean_object* v___x_4179_; 
if (v_isShared_4177_ == 0)
{
v___x_4179_ = v___x_4176_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4180_, 0, v_a_4174_);
v___x_4179_ = v_reuseFailAlloc_4180_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
return v___x_4179_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4143_ = stack[0].m_obj;
lean_object* v_as_4144_ = stack[1].m_obj;
size_t v_sz_4145_ = stack[2].m_num;
size_t v_i_4146_ = stack[3].m_num;
lean_object* v_b_4147_ = stack[4].m_obj;
lean_object* v___y_4148_ = stack[5].m_obj;
lean_object* v___y_4149_ = stack[6].m_obj;
lean_object* v_res_4184_;
v_res_4184_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(v___x_4143_, v_as_4144_, v_sz_4145_, v_i_4146_, v_b_4147_, v___y_4148_, v___y_4149_);
stack->m_obj
 = v_res_4184_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7___boxed(lean_object* v___x_4185_, lean_object* v_as_4186_, lean_object* v_sz_4187_, lean_object* v_i_4188_, lean_object* v_b_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_){
_start:
{
size_t v_sz_boxed_4193_; size_t v_i_boxed_4194_; lean_object* v_res_4195_; 
v_sz_boxed_4193_ = lean_unbox_usize(v_sz_4187_);
lean_dec(v_sz_4187_);
v_i_boxed_4194_ = lean_unbox_usize(v_i_4188_);
lean_dec(v_i_4188_);
v_res_4195_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(v___x_4185_, v_as_4186_, v_sz_boxed_4193_, v_i_boxed_4194_, v_b_4189_, v___y_4190_, v___y_4191_);
lean_dec(v___y_4191_);
lean_dec_ref(v___y_4190_);
lean_dec_ref(v_as_4186_);
return v_res_4195_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(lean_object* v_fst_4196_, lean_object* v_init_4197_, lean_object* v_x_4198_){
_start:
{
if (lean_obj_tag(v_x_4198_) == 0)
{
lean_object* v_k_4200_; lean_object* v_v_4201_; lean_object* v_l_4202_; lean_object* v_r_4203_; uint8_t v___x_4204_; lean_object* v___x_4205_; lean_object* v_a_4206_; lean_object* v_a_4207_; lean_object* v_fst_4208_; lean_object* v_snd_4209_; lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4223_; 
v_k_4200_ = lean_ctor_get(v_x_4198_, 1);
lean_inc(v_k_4200_);
v_v_4201_ = lean_ctor_get(v_x_4198_, 2);
lean_inc(v_v_4201_);
v_l_4202_ = lean_ctor_get(v_x_4198_, 3);
lean_inc(v_l_4202_);
v_r_4203_ = lean_ctor_get(v_x_4198_, 4);
lean_inc(v_r_4203_);
lean_dec_ref_known(v_x_4198_, 5);
v___x_4204_ = 1;
lean_inc_ref(v_fst_4196_);
v___x_4205_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4196_, v_init_4197_, v_l_4202_);
v_a_4206_ = lean_ctor_get(v___x_4205_, 0);
lean_inc(v_a_4206_);
lean_dec_ref(v___x_4205_);
v_a_4207_ = lean_ctor_get(v_a_4206_, 0);
lean_inc(v_a_4207_);
lean_dec(v_a_4206_);
v_fst_4208_ = lean_ctor_get(v_k_4200_, 0);
v_snd_4209_ = lean_ctor_get(v_k_4200_, 1);
v_isSharedCheck_4223_ = !lean_is_exclusive(v_k_4200_);
if (v_isSharedCheck_4223_ == 0)
{
v___x_4211_ = v_k_4200_;
v_isShared_4212_ = v_isSharedCheck_4223_;
goto v_resetjp_4210_;
}
else
{
lean_inc(v_snd_4209_);
lean_inc(v_fst_4208_);
lean_dec(v_k_4200_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4223_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
lean_object* v_optName_4213_; lean_object* v___x_4214_; lean_object* v___x_4216_; 
v_optName_4213_ = lean_ctor_get(v_fst_4196_, 1);
lean_inc(v_optName_4213_);
v___x_4214_ = l_Lean_Name_toString(v_optName_4213_, v___x_4204_);
if (v_isShared_4212_ == 0)
{
lean_ctor_set_tag(v___x_4211_, 1);
v___x_4216_ = v___x_4211_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4222_; 
v_reuseFailAlloc_4222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4222_, 0, v_fst_4208_);
lean_ctor_set(v_reuseFailAlloc_4222_, 1, v_snd_4209_);
v___x_4216_ = v_reuseFailAlloc_4222_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
double v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; 
v___x_4217_ = lean_float_of_nat(v_v_4201_);
v___x_4218_ = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_float(v___x_4218_, 0, v___x_4217_);
v___x_4219_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4219_, 0, v___x_4214_);
lean_ctor_set(v___x_4219_, 1, v___x_4216_);
lean_ctor_set(v___x_4219_, 2, v___x_4218_);
v___x_4220_ = lean_array_push(v_a_4207_, v___x_4219_);
v_init_4197_ = v___x_4220_;
v_x_4198_ = v_r_4203_;
goto _start;
}
}
}
else
{
lean_object* v___x_4224_; lean_object* v___x_4225_; 
lean_dec_ref(v_fst_4196_);
v___x_4224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4224_, 0, v_init_4197_);
v___x_4225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4225_, 0, v___x_4224_);
return v___x_4225_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_4196_ = stack[0].m_obj;
lean_object* v_init_4197_ = stack[1].m_obj;
lean_object* v_x_4198_ = stack[2].m_obj;
lean_object* v_res_4226_;
v_res_4226_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4196_, v_init_4197_, v_x_4198_);
stack->m_obj
 = v_res_4226_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg___boxed(lean_object* v_fst_4227_, lean_object* v_init_4228_, lean_object* v_x_4229_, lean_object* v___y_4230_){
_start:
{
lean_object* v_res_4231_; 
v_res_4231_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4227_, v_init_4228_, v_x_4229_);
return v_res_4231_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(lean_object* v___x_4232_, lean_object* v_as_4233_, size_t v_sz_4234_, size_t v_i_4235_, lean_object* v_b_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_){
_start:
{
lean_object* v_a_4241_; uint8_t v___x_4245_; 
v___x_4245_ = lean_usize_dec_lt(v_i_4235_, v_sz_4234_);
if (v___x_4245_ == 0)
{
lean_object* v___x_4246_; 
lean_dec(v___x_4232_);
v___x_4246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4246_, 0, v_b_4236_);
return v___x_4246_;
}
else
{
lean_object* v_a_4247_; lean_object* v_snd_4248_; lean_object* v_fst_4249_; lean_object* v_size_4250_; lean_object* v_buckets_4251_; lean_object* v___x_4252_; lean_object* v___y_4254_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; uint8_t v___x_4291_; 
v_a_4247_ = lean_array_uget_borrowed(v_as_4233_, v_i_4235_);
v_snd_4248_ = lean_ctor_get(v_a_4247_, 1);
v_fst_4249_ = lean_ctor_get(v_a_4247_, 0);
v_size_4250_ = lean_ctor_get(v_snd_4248_, 0);
v_buckets_4251_ = lean_ctor_get(v_snd_4248_, 1);
v___x_4252_ = lean_box(1);
v___x_4288_ = lean_mk_empty_array_with_capacity(v_size_4250_);
v___x_4289_ = lean_unsigned_to_nat(0u);
v___x_4290_ = lean_array_get_size(v_buckets_4251_);
v___x_4291_ = lean_nat_dec_lt(v___x_4289_, v___x_4290_);
if (v___x_4291_ == 0)
{
v___y_4254_ = v___x_4288_;
goto v___jp_4253_;
}
else
{
size_t v___x_4292_; size_t v___x_4293_; lean_object* v___x_4294_; 
v___x_4292_ = ((size_t)0ULL);
v___x_4293_ = lean_usize_of_nat(v___x_4290_);
v___x_4294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_buckets_4251_, v___x_4292_, v___x_4293_, v___x_4288_);
v___y_4254_ = v___x_4294_;
goto v___jp_4253_;
}
v___jp_4253_:
{
size_t v_sz_4255_; size_t v___x_4256_; lean_object* v___x_4257_; 
v_sz_4255_ = lean_array_size(v___y_4254_);
v___x_4256_ = ((size_t)0ULL);
lean_inc(v___x_4232_);
v___x_4257_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(v___x_4232_, v___y_4254_, v_sz_4255_, v___x_4256_, v___x_4252_, v___y_4237_, v___y_4238_);
lean_dec_ref(v___y_4254_);
if (lean_obj_tag(v___x_4257_) == 0)
{
lean_object* v_a_4258_; lean_object* v___x_4259_; 
v_a_4258_ = lean_ctor_get(v___x_4257_, 0);
lean_inc(v_a_4258_);
lean_dec_ref_known(v___x_4257_, 1);
lean_inc(v_fst_4249_);
v___x_4259_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4249_, v_b_4236_, v_a_4258_);
if (lean_obj_tag(v___x_4259_) == 0)
{
lean_object* v_a_4260_; lean_object* v_a_4261_; 
v_a_4260_ = lean_ctor_get(v___x_4259_, 0);
lean_inc(v_a_4260_);
lean_dec_ref_known(v___x_4259_, 1);
v_a_4261_ = lean_ctor_get(v_a_4260_, 0);
lean_inc(v_a_4261_);
lean_dec(v_a_4260_);
v_a_4241_ = v_a_4261_;
goto v___jp_4240_;
}
else
{
if (lean_obj_tag(v___x_4259_) == 0)
{
lean_object* v_a_4262_; lean_object* v___x_4264_; uint8_t v_isShared_4265_; uint8_t v_isSharedCheck_4271_; 
v_a_4262_ = lean_ctor_get(v___x_4259_, 0);
v_isSharedCheck_4271_ = !lean_is_exclusive(v___x_4259_);
if (v_isSharedCheck_4271_ == 0)
{
v___x_4264_ = v___x_4259_;
v_isShared_4265_ = v_isSharedCheck_4271_;
goto v_resetjp_4263_;
}
else
{
lean_inc(v_a_4262_);
lean_dec(v___x_4259_);
v___x_4264_ = lean_box(0);
v_isShared_4265_ = v_isSharedCheck_4271_;
goto v_resetjp_4263_;
}
v_resetjp_4263_:
{
if (lean_obj_tag(v_a_4262_) == 0)
{
lean_object* v_a_4266_; lean_object* v___x_4268_; 
lean_dec(v___x_4232_);
v_a_4266_ = lean_ctor_get(v_a_4262_, 0);
lean_inc(v_a_4266_);
lean_dec_ref_known(v_a_4262_, 1);
if (v_isShared_4265_ == 0)
{
lean_ctor_set_tag(v___x_4264_, 0);
lean_ctor_set(v___x_4264_, 0, v_a_4266_);
v___x_4268_ = v___x_4264_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4269_; 
v_reuseFailAlloc_4269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4269_, 0, v_a_4266_);
v___x_4268_ = v_reuseFailAlloc_4269_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
return v___x_4268_;
}
}
else
{
lean_object* v_a_4270_; 
lean_del_object(v___x_4264_);
v_a_4270_ = lean_ctor_get(v_a_4262_, 0);
lean_inc(v_a_4270_);
lean_dec_ref_known(v_a_4262_, 1);
v_a_4241_ = v_a_4270_;
goto v___jp_4240_;
}
}
}
else
{
lean_object* v_a_4272_; lean_object* v___x_4274_; uint8_t v_isShared_4275_; uint8_t v_isSharedCheck_4279_; 
lean_dec(v___x_4232_);
v_a_4272_ = lean_ctor_get(v___x_4259_, 0);
v_isSharedCheck_4279_ = !lean_is_exclusive(v___x_4259_);
if (v_isSharedCheck_4279_ == 0)
{
v___x_4274_ = v___x_4259_;
v_isShared_4275_ = v_isSharedCheck_4279_;
goto v_resetjp_4273_;
}
else
{
lean_inc(v_a_4272_);
lean_dec(v___x_4259_);
v___x_4274_ = lean_box(0);
v_isShared_4275_ = v_isSharedCheck_4279_;
goto v_resetjp_4273_;
}
v_resetjp_4273_:
{
lean_object* v___x_4277_; 
if (v_isShared_4275_ == 0)
{
v___x_4277_ = v___x_4274_;
goto v_reusejp_4276_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v_a_4272_);
v___x_4277_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4276_;
}
v_reusejp_4276_:
{
return v___x_4277_;
}
}
}
}
}
else
{
lean_object* v_a_4280_; lean_object* v___x_4282_; uint8_t v_isShared_4283_; uint8_t v_isSharedCheck_4287_; 
lean_dec_ref(v_b_4236_);
lean_dec(v___x_4232_);
v_a_4280_ = lean_ctor_get(v___x_4257_, 0);
v_isSharedCheck_4287_ = !lean_is_exclusive(v___x_4257_);
if (v_isSharedCheck_4287_ == 0)
{
v___x_4282_ = v___x_4257_;
v_isShared_4283_ = v_isSharedCheck_4287_;
goto v_resetjp_4281_;
}
else
{
lean_inc(v_a_4280_);
lean_dec(v___x_4257_);
v___x_4282_ = lean_box(0);
v_isShared_4283_ = v_isSharedCheck_4287_;
goto v_resetjp_4281_;
}
v_resetjp_4281_:
{
lean_object* v___x_4285_; 
if (v_isShared_4283_ == 0)
{
v___x_4285_ = v___x_4282_;
goto v_reusejp_4284_;
}
else
{
lean_object* v_reuseFailAlloc_4286_; 
v_reuseFailAlloc_4286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4286_, 0, v_a_4280_);
v___x_4285_ = v_reuseFailAlloc_4286_;
goto v_reusejp_4284_;
}
v_reusejp_4284_:
{
return v___x_4285_;
}
}
}
}
}
v___jp_4240_:
{
size_t v___x_4242_; size_t v___x_4243_; 
v___x_4242_ = ((size_t)1ULL);
v___x_4243_ = lean_usize_add(v_i_4235_, v___x_4242_);
v_i_4235_ = v___x_4243_;
v_b_4236_ = v_a_4241_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4232_ = stack[0].m_obj;
lean_object* v_as_4233_ = stack[1].m_obj;
size_t v_sz_4234_ = stack[2].m_num;
size_t v_i_4235_ = stack[3].m_num;
lean_object* v_b_4236_ = stack[4].m_obj;
lean_object* v___y_4237_ = stack[5].m_obj;
lean_object* v___y_4238_ = stack[6].m_obj;
lean_object* v_res_4295_;
v_res_4295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(v___x_4232_, v_as_4233_, v_sz_4234_, v_i_4235_, v_b_4236_, v___y_4237_, v___y_4238_);
stack->m_obj
 = v_res_4295_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9___boxed(lean_object* v___x_4296_, lean_object* v_as_4297_, lean_object* v_sz_4298_, lean_object* v_i_4299_, lean_object* v_b_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_){
_start:
{
size_t v_sz_boxed_4304_; size_t v_i_boxed_4305_; lean_object* v_res_4306_; 
v_sz_boxed_4304_ = lean_unbox_usize(v_sz_4298_);
lean_dec(v_sz_4298_);
v_i_boxed_4305_ = lean_unbox_usize(v_i_4299_);
lean_dec(v_i_4299_);
v_res_4306_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(v___x_4296_, v_as_4297_, v_sz_boxed_4304_, v_i_boxed_4305_, v_b_4300_, v___y_4301_, v___y_4302_);
lean_dec(v___y_4302_);
lean_dec_ref(v___y_4301_);
lean_dec_ref(v_as_4297_);
return v_res_4306_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5(void){
_start:
{
lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; 
v___x_4313_ = l_Lean_maxRecDepth;
v___x_4314_ = l_Lean_Options_empty;
v___x_4315_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(v___x_4314_, v___x_4313_);
return v___x_4315_;
}
}
lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(lean_object* v_args_4316_, lean_object* v_linterOpts_4317_, lean_object* v_sp_4318_, lean_object* v_env_4319_, lean_object* v_mod_4320_){
_start:
{
lean_object* v_a_4323_; lean_object* v_msg_4327_; lean_object* v_a_4332_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; uint16_t v___x_4357_; uint8_t v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; uint8_t v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v_a_4373_; lean_object* v___y_4377_; uint8_t v___y_4380_; lean_object* v___y_4381_; uint8_t v___y_4382_; lean_object* v___y_4383_; lean_object* v___y_4384_; lean_object* v___y_4385_; lean_object* v___y_4386_; uint8_t v___y_4387_; uint8_t v___y_4457_; lean_object* v___y_4458_; lean_object* v___y_4459_; lean_object* v___y_4460_; lean_object* v___y_4461_; uint8_t v___y_4462_; uint8_t v___y_4472_; lean_object* v___y_4473_; lean_object* v___y_4474_; lean_object* v___y_4475_; lean_object* v___y_4476_; lean_object* v_fileName_4502_; lean_object* v_fileMap_4503_; lean_object* v_currNamespace_4504_; lean_object* v_openDecls_4505_; lean_object* v_initHeartbeats_4506_; lean_object* v_maxHeartbeats_4507_; lean_object* v_quotContext_4508_; lean_object* v_currMacroScope_4509_; lean_object* v_cancelTk_x3f_4510_; lean_object* v_inheritedTraceOptions_4511_; lean_object* v_currRecDepth_4512_; lean_object* v_ref_4513_; uint8_t v_suppressElabErrors_4514_; uint8_t v_isRecordingDeps_4515_; lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; uint8_t v___y_4537_; lean_object* v_env_4558_; uint8_t v___x_4559_; uint8_t v___x_4560_; 
v___x_4346_ = l_Lean_Name_getRoot(v_mod_4320_);
v___x_4347_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_4348_ = l_Lean_instInhabitedFileMap_default;
v___x_4349_ = l_Lean_Options_empty;
v___x_4350_ = lean_box(0);
v___x_4351_ = lean_box(0);
v___x_4352_ = lean_unsigned_to_nat(0u);
v___x_4353_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5);
v___x_4354_ = l_Lean_firstFrontendMacroScope;
v___x_4355_ = lean_box(0);
v___x_4356_ = lean_box(0);
v___x_4357_ = lean_uint16_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_4358_ = 0;
v___x_4359_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7);
v___x_4360_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10));
v___x_4361_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11));
v___x_4362_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14);
v___x_4363_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_4364_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___closed__0));
v___x_4365_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18);
v___x_4366_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_4367_ = 1;
v___x_4368_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
v___x_4369_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4369_, 0, v_env_4319_);
lean_ctor_set(v___x_4369_, 1, v___x_4359_);
lean_ctor_set(v___x_4369_, 2, v___x_4360_);
lean_ctor_set(v___x_4369_, 3, v___x_4361_);
lean_ctor_set(v___x_4369_, 4, v___x_4362_);
lean_ctor_set(v___x_4369_, 5, v___x_4363_);
lean_ctor_set(v___x_4369_, 6, v___x_4365_);
lean_ctor_set(v___x_4369_, 7, v___x_4366_);
lean_ctor_set(v___x_4369_, 8, v___x_4368_);
lean_ctor_set(v___x_4369_, 9, v___x_4364_);
v___x_4370_ = lean_io_get_num_heartbeats();
v___x_4371_ = lean_st_mk_ref(v___x_4369_);
v___x_4533_ = l_Lean_inheritedTraceOptions;
v___x_4534_ = lean_st_ref_get(v___x_4533_);
v___x_4535_ = lean_st_ref_get(v___x_4371_);
v_env_4558_ = lean_ctor_get(v___x_4535_, 0);
lean_inc_ref(v_env_4558_);
lean_dec(v___x_4535_);
v___x_4559_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4558_);
lean_dec_ref(v_env_4558_);
v___x_4560_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22);
if (v___x_4560_ == 0)
{
if (v___x_4559_ == 0)
{
v___y_4537_ = v___x_4367_;
goto v___jp_4536_;
}
else
{
v_fileName_4502_ = v___x_4347_;
v_fileMap_4503_ = v___x_4348_;
v_currNamespace_4504_ = v___x_4350_;
v_openDecls_4505_ = v___x_4351_;
v_initHeartbeats_4506_ = v___x_4370_;
v_maxHeartbeats_4507_ = v___x_4353_;
v_quotContext_4508_ = v___x_4350_;
v_currMacroScope_4509_ = v___x_4354_;
v_cancelTk_x3f_4510_ = v___x_4355_;
v_inheritedTraceOptions_4511_ = v___x_4534_;
v_currRecDepth_4512_ = v___x_4352_;
v_ref_4513_ = v___x_4356_;
v_suppressElabErrors_4514_ = v___x_4358_;
v_isRecordingDeps_4515_ = v___x_4358_;
goto v___jp_4501_;
}
}
else
{
if (v___x_4559_ == 0)
{
v_fileName_4502_ = v___x_4347_;
v_fileMap_4503_ = v___x_4348_;
v_currNamespace_4504_ = v___x_4350_;
v_openDecls_4505_ = v___x_4351_;
v_initHeartbeats_4506_ = v___x_4370_;
v_maxHeartbeats_4507_ = v___x_4353_;
v_quotContext_4508_ = v___x_4350_;
v_currMacroScope_4509_ = v___x_4354_;
v_cancelTk_x3f_4510_ = v___x_4355_;
v_inheritedTraceOptions_4511_ = v___x_4534_;
v_currRecDepth_4512_ = v___x_4352_;
v_ref_4513_ = v___x_4356_;
v_suppressElabErrors_4514_ = v___x_4358_;
v_isRecordingDeps_4515_ = v___x_4358_;
goto v___jp_4501_;
}
else
{
v___y_4537_ = v___x_4358_;
goto v___jp_4536_;
}
}
v___jp_4322_:
{
lean_object* v___x_4324_; lean_object* v___x_4325_; 
v___x_4324_ = lean_mk_io_user_error(v_a_4323_);
v___x_4325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4325_, 0, v___x_4324_);
return v___x_4325_;
}
v___jp_4326_:
{
lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; 
v___x_4328_ = l_Lean_MessageData_toString(v_msg_4327_);
v___x_4329_ = lean_mk_io_user_error(v___x_4328_);
v___x_4330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4330_, 0, v___x_4329_);
return v___x_4330_;
}
v___jp_4331_:
{
if (lean_obj_tag(v_a_4332_) == 0)
{
lean_object* v_msg_4333_; 
v_msg_4333_ = lean_ctor_get(v_a_4332_, 1);
lean_inc_ref(v_msg_4333_);
lean_dec_ref_known(v_a_4332_, 2);
v_msg_4327_ = v_msg_4333_;
goto v___jp_4326_;
}
else
{
lean_object* v_id_4334_; lean_object* v___x_4335_; 
v_id_4334_ = lean_ctor_get(v_a_4332_, 0);
lean_inc(v_id_4334_);
lean_dec_ref_known(v_a_4332_, 2);
v___x_4335_ = l_Lean_InternalExceptionId_getName(v_id_4334_);
if (lean_obj_tag(v___x_4335_) == 0)
{
lean_object* v_a_4336_; lean_object* v___x_4337_; uint8_t v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; 
lean_dec(v_id_4334_);
v_a_4336_ = lean_ctor_get(v___x_4335_, 0);
lean_inc(v_a_4336_);
lean_dec_ref_known(v___x_4335_, 1);
v___x_4337_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_4338_ = 1;
v___x_4339_ = l_Lean_Name_toString(v_a_4336_, v___x_4338_);
v___x_4340_ = lean_string_append(v___x_4337_, v___x_4339_);
lean_dec_ref(v___x_4339_);
v_a_4323_ = v___x_4340_;
goto v___jp_4322_;
}
else
{
lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; 
lean_dec_ref_known(v___x_4335_, 1);
v___x_4341_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_4342_ = l_Nat_reprFast(v_id_4334_);
v___x_4343_ = lean_string_append(v___x_4341_, v___x_4342_);
lean_dec_ref(v___x_4342_);
v___x_4344_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_4345_ = lean_string_append(v___x_4343_, v___x_4344_);
v_a_4323_ = v___x_4345_;
goto v___jp_4322_;
}
}
}
v___jp_4372_:
{
lean_object* v___x_4374_; lean_object* v___x_4375_; 
v___x_4374_ = lean_st_ref_get(v___x_4371_);
lean_dec(v___x_4371_);
lean_dec(v___x_4374_);
v___x_4375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4375_, 0, v_a_4373_);
return v___x_4375_;
}
v___jp_4376_:
{
lean_object* v_a_4378_; 
v_a_4378_ = lean_ctor_get(v___y_4377_, 0);
lean_inc(v_a_4378_);
lean_dec_ref(v___y_4377_);
v_a_4373_ = v_a_4378_;
goto v___jp_4372_;
}
v___jp_4379_:
{
switch(v___y_4380_)
{
case 0:
{
lean_dec(v_sp_4318_);
if (v___y_4387_ == 0)
{
lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; 
lean_dec_ref(v___y_4385_);
lean_dec_ref(v___y_4383_);
lean_dec_ref(v___y_4381_);
v___x_4388_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__0));
v___x_4389_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4320_, v___x_4367_);
v___x_4390_ = lean_string_append(v___x_4388_, v___x_4389_);
lean_dec_ref(v___x_4389_);
v___x_4391_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__1));
v___x_4392_ = lean_string_append(v___x_4390_, v___x_4391_);
v___x_4393_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_4392_);
if (lean_obj_tag(v___x_4393_) == 0)
{
lean_object* v_a_4394_; lean_object* v___x_4395_; 
v_a_4394_ = lean_ctor_get(v___x_4393_, 0);
lean_inc(v_a_4394_);
lean_dec_ref_known(v___x_4393_, 1);
v___x_4395_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_4387_, v_a_4394_, v___y_4386_, v___y_4384_);
lean_dec(v___y_4384_);
lean_dec_ref(v___y_4386_);
v___y_4377_ = v___x_4395_;
goto v___jp_4376_;
}
else
{
lean_object* v_a_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4405_; 
lean_dec_ref(v___y_4386_);
lean_dec(v___y_4384_);
lean_dec(v___x_4371_);
v_a_4396_ = lean_ctor_get(v___x_4393_, 0);
v_isSharedCheck_4405_ = !lean_is_exclusive(v___x_4393_);
if (v_isSharedCheck_4405_ == 0)
{
v___x_4398_ = v___x_4393_;
v_isShared_4399_ = v_isSharedCheck_4405_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_a_4396_);
lean_dec(v___x_4393_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4405_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v___x_4400_; lean_object* v___x_4402_; 
v___x_4400_ = lean_io_error_to_string(v_a_4396_);
if (v_isShared_4399_ == 0)
{
lean_ctor_set_tag(v___x_4398_, 3);
lean_ctor_set(v___x_4398_, 0, v___x_4400_);
v___x_4402_ = v___x_4398_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v___x_4400_);
v___x_4402_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
lean_object* v___x_4403_; 
v___x_4403_ = l_Lean_MessageData_ofFormat(v___x_4402_);
v_msg_4327_ = v___x_4403_;
goto v___jp_4326_;
}
}
}
}
else
{
lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; 
v___x_4406_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__2));
v___x_4407_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4320_, v___y_4387_);
v___x_4408_ = lean_string_append(v___x_4406_, v___x_4407_);
lean_dec_ref(v___x_4407_);
v___x_4409_ = lean_array_get_size(v___y_4385_);
lean_dec_ref(v___y_4385_);
v___x_4410_ = l_Lean_Linter_EnvLinter_formatLinterResults(v___y_4383_, v___y_4381_, v___x_4367_, v___x_4408_, v___x_4409_, v___x_4367_, v___y_4386_, v___y_4384_);
lean_dec_ref(v___y_4381_);
if (lean_obj_tag(v___x_4410_) == 0)
{
lean_object* v_a_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; 
v_a_4411_ = lean_ctor_get(v___x_4410_, 0);
lean_inc(v_a_4411_);
lean_dec_ref_known(v___x_4410_, 1);
v___x_4412_ = l_Lean_MessageData_toString(v_a_4411_);
v___x_4413_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_4412_);
if (lean_obj_tag(v___x_4413_) == 0)
{
lean_object* v_a_4414_; lean_object* v___x_4415_; 
v_a_4414_ = lean_ctor_get(v___x_4413_, 0);
lean_inc(v_a_4414_);
lean_dec_ref_known(v___x_4413_, 1);
v___x_4415_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_4387_, v_a_4414_, v___y_4386_, v___y_4384_);
lean_dec(v___y_4384_);
lean_dec_ref(v___y_4386_);
v___y_4377_ = v___x_4415_;
goto v___jp_4376_;
}
else
{
lean_object* v_a_4416_; lean_object* v___x_4418_; uint8_t v_isShared_4419_; uint8_t v_isSharedCheck_4425_; 
lean_dec_ref(v___y_4386_);
lean_dec(v___y_4384_);
lean_dec(v___x_4371_);
v_a_4416_ = lean_ctor_get(v___x_4413_, 0);
v_isSharedCheck_4425_ = !lean_is_exclusive(v___x_4413_);
if (v_isSharedCheck_4425_ == 0)
{
v___x_4418_ = v___x_4413_;
v_isShared_4419_ = v_isSharedCheck_4425_;
goto v_resetjp_4417_;
}
else
{
lean_inc(v_a_4416_);
lean_dec(v___x_4413_);
v___x_4418_ = lean_box(0);
v_isShared_4419_ = v_isSharedCheck_4425_;
goto v_resetjp_4417_;
}
v_resetjp_4417_:
{
lean_object* v___x_4420_; lean_object* v___x_4422_; 
v___x_4420_ = lean_io_error_to_string(v_a_4416_);
if (v_isShared_4419_ == 0)
{
lean_ctor_set_tag(v___x_4418_, 3);
lean_ctor_set(v___x_4418_, 0, v___x_4420_);
v___x_4422_ = v___x_4418_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4424_; 
v_reuseFailAlloc_4424_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4424_, 0, v___x_4420_);
v___x_4422_ = v_reuseFailAlloc_4424_;
goto v_reusejp_4421_;
}
v_reusejp_4421_:
{
lean_object* v___x_4423_; 
v___x_4423_ = l_Lean_MessageData_ofFormat(v___x_4422_);
v_msg_4327_ = v___x_4423_;
goto v___jp_4326_;
}
}
}
}
else
{
lean_object* v_a_4426_; 
lean_dec_ref(v___y_4386_);
lean_dec(v___y_4384_);
lean_dec(v___x_4371_);
v_a_4426_ = lean_ctor_get(v___x_4410_, 0);
lean_inc(v_a_4426_);
lean_dec_ref_known(v___x_4410_, 1);
v_a_4332_ = v_a_4426_;
goto v___jp_4331_;
}
}
}
case 1:
{
lean_object* v___x_4427_; lean_object* v_env_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; size_t v_sz_4432_; size_t v___x_4433_; lean_object* v___x_4434_; 
lean_dec_ref(v___y_4385_);
lean_dec_ref(v___y_4381_);
lean_dec(v_mod_4320_);
v___x_4427_ = lean_st_ref_get(v___y_4384_);
v_env_4428_ = lean_ctor_get(v___x_4427_, 0);
lean_inc_ref(v_env_4428_);
lean_dec(v___x_4427_);
v___x_4429_ = l_Lean_Environment_mainModule(v_env_4428_);
lean_dec_ref(v_env_4428_);
v___x_4430_ = lean_box(v___y_4382_);
v___x_4431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4431_, 0, v___x_4364_);
lean_ctor_set(v___x_4431_, 1, v___x_4430_);
v_sz_4432_ = lean_array_size(v___y_4383_);
v___x_4433_ = ((size_t)0ULL);
v___x_4434_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(v_sp_4318_, v___x_4429_, v___y_4383_, v_sz_4432_, v___x_4433_, v___x_4431_, v___y_4386_, v___y_4384_);
lean_dec(v___y_4384_);
lean_dec_ref(v___y_4386_);
lean_dec_ref(v___y_4383_);
if (lean_obj_tag(v___x_4434_) == 0)
{
lean_object* v_a_4435_; lean_object* v_fst_4436_; lean_object* v_snd_4437_; lean_object* v___x_4438_; uint8_t v___x_4439_; 
v_a_4435_ = lean_ctor_get(v___x_4434_, 0);
lean_inc(v_a_4435_);
lean_dec_ref_known(v___x_4434_, 1);
v_fst_4436_ = lean_ctor_get(v_a_4435_, 0);
lean_inc(v_fst_4436_);
v_snd_4437_ = lean_ctor_get(v_a_4435_, 1);
lean_inc(v_snd_4437_);
lean_dec(v_a_4435_);
v___x_4438_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_4438_, 0, v_fst_4436_);
v___x_4439_ = lean_unbox(v_snd_4437_);
lean_dec(v_snd_4437_);
lean_ctor_set_uint8(v___x_4438_, sizeof(void*)*1, v___x_4439_);
v_a_4373_ = v___x_4438_;
goto v___jp_4372_;
}
else
{
lean_object* v_a_4440_; 
lean_dec(v___x_4371_);
v_a_4440_ = lean_ctor_get(v___x_4434_, 0);
lean_inc(v_a_4440_);
lean_dec_ref_known(v___x_4434_, 1);
v_a_4332_ = v_a_4440_;
goto v___jp_4331_;
}
}
default: 
{
lean_object* v___x_4441_; lean_object* v_env_4442_; lean_object* v___x_4443_; size_t v_sz_4444_; size_t v___x_4445_; lean_object* v___x_4446_; 
lean_dec_ref(v___y_4385_);
lean_dec_ref(v___y_4381_);
lean_dec(v_mod_4320_);
lean_dec(v_sp_4318_);
v___x_4441_ = lean_st_ref_get(v___y_4384_);
v_env_4442_ = lean_ctor_get(v___x_4441_, 0);
lean_inc_ref(v_env_4442_);
lean_dec(v___x_4441_);
v___x_4443_ = l_Lean_Environment_mainModule(v_env_4442_);
lean_dec_ref(v_env_4442_);
v_sz_4444_ = lean_array_size(v___y_4383_);
v___x_4445_ = ((size_t)0ULL);
v___x_4446_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(v___x_4443_, v___y_4383_, v_sz_4444_, v___x_4445_, v___x_4364_, v___y_4386_, v___y_4384_);
lean_dec(v___y_4384_);
lean_dec_ref(v___y_4386_);
lean_dec_ref(v___y_4383_);
if (lean_obj_tag(v___x_4446_) == 0)
{
lean_object* v_a_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4454_; 
v_a_4447_ = lean_ctor_get(v___x_4446_, 0);
v_isSharedCheck_4454_ = !lean_is_exclusive(v___x_4446_);
if (v_isSharedCheck_4454_ == 0)
{
v___x_4449_ = v___x_4446_;
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_a_4447_);
lean_dec(v___x_4446_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
lean_object* v___x_4452_; 
if (v_isShared_4450_ == 0)
{
lean_ctor_set_tag(v___x_4449_, 2);
v___x_4452_ = v___x_4449_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v_a_4447_);
v___x_4452_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
v_a_4373_ = v___x_4452_;
goto v___jp_4372_;
}
}
}
else
{
lean_object* v_a_4455_; 
lean_dec(v___x_4371_);
v_a_4455_ = lean_ctor_get(v___x_4446_, 0);
lean_inc(v_a_4455_);
lean_dec_ref_known(v___x_4446_, 1);
v_a_4332_ = v_a_4455_;
goto v___jp_4331_;
}
}
}
}
v___jp_4456_:
{
lean_object* v___x_4463_; 
lean_inc_ref(v___y_4461_);
v___x_4463_ = l_Lean_Linter_EnvLinter_lintCore(v___y_4458_, v___y_4461_, v___y_4460_, v___y_4459_);
if (lean_obj_tag(v___x_4463_) == 0)
{
lean_object* v_a_4464_; lean_object* v___x_4465_; uint8_t v___x_4466_; 
v_a_4464_ = lean_ctor_get(v___x_4463_, 0);
lean_inc(v_a_4464_);
lean_dec_ref_known(v___x_4463_, 1);
v___x_4465_ = lean_array_get_size(v_a_4464_);
v___x_4466_ = lean_nat_dec_lt(v___x_4352_, v___x_4465_);
if (v___x_4466_ == 0)
{
v___y_4380_ = v___y_4457_;
v___y_4381_ = v___y_4458_;
v___y_4382_ = v___y_4462_;
v___y_4383_ = v_a_4464_;
v___y_4384_ = v___y_4459_;
v___y_4385_ = v___y_4461_;
v___y_4386_ = v___y_4460_;
v___y_4387_ = v___x_4466_;
goto v___jp_4379_;
}
else
{
if (v___x_4466_ == 0)
{
v___y_4380_ = v___y_4457_;
v___y_4381_ = v___y_4458_;
v___y_4382_ = v___y_4462_;
v___y_4383_ = v_a_4464_;
v___y_4384_ = v___y_4459_;
v___y_4385_ = v___y_4461_;
v___y_4386_ = v___y_4460_;
v___y_4387_ = v___x_4466_;
goto v___jp_4379_;
}
else
{
size_t v___x_4467_; size_t v___x_4468_; uint8_t v___x_4469_; 
v___x_4467_ = ((size_t)0ULL);
v___x_4468_ = lean_usize_of_nat(v___x_4465_);
v___x_4469_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(v___y_4462_, v_a_4464_, v___x_4467_, v___x_4468_);
v___y_4380_ = v___y_4457_;
v___y_4381_ = v___y_4458_;
v___y_4382_ = v___y_4462_;
v___y_4383_ = v_a_4464_;
v___y_4384_ = v___y_4459_;
v___y_4385_ = v___y_4461_;
v___y_4386_ = v___y_4460_;
v___y_4387_ = v___x_4469_;
goto v___jp_4379_;
}
}
}
else
{
lean_object* v_a_4470_; 
lean_dec_ref(v___y_4461_);
lean_dec_ref(v___y_4460_);
lean_dec(v___y_4459_);
lean_dec_ref(v___y_4458_);
lean_dec(v___x_4371_);
lean_dec(v_mod_4320_);
lean_dec(v_sp_4318_);
v_a_4470_ = lean_ctor_get(v___x_4463_, 0);
lean_inc(v_a_4470_);
lean_dec_ref_known(v___x_4463_, 1);
v_a_4332_ = v_a_4470_;
goto v___jp_4331_;
}
}
v___jp_4471_:
{
lean_object* v___x_4477_; 
v___x_4477_ = l_Lean_Linter_EnvLinter_getEnvLinters(v___y_4476_, v___y_4475_, v___y_4474_);
lean_dec(v___y_4476_);
if (lean_obj_tag(v___x_4477_) == 0)
{
lean_object* v_a_4478_; lean_object* v___x_4479_; uint8_t v___x_4480_; 
v_a_4478_ = lean_ctor_get(v___x_4477_, 0);
lean_inc(v_a_4478_);
lean_dec_ref_known(v___x_4477_, 1);
v___x_4479_ = lean_array_get_size(v_a_4478_);
v___x_4480_ = lean_nat_dec_eq(v___x_4479_, v___x_4352_);
if (v___x_4480_ == 0)
{
v___y_4457_ = v___y_4472_;
v___y_4458_ = v___y_4473_;
v___y_4459_ = v___y_4474_;
v___y_4460_ = v___y_4475_;
v___y_4461_ = v_a_4478_;
v___y_4462_ = v___x_4480_;
goto v___jp_4456_;
}
else
{
uint8_t v___x_4481_; uint8_t v___x_4482_; 
v___x_4481_ = 0;
v___x_4482_ = l_Lake_BuiltinLint_instBEqMode_beq(v___y_4472_, v___x_4481_);
if (v___x_4482_ == 0)
{
v___y_4457_ = v___y_4472_;
v___y_4458_ = v___y_4473_;
v___y_4459_ = v___y_4474_;
v___y_4460_ = v___y_4475_;
v___y_4461_ = v_a_4478_;
v___y_4462_ = v___x_4482_;
goto v___jp_4456_;
}
else
{
lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; 
lean_dec(v_a_4478_);
lean_dec_ref(v___y_4475_);
lean_dec(v___y_4474_);
lean_dec_ref(v___y_4473_);
lean_dec(v_sp_4318_);
v___x_4483_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__3));
v___x_4484_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4320_, v___x_4482_);
v___x_4485_ = lean_string_append(v___x_4483_, v___x_4484_);
lean_dec_ref(v___x_4484_);
v___x_4486_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__1));
v___x_4487_ = lean_string_append(v___x_4485_, v___x_4486_);
v___x_4488_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_4487_);
if (lean_obj_tag(v___x_4488_) == 0)
{
lean_object* v___x_4489_; 
lean_dec_ref_known(v___x_4488_, 1);
v___x_4489_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__4));
v_a_4373_ = v___x_4489_;
goto v___jp_4372_;
}
else
{
lean_object* v_a_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4499_; 
lean_dec(v___x_4371_);
v_a_4490_ = lean_ctor_get(v___x_4488_, 0);
v_isSharedCheck_4499_ = !lean_is_exclusive(v___x_4488_);
if (v_isSharedCheck_4499_ == 0)
{
v___x_4492_ = v___x_4488_;
v_isShared_4493_ = v_isSharedCheck_4499_;
goto v_resetjp_4491_;
}
else
{
lean_inc(v_a_4490_);
lean_dec(v___x_4488_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4499_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
lean_object* v___x_4494_; lean_object* v___x_4496_; 
v___x_4494_ = lean_io_error_to_string(v_a_4490_);
if (v_isShared_4493_ == 0)
{
lean_ctor_set_tag(v___x_4492_, 3);
lean_ctor_set(v___x_4492_, 0, v___x_4494_);
v___x_4496_ = v___x_4492_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v___x_4494_);
v___x_4496_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
lean_object* v___x_4497_; 
v___x_4497_ = l_Lean_MessageData_ofFormat(v___x_4496_);
v_msg_4327_ = v___x_4497_;
goto v___jp_4326_;
}
}
}
}
}
}
else
{
lean_object* v_a_4500_; 
lean_dec_ref(v___y_4475_);
lean_dec(v___y_4474_);
lean_dec_ref(v___y_4473_);
lean_dec(v___x_4371_);
lean_dec(v_mod_4320_);
lean_dec(v_sp_4318_);
v_a_4500_ = lean_ctor_get(v___x_4477_, 0);
lean_inc(v_a_4500_);
lean_dec_ref_known(v___x_4477_, 1);
v_a_4332_ = v_a_4500_;
goto v___jp_4331_;
}
}
v___jp_4501_:
{
lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; 
v___x_4516_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5);
lean_inc(v_currMacroScope_4509_);
lean_inc(v_quotContext_4508_);
lean_inc(v_maxHeartbeats_4507_);
lean_inc(v_openDecls_4505_);
lean_inc(v_currNamespace_4504_);
lean_inc_ref(v_fileMap_4503_);
lean_inc_ref(v_fileName_4502_);
v___x_4517_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4517_, 0, v_fileName_4502_);
lean_ctor_set(v___x_4517_, 1, v_fileMap_4503_);
lean_ctor_set(v___x_4517_, 2, v___x_4349_);
lean_ctor_set(v___x_4517_, 3, v___x_4516_);
lean_ctor_set(v___x_4517_, 4, v_currNamespace_4504_);
lean_ctor_set(v___x_4517_, 5, v_openDecls_4505_);
lean_ctor_set(v___x_4517_, 6, v_initHeartbeats_4506_);
lean_ctor_set(v___x_4517_, 7, v_maxHeartbeats_4507_);
lean_ctor_set(v___x_4517_, 8, v_quotContext_4508_);
lean_ctor_set(v___x_4517_, 9, v_currMacroScope_4509_);
lean_ctor_set(v___x_4517_, 10, v_cancelTk_x3f_4510_);
lean_ctor_set(v___x_4517_, 11, v_inheritedTraceOptions_4511_);
lean_inc(v_ref_4513_);
v___x_4518_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_4518_, 0, v___x_4517_);
lean_ctor_set(v___x_4518_, 1, v_currRecDepth_4512_);
lean_ctor_set(v___x_4518_, 2, v_ref_4513_);
lean_ctor_set_uint16(v___x_4518_, sizeof(void*)*3, v___x_4357_);
lean_ctor_set_uint8(v___x_4518_, sizeof(void*)*3 + 2, v_suppressElabErrors_4514_);
lean_ctor_set_uint8(v___x_4518_, sizeof(void*)*3 + 3, v_isRecordingDeps_4515_);
v___x_4519_ = l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(v___x_4346_, v___x_4371_);
lean_dec(v___x_4346_);
if (lean_obj_tag(v___x_4519_) == 0)
{
uint8_t v_lintOnly_4520_; 
v_lintOnly_4520_ = lean_ctor_get_uint8(v_args_4316_, sizeof(void*)*4);
if (v_lintOnly_4520_ == 0)
{
lean_object* v_a_4521_; uint8_t v_mode_4522_; 
lean_dec_ref(v_linterOpts_4317_);
v_a_4521_ = lean_ctor_get(v___x_4519_, 0);
lean_inc(v_a_4521_);
lean_dec_ref_known(v___x_4519_, 1);
v_mode_4522_ = lean_ctor_get_uint8(v_args_4316_, sizeof(void*)*4 + 1);
lean_inc(v___x_4371_);
v___y_4472_ = v_mode_4522_;
v___y_4473_ = v_a_4521_;
v___y_4474_ = v___x_4371_;
v___y_4475_ = v___x_4518_;
v___y_4476_ = v___x_4355_;
goto v___jp_4471_;
}
else
{
lean_object* v_a_4523_; lean_object* v___x_4525_; uint8_t v_isShared_4526_; uint8_t v_isSharedCheck_4531_; 
v_a_4523_ = lean_ctor_get(v___x_4519_, 0);
v_isSharedCheck_4531_ = !lean_is_exclusive(v___x_4519_);
if (v_isSharedCheck_4531_ == 0)
{
v___x_4525_ = v___x_4519_;
v_isShared_4526_ = v_isSharedCheck_4531_;
goto v_resetjp_4524_;
}
else
{
lean_inc(v_a_4523_);
lean_dec(v___x_4519_);
v___x_4525_ = lean_box(0);
v_isShared_4526_ = v_isSharedCheck_4531_;
goto v_resetjp_4524_;
}
v_resetjp_4524_:
{
uint8_t v_mode_4527_; lean_object* v___x_4529_; 
v_mode_4527_ = lean_ctor_get_uint8(v_args_4316_, sizeof(void*)*4 + 1);
if (v_isShared_4526_ == 0)
{
lean_ctor_set_tag(v___x_4525_, 1);
lean_ctor_set(v___x_4525_, 0, v_linterOpts_4317_);
v___x_4529_ = v___x_4525_;
goto v_reusejp_4528_;
}
else
{
lean_object* v_reuseFailAlloc_4530_; 
v_reuseFailAlloc_4530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4530_, 0, v_linterOpts_4317_);
v___x_4529_ = v_reuseFailAlloc_4530_;
goto v_reusejp_4528_;
}
v_reusejp_4528_:
{
lean_inc(v___x_4371_);
v___y_4472_ = v_mode_4527_;
v___y_4473_ = v_a_4523_;
v___y_4474_ = v___x_4371_;
v___y_4475_ = v___x_4518_;
v___y_4476_ = v___x_4529_;
goto v___jp_4471_;
}
}
}
}
else
{
lean_object* v_a_4532_; 
lean_dec_ref_known(v___x_4518_, 3);
lean_dec(v___x_4371_);
lean_dec(v_mod_4320_);
lean_dec(v_sp_4318_);
lean_dec_ref(v_linterOpts_4317_);
v_a_4532_ = lean_ctor_get(v___x_4519_, 0);
lean_inc(v_a_4532_);
lean_dec_ref_known(v___x_4519_, 1);
v_a_4332_ = v_a_4532_;
goto v___jp_4331_;
}
}
v___jp_4536_:
{
lean_object* v___x_4538_; lean_object* v_env_4539_; lean_object* v_nextMacroScope_4540_; lean_object* v_ngen_4541_; lean_object* v_auxDeclNGen_4542_; lean_object* v_traceState_4543_; lean_object* v_recordedDeps_4544_; lean_object* v_messages_4545_; lean_object* v_infoState_4546_; lean_object* v_snapshotTasks_4547_; lean_object* v___x_4549_; uint8_t v_isShared_4550_; uint8_t v_isSharedCheck_4556_; 
v___x_4538_ = lean_st_ref_take(v___x_4371_);
v_env_4539_ = lean_ctor_get(v___x_4538_, 0);
v_nextMacroScope_4540_ = lean_ctor_get(v___x_4538_, 1);
v_ngen_4541_ = lean_ctor_get(v___x_4538_, 2);
v_auxDeclNGen_4542_ = lean_ctor_get(v___x_4538_, 3);
v_traceState_4543_ = lean_ctor_get(v___x_4538_, 4);
v_recordedDeps_4544_ = lean_ctor_get(v___x_4538_, 6);
v_messages_4545_ = lean_ctor_get(v___x_4538_, 7);
v_infoState_4546_ = lean_ctor_get(v___x_4538_, 8);
v_snapshotTasks_4547_ = lean_ctor_get(v___x_4538_, 9);
v_isSharedCheck_4556_ = !lean_is_exclusive(v___x_4538_);
if (v_isSharedCheck_4556_ == 0)
{
lean_object* v_unused_4557_; 
v_unused_4557_ = lean_ctor_get(v___x_4538_, 5);
lean_dec(v_unused_4557_);
v___x_4549_ = v___x_4538_;
v_isShared_4550_ = v_isSharedCheck_4556_;
goto v_resetjp_4548_;
}
else
{
lean_inc(v_snapshotTasks_4547_);
lean_inc(v_infoState_4546_);
lean_inc(v_messages_4545_);
lean_inc(v_recordedDeps_4544_);
lean_inc(v_traceState_4543_);
lean_inc(v_auxDeclNGen_4542_);
lean_inc(v_ngen_4541_);
lean_inc(v_nextMacroScope_4540_);
lean_inc(v_env_4539_);
lean_dec(v___x_4538_);
v___x_4549_ = lean_box(0);
v_isShared_4550_ = v_isSharedCheck_4556_;
goto v_resetjp_4548_;
}
v_resetjp_4548_:
{
lean_object* v___x_4551_; lean_object* v___x_4553_; 
v___x_4551_ = l_Lean_Kernel_enableDiag(v_env_4539_, v___y_4537_);
if (v_isShared_4550_ == 0)
{
lean_ctor_set(v___x_4549_, 5, v___x_4363_);
lean_ctor_set(v___x_4549_, 0, v___x_4551_);
v___x_4553_ = v___x_4549_;
goto v_reusejp_4552_;
}
else
{
lean_object* v_reuseFailAlloc_4555_; 
v_reuseFailAlloc_4555_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4555_, 0, v___x_4551_);
lean_ctor_set(v_reuseFailAlloc_4555_, 1, v_nextMacroScope_4540_);
lean_ctor_set(v_reuseFailAlloc_4555_, 2, v_ngen_4541_);
lean_ctor_set(v_reuseFailAlloc_4555_, 3, v_auxDeclNGen_4542_);
lean_ctor_set(v_reuseFailAlloc_4555_, 4, v_traceState_4543_);
lean_ctor_set(v_reuseFailAlloc_4555_, 5, v___x_4363_);
lean_ctor_set(v_reuseFailAlloc_4555_, 6, v_recordedDeps_4544_);
lean_ctor_set(v_reuseFailAlloc_4555_, 7, v_messages_4545_);
lean_ctor_set(v_reuseFailAlloc_4555_, 8, v_infoState_4546_);
lean_ctor_set(v_reuseFailAlloc_4555_, 9, v_snapshotTasks_4547_);
v___x_4553_ = v_reuseFailAlloc_4555_;
goto v_reusejp_4552_;
}
v_reusejp_4552_:
{
lean_object* v___x_4554_; 
v___x_4554_ = lean_st_ref_put(v___x_4371_, v___x_4553_);
v_fileName_4502_ = v___x_4347_;
v_fileMap_4503_ = v___x_4348_;
v_currNamespace_4504_ = v___x_4350_;
v_openDecls_4505_ = v___x_4351_;
v_initHeartbeats_4506_ = v___x_4370_;
v_maxHeartbeats_4507_ = v___x_4353_;
v_quotContext_4508_ = v___x_4350_;
v_currMacroScope_4509_ = v___x_4354_;
v_cancelTk_x3f_4510_ = v___x_4355_;
v_inheritedTraceOptions_4511_ = v___x_4534_;
v_currRecDepth_4512_ = v___x_4352_;
v_ref_4513_ = v___x_4356_;
v_suppressElabErrors_4514_ = v___x_4358_;
v_isRecordingDeps_4515_ = v___x_4358_;
goto v___jp_4501_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_4316_ = stack[0].m_obj;
lean_object* v_linterOpts_4317_ = stack[1].m_obj;
lean_object* v_sp_4318_ = stack[2].m_obj;
lean_object* v_env_4319_ = stack[3].m_obj;
lean_object* v_mod_4320_ = stack[4].m_obj;
lean_object* v_res_4561_;
v_res_4561_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(v_args_4316_, v_linterOpts_4317_, v_sp_4318_, v_env_4319_, v_mod_4320_);
stack->m_obj
 = v_res_4561_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___boxed(lean_object* v_args_4562_, lean_object* v_linterOpts_4563_, lean_object* v_sp_4564_, lean_object* v_env_4565_, lean_object* v_mod_4566_, lean_object* v_a_4567_){
_start:
{
lean_object* v_res_4568_; 
v_res_4568_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(v_args_4562_, v_linterOpts_4563_, v_sp_4564_, v_env_4565_, v_mod_4566_);
lean_dec_ref(v_args_4562_);
return v_res_4568_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5(lean_object* v_00_u03b4_4569_, lean_object* v_t_4570_, lean_object* v_k_4571_, lean_object* v_fallback_4572_){
_start:
{
lean_object* v___x_4573_; 
v___x_4573_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_t_4570_, v_k_4571_, v_fallback_4572_);
return v___x_4573_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___boxed(lean_object* v_00_u03b4_4574_, lean_object* v_t_4575_, lean_object* v_k_4576_, lean_object* v_fallback_4577_){
_start:
{
lean_object* v_res_4578_; 
v_res_4578_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5(v_00_u03b4_4574_, v_t_4575_, v_k_4576_, v_fallback_4577_);
lean_dec(v_fallback_4577_);
lean_dec_ref(v_k_4576_);
lean_dec(v_t_4575_);
return v_res_4578_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6(lean_object* v_00_u03b2_4579_, lean_object* v_k_4580_, lean_object* v_v_4581_, lean_object* v_t_4582_, lean_object* v_hl_4583_){
_start:
{
lean_object* v___x_4584_; 
v___x_4584_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_4580_, v_v_4581_, v_t_4582_);
return v___x_4584_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8(lean_object* v_fst_4585_, lean_object* v_init_4586_, lean_object* v_x_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_){
_start:
{
lean_object* v___x_4591_; 
v___x_4591_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4585_, v_init_4586_, v_x_4587_);
return v___x_4591_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_4585_ = stack[0].m_obj;
lean_object* v_init_4586_ = stack[1].m_obj;
lean_object* v_x_4587_ = stack[2].m_obj;
lean_object* v___y_4588_ = stack[3].m_obj;
lean_object* v___y_4589_ = stack[4].m_obj;
lean_object* v_res_4592_;
v_res_4592_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8(v_fst_4585_, v_init_4586_, v_x_4587_, v___y_4588_, v___y_4589_);
stack->m_obj
 = v_res_4592_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___boxed(lean_object* v_fst_4593_, lean_object* v_init_4594_, lean_object* v_x_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_){
_start:
{
lean_object* v_res_4599_; 
v_res_4599_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8(v_fst_4593_, v_init_4594_, v_x_4595_, v___y_4596_, v___y_4597_);
lean_dec(v___y_4597_);
lean_dec_ref(v___y_4596_);
return v_res_4599_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4600_, lean_object* v_constName_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_){
_start:
{
lean_object* v___x_4605_; 
v___x_4605_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_4601_, v___y_4602_, v___y_4603_);
return v___x_4605_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_4601_ = stack[1].m_obj;
lean_object* v___y_4602_ = stack[2].m_obj;
lean_object* v___y_4603_ = stack[3].m_obj;
lean_object* v_res_4606_;
v_res_4606_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1(lean_box(0), v_constName_4601_, v___y_4602_, v___y_4603_);
stack->m_obj
 = v_res_4606_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_4607_, lean_object* v_constName_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_){
_start:
{
lean_object* v_res_4612_; 
v_res_4612_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1(v_00_u03b1_4607_, v_constName_4608_, v___y_4609_, v___y_4610_);
lean_dec(v___y_4610_);
lean_dec_ref(v___y_4609_);
return v_res_4612_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12(lean_object* v_00_u03b1_4613_, lean_object* v_ref_4614_, lean_object* v_constName_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_){
_start:
{
lean_object* v___x_4619_; 
v___x_4619_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_4614_, v_constName_4615_, v___y_4616_, v___y_4617_);
return v___x_4619_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_4614_ = stack[1].m_obj;
lean_object* v_constName_4615_ = stack[2].m_obj;
lean_object* v___y_4616_ = stack[3].m_obj;
lean_object* v___y_4617_ = stack[4].m_obj;
lean_object* v_res_4620_;
v_res_4620_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12(lean_box(0), v_ref_4614_, v_constName_4615_, v___y_4616_, v___y_4617_);
stack->m_obj
 = v_res_4620_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___boxed(lean_object* v_00_u03b1_4621_, lean_object* v_ref_4622_, lean_object* v_constName_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_){
_start:
{
lean_object* v_res_4627_; 
v_res_4627_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12(v_00_u03b1_4621_, v_ref_4622_, v_constName_4623_, v___y_4624_, v___y_4625_);
lean_dec(v___y_4625_);
lean_dec_ref(v___y_4624_);
lean_dec(v_ref_4622_);
return v_res_4627_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13(lean_object* v_00_u03b1_4628_, lean_object* v_ref_4629_, lean_object* v_msg_4630_, lean_object* v_declHint_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_){
_start:
{
lean_object* v___x_4635_; 
v___x_4635_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_4629_, v_msg_4630_, v_declHint_4631_, v___y_4632_, v___y_4633_);
return v___x_4635_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_4629_ = stack[1].m_obj;
lean_object* v_msg_4630_ = stack[2].m_obj;
lean_object* v_declHint_4631_ = stack[3].m_obj;
lean_object* v___y_4632_ = stack[4].m_obj;
lean_object* v___y_4633_ = stack[5].m_obj;
lean_object* v_res_4636_;
v_res_4636_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13(lean_box(0), v_ref_4629_, v_msg_4630_, v_declHint_4631_, v___y_4632_, v___y_4633_);
stack->m_obj
 = v_res_4636_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___boxed(lean_object* v_00_u03b1_4637_, lean_object* v_ref_4638_, lean_object* v_msg_4639_, lean_object* v_declHint_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_){
_start:
{
lean_object* v_res_4644_; 
v_res_4644_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13(v_00_u03b1_4637_, v_ref_4638_, v_msg_4639_, v_declHint_4640_, v___y_4641_, v___y_4642_);
lean_dec(v___y_4642_);
lean_dec_ref(v___y_4641_);
lean_dec(v_ref_4638_);
return v_res_4644_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15(lean_object* v_msg_4645_, lean_object* v_declHint_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_){
_start:
{
lean_object* v___x_4650_; 
v___x_4650_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_4645_, v_declHint_4646_, v___y_4648_);
return v___x_4650_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_4645_ = stack[0].m_obj;
lean_object* v_declHint_4646_ = stack[1].m_obj;
lean_object* v___y_4647_ = stack[2].m_obj;
lean_object* v___y_4648_ = stack[3].m_obj;
lean_object* v_res_4651_;
v_res_4651_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15(v_msg_4645_, v_declHint_4646_, v___y_4647_, v___y_4648_);
stack->m_obj
 = v_res_4651_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___boxed(lean_object* v_msg_4652_, lean_object* v_declHint_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_){
_start:
{
lean_object* v_res_4657_; 
v_res_4657_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15(v_msg_4652_, v_declHint_4653_, v___y_4654_, v___y_4655_);
lean_dec(v___y_4655_);
lean_dec_ref(v___y_4654_);
return v_res_4657_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15(lean_object* v_00_u03b1_4658_, lean_object* v_ref_4659_, lean_object* v_msg_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_){
_start:
{
lean_object* v___x_4664_; 
v___x_4664_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_4659_, v_msg_4660_, v___y_4661_, v___y_4662_);
return v___x_4664_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_4659_ = stack[1].m_obj;
lean_object* v_msg_4660_ = stack[2].m_obj;
lean_object* v___y_4661_ = stack[3].m_obj;
lean_object* v___y_4662_ = stack[4].m_obj;
lean_object* v_res_4665_;
v_res_4665_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15(lean_box(0), v_ref_4659_, v_msg_4660_, v___y_4661_, v___y_4662_);
stack->m_obj
 = v_res_4665_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___boxed(lean_object* v_00_u03b1_4666_, lean_object* v_ref_4667_, lean_object* v_msg_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_){
_start:
{
lean_object* v_res_4672_; 
v_res_4672_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15(v_00_u03b1_4666_, v_ref_4667_, v_msg_4668_, v___y_4669_, v___y_4670_);
lean_dec(v___y_4670_);
lean_dec_ref(v___y_4669_);
lean_dec(v_ref_4667_);
return v_res_4672_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17(lean_object* v_00_u03b1_4673_, lean_object* v_msg_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_){
_start:
{
lean_object* v___x_4678_; 
v___x_4678_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_4674_, v___y_4675_, v___y_4676_);
return v___x_4678_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_4674_ = stack[1].m_obj;
lean_object* v___y_4675_ = stack[2].m_obj;
lean_object* v___y_4676_ = stack[3].m_obj;
lean_object* v_res_4679_;
v_res_4679_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17(lean_box(0), v_msg_4674_, v___y_4675_, v___y_4676_);
stack->m_obj
 = v_res_4679_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___boxed(lean_object* v_00_u03b1_4680_, lean_object* v_msg_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_){
_start:
{
lean_object* v_res_4685_; 
v_res_4685_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17(v_00_u03b1_4680_, v_msg_4681_, v___y_4682_, v___y_4683_);
lean_dec(v___y_4683_);
lean_dec_ref(v___y_4682_);
return v_res_4685_;
}
}
lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(lean_object* v_s_4686_){
_start:
{
lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; uint32_t v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; 
v___x_4688_ = l_Std_Format_defWidth;
v___x_4689_ = lean_unsigned_to_nat(0u);
v___x_4690_ = l_Std_Format_pretty(v_s_4686_, v___x_4688_, v___x_4689_, v___x_4689_);
v___x_4691_ = 10;
v___x_4692_ = lean_string_push(v___x_4690_, v___x_4691_);
v___x_4693_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(v___x_4692_);
return v___x_4693_;
}
}
LEAN_EXPORT void l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_4686_ = stack[0].m_obj;
lean_object* v_res_4694_;
v_res_4694_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(v_s_4686_);
stack->m_obj
 = v_res_4694_;
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0___boxed(lean_object* v_s_4695_, lean_object* v_a_4696_){
_start:
{
lean_object* v_res_4697_; 
v_res_4697_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(v_s_4695_);
return v_res_4697_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(lean_object* v_as_4698_, size_t v_sz_4699_, size_t v_i_4700_, lean_object* v_b_4701_, lean_object* v___y_4702_){
_start:
{
uint8_t v___x_4704_; 
v___x_4704_ = lean_usize_dec_lt(v_i_4700_, v_sz_4699_);
if (v___x_4704_ == 0)
{
lean_object* v___x_4705_; 
v___x_4705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4705_, 0, v_b_4701_);
return v___x_4705_;
}
else
{
lean_object* v___x_4706_; lean_object* v_a_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v_ref_4710_; lean_object* v___x_4711_; 
v___x_4706_ = lean_box(0);
v_a_4707_ = lean_array_uget_borrowed(v_as_4698_, v_i_4700_);
v___x_4708_ = lean_box(0);
lean_inc(v_a_4707_);
v___x_4709_ = l_Lean_MessageData_format(v_a_4707_, v___x_4708_);
v_ref_4710_ = lean_ctor_get(v___y_4702_, 2);
v___x_4711_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(v___x_4709_);
if (lean_obj_tag(v___x_4711_) == 0)
{
size_t v___x_4712_; size_t v___x_4713_; 
lean_dec_ref_known(v___x_4711_, 1);
v___x_4712_ = ((size_t)1ULL);
v___x_4713_ = lean_usize_add(v_i_4700_, v___x_4712_);
v_i_4700_ = v___x_4713_;
v_b_4701_ = v___x_4706_;
goto _start;
}
else
{
lean_object* v_a_4715_; lean_object* v___x_4717_; uint8_t v_isShared_4718_; uint8_t v_isSharedCheck_4726_; 
v_a_4715_ = lean_ctor_get(v___x_4711_, 0);
v_isSharedCheck_4726_ = !lean_is_exclusive(v___x_4711_);
if (v_isSharedCheck_4726_ == 0)
{
v___x_4717_ = v___x_4711_;
v_isShared_4718_ = v_isSharedCheck_4726_;
goto v_resetjp_4716_;
}
else
{
lean_inc(v_a_4715_);
lean_dec(v___x_4711_);
v___x_4717_ = lean_box(0);
v_isShared_4718_ = v_isSharedCheck_4726_;
goto v_resetjp_4716_;
}
v_resetjp_4716_:
{
lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4724_; 
v___x_4719_ = lean_io_error_to_string(v_a_4715_);
v___x_4720_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4720_, 0, v___x_4719_);
v___x_4721_ = l_Lean_MessageData_ofFormat(v___x_4720_);
lean_inc(v_ref_4710_);
v___x_4722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4722_, 0, v_ref_4710_);
lean_ctor_set(v___x_4722_, 1, v___x_4721_);
if (v_isShared_4718_ == 0)
{
lean_ctor_set(v___x_4717_, 0, v___x_4722_);
v___x_4724_ = v___x_4717_;
goto v_reusejp_4723_;
}
else
{
lean_object* v_reuseFailAlloc_4725_; 
v_reuseFailAlloc_4725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4725_, 0, v___x_4722_);
v___x_4724_ = v_reuseFailAlloc_4725_;
goto v_reusejp_4723_;
}
v_reusejp_4723_:
{
return v___x_4724_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4698_ = stack[0].m_obj;
size_t v_sz_4699_ = stack[1].m_num;
size_t v_i_4700_ = stack[2].m_num;
lean_object* v_b_4701_ = stack[3].m_obj;
lean_object* v___y_4702_ = stack[4].m_obj;
lean_object* v_res_4727_;
v_res_4727_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(v_as_4698_, v_sz_4699_, v_i_4700_, v_b_4701_, v___y_4702_);
stack->m_obj
 = v_res_4727_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg___boxed(lean_object* v_as_4728_, lean_object* v_sz_4729_, lean_object* v_i_4730_, lean_object* v_b_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_){
_start:
{
size_t v_sz_boxed_4734_; size_t v_i_boxed_4735_; lean_object* v_res_4736_; 
v_sz_boxed_4734_ = lean_unbox_usize(v_sz_4729_);
lean_dec(v_sz_4729_);
v_i_boxed_4735_ = lean_unbox_usize(v_i_4730_);
lean_dec(v_i_4730_);
v_res_4736_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(v_as_4728_, v_sz_boxed_4734_, v_i_boxed_4735_, v_b_4731_, v___y_4732_);
lean_dec_ref(v___y_4732_);
lean_dec_ref(v_as_4728_);
return v_res_4736_;
}
}
lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(lean_object* v_errors_4737_, lean_object* v_entries_4738_, lean_object* v_____r_4739_, uint8_t v_anyFailed_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_){
_start:
{
lean_object* v___x_4744_; size_t v_sz_4745_; size_t v___x_4746_; lean_object* v___x_4747_; 
v___x_4744_ = lean_box(0);
v_sz_4745_ = lean_array_size(v_errors_4737_);
v___x_4746_ = ((size_t)0ULL);
v___x_4747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(v_errors_4737_, v_sz_4745_, v___x_4746_, v___x_4744_, v___y_4741_);
if (lean_obj_tag(v___x_4747_) == 0)
{
lean_object* v___x_4749_; uint8_t v_isShared_4750_; uint8_t v_isSharedCheck_4756_; 
v_isSharedCheck_4756_ = !lean_is_exclusive(v___x_4747_);
if (v_isSharedCheck_4756_ == 0)
{
lean_object* v_unused_4757_; 
v_unused_4757_ = lean_ctor_get(v___x_4747_, 0);
lean_dec(v_unused_4757_);
v___x_4749_ = v___x_4747_;
v_isShared_4750_ = v_isSharedCheck_4756_;
goto v_resetjp_4748_;
}
else
{
lean_dec(v___x_4747_);
v___x_4749_ = lean_box(0);
v_isShared_4750_ = v_isSharedCheck_4756_;
goto v_resetjp_4748_;
}
v_resetjp_4748_:
{
lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4754_; 
v___x_4751_ = lean_box(v_anyFailed_4740_);
v___x_4752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4752_, 0, v_entries_4738_);
lean_ctor_set(v___x_4752_, 1, v___x_4751_);
if (v_isShared_4750_ == 0)
{
lean_ctor_set(v___x_4749_, 0, v___x_4752_);
v___x_4754_ = v___x_4749_;
goto v_reusejp_4753_;
}
else
{
lean_object* v_reuseFailAlloc_4755_; 
v_reuseFailAlloc_4755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4755_, 0, v___x_4752_);
v___x_4754_ = v_reuseFailAlloc_4755_;
goto v_reusejp_4753_;
}
v_reusejp_4753_:
{
return v___x_4754_;
}
}
}
else
{
lean_object* v_a_4758_; lean_object* v___x_4760_; uint8_t v_isShared_4761_; uint8_t v_isSharedCheck_4765_; 
lean_dec_ref(v_entries_4738_);
v_a_4758_ = lean_ctor_get(v___x_4747_, 0);
v_isSharedCheck_4765_ = !lean_is_exclusive(v___x_4747_);
if (v_isSharedCheck_4765_ == 0)
{
v___x_4760_ = v___x_4747_;
v_isShared_4761_ = v_isSharedCheck_4765_;
goto v_resetjp_4759_;
}
else
{
lean_inc(v_a_4758_);
lean_dec(v___x_4747_);
v___x_4760_ = lean_box(0);
v_isShared_4761_ = v_isSharedCheck_4765_;
goto v_resetjp_4759_;
}
v_resetjp_4759_:
{
lean_object* v___x_4763_; 
if (v_isShared_4761_ == 0)
{
v___x_4763_ = v___x_4760_;
goto v_reusejp_4762_;
}
else
{
lean_object* v_reuseFailAlloc_4764_; 
v_reuseFailAlloc_4764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4764_, 0, v_a_4758_);
v___x_4763_ = v_reuseFailAlloc_4764_;
goto v_reusejp_4762_;
}
v_reusejp_4762_:
{
return v___x_4763_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_errors_4737_ = stack[0].m_obj;
lean_object* v_entries_4738_ = stack[1].m_obj;
lean_object* v_____r_4739_ = stack[2].m_obj;
uint8_t v_anyFailed_4740_ = stack[3].m_num;
lean_object* v___y_4741_ = stack[4].m_obj;
lean_object* v___y_4742_ = stack[5].m_obj;
lean_object* v_res_4766_;
v_res_4766_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(v_errors_4737_, v_entries_4738_, v_____r_4739_, v_anyFailed_4740_, v___y_4741_, v___y_4742_);
stack->m_obj
 = v_res_4766_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0___boxed(lean_object* v_errors_4767_, lean_object* v_entries_4768_, lean_object* v_____r_4769_, lean_object* v_anyFailed_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_){
_start:
{
uint8_t v_anyFailed_boxed_4774_; lean_object* v_res_4775_; 
v_anyFailed_boxed_4774_ = lean_unbox(v_anyFailed_4770_);
v_res_4775_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(v_errors_4767_, v_entries_4768_, v_____r_4769_, v_anyFailed_boxed_4774_, v___y_4771_, v___y_4772_);
lean_dec(v___y_4772_);
lean_dec_ref(v___y_4771_);
lean_dec_ref(v_errors_4767_);
return v_res_4775_;
}
}
lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(lean_object* v_sp_4776_, lean_object* v_env_4777_, lean_object* v_mod_4778_){
_start:
{
lean_object* v_a_4781_; lean_object* v_a_4785_; uint8_t v_anyFailed_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; uint16_t v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; uint8_t v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___y_4830_; lean_object* v_fileName_4846_; lean_object* v_fileMap_4847_; lean_object* v_currNamespace_4848_; lean_object* v_openDecls_4849_; lean_object* v_initHeartbeats_4850_; lean_object* v_maxHeartbeats_4851_; lean_object* v_quotContext_4852_; lean_object* v_currMacroScope_4853_; lean_object* v_cancelTk_x3f_4854_; lean_object* v_inheritedTraceOptions_4855_; lean_object* v_currRecDepth_4856_; lean_object* v_ref_4857_; uint8_t v_suppressElabErrors_4858_; uint8_t v_isRecordingDeps_4859_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; uint8_t v___y_4882_; lean_object* v_env_4903_; uint8_t v___x_4904_; uint8_t v___x_4905_; 
v_anyFailed_4802_ = 0;
v___x_4803_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_4804_ = l_Lean_instInhabitedFileMap_default;
v___x_4805_ = l_Lean_Options_empty;
v___x_4806_ = lean_box(0);
v___x_4807_ = lean_box(0);
v___x_4808_ = lean_unsigned_to_nat(0u);
v___x_4809_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5);
v___x_4810_ = l_Lean_firstFrontendMacroScope;
v___x_4811_ = lean_box(0);
v___x_4812_ = lean_box(0);
v___x_4813_ = lean_uint16_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_4814_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7);
v___x_4815_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10));
v___x_4816_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11));
v___x_4817_ = lean_unsigned_to_nat(32u);
v___x_4818_ = lean_mk_empty_array_with_capacity(v___x_4817_);
lean_dec_ref(v___x_4818_);
v___x_4819_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14);
v___x_4820_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_4821_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___closed__0));
v___x_4822_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18);
v___x_4823_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_4824_ = 1;
v___x_4825_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
v___x_4826_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4826_, 0, v_env_4777_);
lean_ctor_set(v___x_4826_, 1, v___x_4814_);
lean_ctor_set(v___x_4826_, 2, v___x_4815_);
lean_ctor_set(v___x_4826_, 3, v___x_4816_);
lean_ctor_set(v___x_4826_, 4, v___x_4819_);
lean_ctor_set(v___x_4826_, 5, v___x_4820_);
lean_ctor_set(v___x_4826_, 6, v___x_4822_);
lean_ctor_set(v___x_4826_, 7, v___x_4823_);
lean_ctor_set(v___x_4826_, 8, v___x_4825_);
lean_ctor_set(v___x_4826_, 9, v___x_4821_);
v___x_4827_ = lean_io_get_num_heartbeats();
v___x_4828_ = lean_st_mk_ref(v___x_4826_);
v___x_4878_ = l_Lean_inheritedTraceOptions;
v___x_4879_ = lean_st_ref_get(v___x_4878_);
v___x_4880_ = lean_st_ref_get(v___x_4828_);
v_env_4903_ = lean_ctor_get(v___x_4880_, 0);
lean_inc_ref(v_env_4903_);
lean_dec(v___x_4880_);
v___x_4904_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4903_);
lean_dec_ref(v_env_4903_);
v___x_4905_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22);
if (v___x_4905_ == 0)
{
if (v___x_4904_ == 0)
{
v___y_4882_ = v___x_4824_;
goto v___jp_4881_;
}
else
{
v_fileName_4846_ = v___x_4803_;
v_fileMap_4847_ = v___x_4804_;
v_currNamespace_4848_ = v___x_4806_;
v_openDecls_4849_ = v___x_4807_;
v_initHeartbeats_4850_ = v___x_4827_;
v_maxHeartbeats_4851_ = v___x_4809_;
v_quotContext_4852_ = v___x_4806_;
v_currMacroScope_4853_ = v___x_4810_;
v_cancelTk_x3f_4854_ = v___x_4811_;
v_inheritedTraceOptions_4855_ = v___x_4879_;
v_currRecDepth_4856_ = v___x_4808_;
v_ref_4857_ = v___x_4812_;
v_suppressElabErrors_4858_ = v_anyFailed_4802_;
v_isRecordingDeps_4859_ = v_anyFailed_4802_;
goto v___jp_4845_;
}
}
else
{
if (v___x_4904_ == 0)
{
v_fileName_4846_ = v___x_4803_;
v_fileMap_4847_ = v___x_4804_;
v_currNamespace_4848_ = v___x_4806_;
v_openDecls_4849_ = v___x_4807_;
v_initHeartbeats_4850_ = v___x_4827_;
v_maxHeartbeats_4851_ = v___x_4809_;
v_quotContext_4852_ = v___x_4806_;
v_currMacroScope_4853_ = v___x_4810_;
v_cancelTk_x3f_4854_ = v___x_4811_;
v_inheritedTraceOptions_4855_ = v___x_4879_;
v_currRecDepth_4856_ = v___x_4808_;
v_ref_4857_ = v___x_4812_;
v_suppressElabErrors_4858_ = v_anyFailed_4802_;
v_isRecordingDeps_4859_ = v_anyFailed_4802_;
goto v___jp_4845_;
}
else
{
v___y_4882_ = v_anyFailed_4802_;
goto v___jp_4881_;
}
}
v___jp_4780_:
{
lean_object* v___x_4782_; lean_object* v___x_4783_; 
v___x_4782_ = lean_mk_io_user_error(v_a_4781_);
v___x_4783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4783_, 0, v___x_4782_);
return v___x_4783_;
}
v___jp_4784_:
{
if (lean_obj_tag(v_a_4785_) == 0)
{
lean_object* v_msg_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; 
v_msg_4786_ = lean_ctor_get(v_a_4785_, 1);
lean_inc_ref(v_msg_4786_);
lean_dec_ref_known(v_a_4785_, 2);
v___x_4787_ = l_Lean_MessageData_toString(v_msg_4786_);
v___x_4788_ = lean_mk_io_user_error(v___x_4787_);
v___x_4789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4789_, 0, v___x_4788_);
return v___x_4789_;
}
else
{
lean_object* v_id_4790_; lean_object* v___x_4791_; 
v_id_4790_ = lean_ctor_get(v_a_4785_, 0);
lean_inc(v_id_4790_);
lean_dec_ref_known(v_a_4785_, 2);
v___x_4791_ = l_Lean_InternalExceptionId_getName(v_id_4790_);
if (lean_obj_tag(v___x_4791_) == 0)
{
lean_object* v_a_4792_; lean_object* v___x_4793_; uint8_t v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; 
lean_dec(v_id_4790_);
v_a_4792_ = lean_ctor_get(v___x_4791_, 0);
lean_inc(v_a_4792_);
lean_dec_ref_known(v___x_4791_, 1);
v___x_4793_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_4794_ = 1;
v___x_4795_ = l_Lean_Name_toString(v_a_4792_, v___x_4794_);
v___x_4796_ = lean_string_append(v___x_4793_, v___x_4795_);
lean_dec_ref(v___x_4795_);
v_a_4781_ = v___x_4796_;
goto v___jp_4780_;
}
else
{
lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; 
lean_dec_ref_known(v___x_4791_, 1);
v___x_4797_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_4798_ = l_Nat_reprFast(v_id_4790_);
v___x_4799_ = lean_string_append(v___x_4797_, v___x_4798_);
lean_dec_ref(v___x_4798_);
v___x_4800_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_4801_ = lean_string_append(v___x_4799_, v___x_4800_);
v_a_4781_ = v___x_4801_;
goto v___jp_4780_;
}
}
}
v___jp_4829_:
{
if (lean_obj_tag(v___y_4830_) == 0)
{
lean_object* v_a_4831_; lean_object* v___x_4833_; uint8_t v_isShared_4834_; uint8_t v_isSharedCheck_4843_; 
v_a_4831_ = lean_ctor_get(v___y_4830_, 0);
v_isSharedCheck_4843_ = !lean_is_exclusive(v___y_4830_);
if (v_isSharedCheck_4843_ == 0)
{
v___x_4833_ = v___y_4830_;
v_isShared_4834_ = v_isSharedCheck_4843_;
goto v_resetjp_4832_;
}
else
{
lean_inc(v_a_4831_);
lean_dec(v___y_4830_);
v___x_4833_ = lean_box(0);
v_isShared_4834_ = v_isSharedCheck_4843_;
goto v_resetjp_4832_;
}
v_resetjp_4832_:
{
lean_object* v___x_4835_; lean_object* v_fst_4836_; lean_object* v_snd_4837_; lean_object* v___x_4838_; uint8_t v___x_4839_; lean_object* v___x_4841_; 
v___x_4835_ = lean_st_ref_get(v___x_4828_);
lean_dec(v___x_4828_);
lean_dec(v___x_4835_);
v_fst_4836_ = lean_ctor_get(v_a_4831_, 0);
lean_inc(v_fst_4836_);
v_snd_4837_ = lean_ctor_get(v_a_4831_, 1);
lean_inc(v_snd_4837_);
lean_dec(v_a_4831_);
v___x_4838_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4838_, 0, v_fst_4836_);
v___x_4839_ = lean_unbox(v_snd_4837_);
lean_dec(v_snd_4837_);
lean_ctor_set_uint8(v___x_4838_, sizeof(void*)*1, v___x_4839_);
if (v_isShared_4834_ == 0)
{
lean_ctor_set(v___x_4833_, 0, v___x_4838_);
v___x_4841_ = v___x_4833_;
goto v_reusejp_4840_;
}
else
{
lean_object* v_reuseFailAlloc_4842_; 
v_reuseFailAlloc_4842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4842_, 0, v___x_4838_);
v___x_4841_ = v_reuseFailAlloc_4842_;
goto v_reusejp_4840_;
}
v_reusejp_4840_:
{
return v___x_4841_;
}
}
}
else
{
lean_object* v_a_4844_; 
lean_dec(v___x_4828_);
v_a_4844_ = lean_ctor_get(v___y_4830_, 0);
lean_inc(v_a_4844_);
lean_dec_ref_known(v___y_4830_, 1);
v_a_4785_ = v_a_4844_;
goto v___jp_4784_;
}
}
v___jp_4845_:
{
lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; 
v___x_4860_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5);
lean_inc(v_cancelTk_x3f_4854_);
lean_inc(v_currMacroScope_4853_);
lean_inc(v_quotContext_4852_);
lean_inc(v_maxHeartbeats_4851_);
lean_inc(v_openDecls_4849_);
lean_inc(v_currNamespace_4848_);
lean_inc_ref(v_fileMap_4847_);
lean_inc_ref(v_fileName_4846_);
v___x_4861_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4861_, 0, v_fileName_4846_);
lean_ctor_set(v___x_4861_, 1, v_fileMap_4847_);
lean_ctor_set(v___x_4861_, 2, v___x_4805_);
lean_ctor_set(v___x_4861_, 3, v___x_4860_);
lean_ctor_set(v___x_4861_, 4, v_currNamespace_4848_);
lean_ctor_set(v___x_4861_, 5, v_openDecls_4849_);
lean_ctor_set(v___x_4861_, 6, v_initHeartbeats_4850_);
lean_ctor_set(v___x_4861_, 7, v_maxHeartbeats_4851_);
lean_ctor_set(v___x_4861_, 8, v_quotContext_4852_);
lean_ctor_set(v___x_4861_, 9, v_currMacroScope_4853_);
lean_ctor_set(v___x_4861_, 10, v_cancelTk_x3f_4854_);
lean_ctor_set(v___x_4861_, 11, v_inheritedTraceOptions_4855_);
lean_inc(v_ref_4857_);
v___x_4862_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_4862_, 0, v___x_4861_);
lean_ctor_set(v___x_4862_, 1, v_currRecDepth_4856_);
lean_ctor_set(v___x_4862_, 2, v_ref_4857_);
lean_ctor_set_uint16(v___x_4862_, sizeof(void*)*3, v___x_4813_);
lean_ctor_set_uint8(v___x_4862_, sizeof(void*)*3 + 2, v_suppressElabErrors_4858_);
lean_ctor_set_uint8(v___x_4862_, sizeof(void*)*3 + 3, v_isRecordingDeps_4859_);
v___x_4863_ = l_Lean_Linter_CodeQuality_getPackageChecks(v___x_4862_, v___x_4828_);
if (lean_obj_tag(v___x_4863_) == 0)
{
lean_object* v_a_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; 
v_a_4864_ = lean_ctor_get(v___x_4863_, 0);
lean_inc(v_a_4864_);
lean_dec_ref_known(v___x_4863_, 1);
v___x_4865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4865_, 0, v_sp_4776_);
lean_ctor_set(v___x_4865_, 1, v_mod_4778_);
v___x_4866_ = l_Lean_Linter_CodeQuality_runPackageChecks(v_a_4864_, v___x_4865_, v___x_4862_, v___x_4828_);
if (lean_obj_tag(v___x_4866_) == 0)
{
lean_object* v_a_4867_; lean_object* v_entries_4868_; lean_object* v_errors_4869_; lean_object* v___x_4870_; uint8_t v___x_4871_; 
v_a_4867_ = lean_ctor_get(v___x_4866_, 0);
lean_inc(v_a_4867_);
lean_dec_ref_known(v___x_4866_, 1);
v_entries_4868_ = lean_ctor_get(v_a_4867_, 0);
lean_inc_ref(v_entries_4868_);
v_errors_4869_ = lean_ctor_get(v_a_4867_, 1);
lean_inc_ref(v_errors_4869_);
lean_dec(v_a_4867_);
v___x_4870_ = lean_array_get_size(v_errors_4869_);
v___x_4871_ = lean_nat_dec_eq(v___x_4870_, v___x_4808_);
if (v___x_4871_ == 0)
{
lean_object* v___x_4872_; lean_object* v___x_4873_; 
v___x_4872_ = lean_box(0);
v___x_4873_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(v_errors_4869_, v_entries_4868_, v___x_4872_, v___x_4824_, v___x_4862_, v___x_4828_);
lean_dec_ref_known(v___x_4862_, 3);
lean_dec_ref(v_errors_4869_);
v___y_4830_ = v___x_4873_;
goto v___jp_4829_;
}
else
{
lean_object* v___x_4874_; lean_object* v___x_4875_; 
v___x_4874_ = lean_box(0);
v___x_4875_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(v_errors_4869_, v_entries_4868_, v___x_4874_, v_anyFailed_4802_, v___x_4862_, v___x_4828_);
lean_dec_ref_known(v___x_4862_, 3);
lean_dec_ref(v_errors_4869_);
v___y_4830_ = v___x_4875_;
goto v___jp_4829_;
}
}
else
{
lean_object* v_a_4876_; 
lean_dec_ref_known(v___x_4862_, 3);
lean_dec(v___x_4828_);
v_a_4876_ = lean_ctor_get(v___x_4866_, 0);
lean_inc(v_a_4876_);
lean_dec_ref_known(v___x_4866_, 1);
v_a_4785_ = v_a_4876_;
goto v___jp_4784_;
}
}
else
{
lean_object* v_a_4877_; 
lean_dec_ref_known(v___x_4862_, 3);
lean_dec(v___x_4828_);
lean_dec(v_mod_4778_);
lean_dec(v_sp_4776_);
v_a_4877_ = lean_ctor_get(v___x_4863_, 0);
lean_inc(v_a_4877_);
lean_dec_ref_known(v___x_4863_, 1);
v_a_4785_ = v_a_4877_;
goto v___jp_4784_;
}
}
v___jp_4881_:
{
lean_object* v___x_4883_; lean_object* v_env_4884_; lean_object* v_nextMacroScope_4885_; lean_object* v_ngen_4886_; lean_object* v_auxDeclNGen_4887_; lean_object* v_traceState_4888_; lean_object* v_recordedDeps_4889_; lean_object* v_messages_4890_; lean_object* v_infoState_4891_; lean_object* v_snapshotTasks_4892_; lean_object* v___x_4894_; uint8_t v_isShared_4895_; uint8_t v_isSharedCheck_4901_; 
v___x_4883_ = lean_st_ref_take(v___x_4828_);
v_env_4884_ = lean_ctor_get(v___x_4883_, 0);
v_nextMacroScope_4885_ = lean_ctor_get(v___x_4883_, 1);
v_ngen_4886_ = lean_ctor_get(v___x_4883_, 2);
v_auxDeclNGen_4887_ = lean_ctor_get(v___x_4883_, 3);
v_traceState_4888_ = lean_ctor_get(v___x_4883_, 4);
v_recordedDeps_4889_ = lean_ctor_get(v___x_4883_, 6);
v_messages_4890_ = lean_ctor_get(v___x_4883_, 7);
v_infoState_4891_ = lean_ctor_get(v___x_4883_, 8);
v_snapshotTasks_4892_ = lean_ctor_get(v___x_4883_, 9);
v_isSharedCheck_4901_ = !lean_is_exclusive(v___x_4883_);
if (v_isSharedCheck_4901_ == 0)
{
lean_object* v_unused_4902_; 
v_unused_4902_ = lean_ctor_get(v___x_4883_, 5);
lean_dec(v_unused_4902_);
v___x_4894_ = v___x_4883_;
v_isShared_4895_ = v_isSharedCheck_4901_;
goto v_resetjp_4893_;
}
else
{
lean_inc(v_snapshotTasks_4892_);
lean_inc(v_infoState_4891_);
lean_inc(v_messages_4890_);
lean_inc(v_recordedDeps_4889_);
lean_inc(v_traceState_4888_);
lean_inc(v_auxDeclNGen_4887_);
lean_inc(v_ngen_4886_);
lean_inc(v_nextMacroScope_4885_);
lean_inc(v_env_4884_);
lean_dec(v___x_4883_);
v___x_4894_ = lean_box(0);
v_isShared_4895_ = v_isSharedCheck_4901_;
goto v_resetjp_4893_;
}
v_resetjp_4893_:
{
lean_object* v___x_4896_; lean_object* v___x_4898_; 
v___x_4896_ = l_Lean_Kernel_enableDiag(v_env_4884_, v___y_4882_);
if (v_isShared_4895_ == 0)
{
lean_ctor_set(v___x_4894_, 5, v___x_4820_);
lean_ctor_set(v___x_4894_, 0, v___x_4896_);
v___x_4898_ = v___x_4894_;
goto v_reusejp_4897_;
}
else
{
lean_object* v_reuseFailAlloc_4900_; 
v_reuseFailAlloc_4900_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4900_, 0, v___x_4896_);
lean_ctor_set(v_reuseFailAlloc_4900_, 1, v_nextMacroScope_4885_);
lean_ctor_set(v_reuseFailAlloc_4900_, 2, v_ngen_4886_);
lean_ctor_set(v_reuseFailAlloc_4900_, 3, v_auxDeclNGen_4887_);
lean_ctor_set(v_reuseFailAlloc_4900_, 4, v_traceState_4888_);
lean_ctor_set(v_reuseFailAlloc_4900_, 5, v___x_4820_);
lean_ctor_set(v_reuseFailAlloc_4900_, 6, v_recordedDeps_4889_);
lean_ctor_set(v_reuseFailAlloc_4900_, 7, v_messages_4890_);
lean_ctor_set(v_reuseFailAlloc_4900_, 8, v_infoState_4891_);
lean_ctor_set(v_reuseFailAlloc_4900_, 9, v_snapshotTasks_4892_);
v___x_4898_ = v_reuseFailAlloc_4900_;
goto v_reusejp_4897_;
}
v_reusejp_4897_:
{
lean_object* v___x_4899_; 
v___x_4899_ = lean_st_ref_put(v___x_4828_, v___x_4898_);
v_fileName_4846_ = v___x_4803_;
v_fileMap_4847_ = v___x_4804_;
v_currNamespace_4848_ = v___x_4806_;
v_openDecls_4849_ = v___x_4807_;
v_initHeartbeats_4850_ = v___x_4827_;
v_maxHeartbeats_4851_ = v___x_4809_;
v_quotContext_4852_ = v___x_4806_;
v_currMacroScope_4853_ = v___x_4810_;
v_cancelTk_x3f_4854_ = v___x_4811_;
v_inheritedTraceOptions_4855_ = v___x_4879_;
v_currRecDepth_4856_ = v___x_4808_;
v_ref_4857_ = v___x_4812_;
v_suppressElabErrors_4858_ = v_anyFailed_4802_;
v_isRecordingDeps_4859_ = v_anyFailed_4802_;
goto v___jp_4845_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_0interp(lean_interpreter_value* stack)
{
lean_object* v_sp_4776_ = stack[0].m_obj;
lean_object* v_env_4777_ = stack[1].m_obj;
lean_object* v_mod_4778_ = stack[2].m_obj;
lean_object* v_res_4906_;
v_res_4906_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(v_sp_4776_, v_env_4777_, v_mod_4778_);
stack->m_obj
 = v_res_4906_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___boxed(lean_object* v_sp_4907_, lean_object* v_env_4908_, lean_object* v_mod_4909_, lean_object* v_a_4910_){
_start:
{
lean_object* v_res_4911_; 
v_res_4911_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(v_sp_4907_, v_env_4908_, v_mod_4909_);
return v_res_4911_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1(lean_object* v_as_4912_, size_t v_sz_4913_, size_t v_i_4914_, lean_object* v_b_4915_, lean_object* v___y_4916_, lean_object* v___y_4917_){
_start:
{
lean_object* v___x_4919_; 
v___x_4919_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(v_as_4912_, v_sz_4913_, v_i_4914_, v_b_4915_, v___y_4916_);
return v___x_4919_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4912_ = stack[0].m_obj;
size_t v_sz_4913_ = stack[1].m_num;
size_t v_i_4914_ = stack[2].m_num;
lean_object* v_b_4915_ = stack[3].m_obj;
lean_object* v___y_4916_ = stack[4].m_obj;
lean_object* v___y_4917_ = stack[5].m_obj;
lean_object* v_res_4920_;
v_res_4920_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1(v_as_4912_, v_sz_4913_, v_i_4914_, v_b_4915_, v___y_4916_, v___y_4917_);
stack->m_obj
 = v_res_4920_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___boxed(lean_object* v_as_4921_, lean_object* v_sz_4922_, lean_object* v_i_4923_, lean_object* v_b_4924_, lean_object* v___y_4925_, lean_object* v___y_4926_, lean_object* v___y_4927_){
_start:
{
size_t v_sz_boxed_4928_; size_t v_i_boxed_4929_; lean_object* v_res_4930_; 
v_sz_boxed_4928_ = lean_unbox_usize(v_sz_4922_);
lean_dec(v_sz_4922_);
v_i_boxed_4929_ = lean_unbox_usize(v_i_4923_);
lean_dec(v_i_4923_);
v_res_4930_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1(v_as_4921_, v_sz_boxed_4928_, v_i_boxed_4929_, v_b_4924_, v___y_4925_, v___y_4926_);
lean_dec(v___y_4926_);
lean_dec_ref(v___y_4925_);
lean_dec_ref(v_as_4921_);
return v_res_4930_;
}
}
lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1(){
_start:
{
lean_object* v___x_4932_; 
v___x_4932_ = lean_enable_initializer_execution();
return v___x_4932_;
}
}
LEAN_EXPORT void l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4933_;
v_res_4933_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1();
stack->m_obj
 = v_res_4933_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1___boxed(lean_object* v_a_4934_){
_start:
{
lean_object* v_res_4935_; 
v_res_4935_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1();
return v_res_4935_;
}
}
lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(lean_object* v_region_4936_){
_start:
{
lean_object* v___x_4938_; 
v___x_4938_ = lean_compacted_region_free(v_region_4936_);
return v___x_4938_;
}
}
LEAN_EXPORT void l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_region_4936_ = stack[0].m_obj;
lean_object* v_res_4939_;
v_res_4939_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(v_region_4936_);
stack->m_obj
 = v_res_4939_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4___boxed(lean_object* v_region_4940_, lean_object* v_a_4941_){
_start:
{
lean_object* v_res_4942_; 
v_res_4942_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(v_region_4940_);
return v_res_4942_;
}
}
lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(lean_object* v_o_4946_, lean_object* v_k_4947_, uint8_t v_v_4948_){
_start:
{
lean_object* v_map_4949_; uint8_t v_hasTrace_4950_; lean_object* v___x_4952_; uint8_t v_isShared_4953_; uint8_t v_isSharedCheck_4964_; 
v_map_4949_ = lean_ctor_get(v_o_4946_, 0);
v_hasTrace_4950_ = lean_ctor_get_uint8(v_o_4946_, sizeof(void*)*1);
v_isSharedCheck_4964_ = !lean_is_exclusive(v_o_4946_);
if (v_isSharedCheck_4964_ == 0)
{
v___x_4952_ = v_o_4946_;
v_isShared_4953_ = v_isSharedCheck_4964_;
goto v_resetjp_4951_;
}
else
{
lean_inc(v_map_4949_);
lean_dec(v_o_4946_);
v___x_4952_ = lean_box(0);
v_isShared_4953_ = v_isSharedCheck_4964_;
goto v_resetjp_4951_;
}
v_resetjp_4951_:
{
lean_object* v___x_4954_; lean_object* v___x_4955_; 
v___x_4954_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4954_, 0, v_v_4948_);
lean_inc(v_k_4947_);
v___x_4955_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4947_, v___x_4954_, v_map_4949_);
if (v_hasTrace_4950_ == 0)
{
lean_object* v___x_4956_; uint8_t v___x_4957_; lean_object* v___x_4959_; 
v___x_4956_ = ((lean_object*)(l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___closed__1));
v___x_4957_ = l_Lean_Name_isPrefixOf(v___x_4956_, v_k_4947_);
lean_dec(v_k_4947_);
if (v_isShared_4953_ == 0)
{
lean_ctor_set(v___x_4952_, 0, v___x_4955_);
v___x_4959_ = v___x_4952_;
goto v_reusejp_4958_;
}
else
{
lean_object* v_reuseFailAlloc_4960_; 
v_reuseFailAlloc_4960_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4960_, 0, v___x_4955_);
v___x_4959_ = v_reuseFailAlloc_4960_;
goto v_reusejp_4958_;
}
v_reusejp_4958_:
{
lean_ctor_set_uint8(v___x_4959_, sizeof(void*)*1, v___x_4957_);
return v___x_4959_;
}
}
else
{
lean_object* v___x_4962_; 
lean_dec(v_k_4947_);
if (v_isShared_4953_ == 0)
{
lean_ctor_set(v___x_4952_, 0, v___x_4955_);
v___x_4962_ = v___x_4952_;
goto v_reusejp_4961_;
}
else
{
lean_object* v_reuseFailAlloc_4963_; 
v_reuseFailAlloc_4963_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4963_, 0, v___x_4955_);
lean_ctor_set_uint8(v_reuseFailAlloc_4963_, sizeof(void*)*1, v_hasTrace_4950_);
v___x_4962_ = v_reuseFailAlloc_4963_;
goto v_reusejp_4961_;
}
v_reusejp_4961_:
{
return v___x_4962_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_4946_ = stack[0].m_obj;
lean_object* v_k_4947_ = stack[1].m_obj;
uint8_t v_v_4948_ = stack[2].m_num;
lean_object* v_res_4965_;
v_res_4965_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_o_4946_, v_k_4947_, v_v_4948_);
stack->m_obj
 = v_res_4965_;
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___boxed(lean_object* v_o_4966_, lean_object* v_k_4967_, lean_object* v_v_4968_){
_start:
{
uint8_t v_v_boxed_4969_; lean_object* v_res_4970_; 
v_v_boxed_4969_ = lean_unbox(v_v_4968_);
v_res_4970_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_o_4966_, v_k_4967_, v_v_boxed_4969_);
return v_res_4970_;
}
}
lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__4(lean_object* v_s_4971_){
_start:
{
lean_object* v___x_4973_; lean_object* v___x_4974_; uint32_t v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; 
v___x_4973_ = lean_unsigned_to_nat(80u);
v___x_4974_ = l_Lean_Json_pretty(v_s_4971_, v___x_4973_);
v___x_4975_ = 10;
v___x_4976_ = lean_string_push(v___x_4974_, v___x_4975_);
v___x_4977_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_4976_);
return v___x_4977_;
}
}
LEAN_EXPORT void l_IO_println___at___00Lake_BuiltinLint_run_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_4971_ = stack[0].m_obj;
lean_object* v_res_4978_;
v_res_4978_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__4(v_s_4971_);
stack->m_obj
 = v_res_4978_;
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__4___boxed(lean_object* v_s_4979_, lean_object* v_a_4980_){
_start:
{
lean_object* v_res_4981_; 
v_res_4981_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__4(v_s_4979_);
return v_res_4981_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(lean_object* v_as_4982_, size_t v_sz_4983_, size_t v_i_4984_, lean_object* v_b_4985_){
_start:
{
uint8_t v___x_4987_; 
v___x_4987_ = lean_usize_dec_lt(v_i_4984_, v_sz_4983_);
if (v___x_4987_ == 0)
{
lean_object* v___x_4988_; 
v___x_4988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4988_, 0, v_b_4985_);
return v___x_4988_;
}
else
{
lean_object* v___x_4989_; lean_object* v_a_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; 
v___x_4989_ = lean_box(0);
v_a_4990_ = lean_array_uget_borrowed(v_as_4982_, v_i_4984_);
lean_inc(v_a_4990_);
v___x_4991_ = l_Lean_Linter_CodeQuality_instToJsonEntry_toJson(v_a_4990_);
v___x_4992_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__4(v___x_4991_);
if (lean_obj_tag(v___x_4992_) == 0)
{
size_t v___x_4993_; size_t v___x_4994_; 
lean_dec_ref_known(v___x_4992_, 1);
v___x_4993_ = ((size_t)1ULL);
v___x_4994_ = lean_usize_add(v_i_4984_, v___x_4993_);
v_i_4984_ = v___x_4994_;
v_b_4985_ = v___x_4989_;
goto _start;
}
else
{
return v___x_4992_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4982_ = stack[0].m_obj;
size_t v_sz_4983_ = stack[1].m_num;
size_t v_i_4984_ = stack[2].m_num;
lean_object* v_b_4985_ = stack[3].m_obj;
lean_object* v_res_4996_;
v_res_4996_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(v_as_4982_, v_sz_4983_, v_i_4984_, v_b_4985_);
stack->m_obj
 = v_res_4996_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___boxed(lean_object* v_as_4997_, lean_object* v_sz_4998_, lean_object* v_i_4999_, lean_object* v_b_5000_, lean_object* v___y_5001_){
_start:
{
size_t v_sz_boxed_5002_; size_t v_i_boxed_5003_; lean_object* v_res_5004_; 
v_sz_boxed_5002_ = lean_unbox_usize(v_sz_4998_);
lean_dec(v_sz_4998_);
v_i_boxed_5003_ = lean_unbox_usize(v_i_4999_);
lean_dec(v_i_4999_);
v_res_5004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(v_as_4997_, v_sz_boxed_5002_, v_i_boxed_5003_, v_b_5000_);
lean_dec_ref(v_as_4997_);
return v_res_5004_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(lean_object* v___x_5005_, size_t v_sz_5006_, size_t v_i_5007_, lean_object* v_bs_5008_){
_start:
{
uint8_t v_anyUnlocated_5009_; 
v_anyUnlocated_5009_ = lean_usize_dec_lt(v_i_5007_, v_sz_5006_);
if (v_anyUnlocated_5009_ == 0)
{
return v_bs_5008_;
}
else
{
lean_object* v___x_5010_; uint8_t v_anyFailed_5011_; lean_object* v_v_5012_; lean_object* v_bs_x27_5013_; lean_object* v___x_5014_; size_t v___x_5015_; size_t v___x_5016_; lean_object* v___x_5017_; 
v___x_5010_ = lean_unsigned_to_nat(0u);
v_anyFailed_5011_ = lean_nat_dec_eq(v___x_5005_, v___x_5010_);
v_v_5012_ = lean_array_uget(v_bs_5008_, v_i_5007_);
v_bs_x27_5013_ = lean_array_uset(v_bs_5008_, v_i_5007_, v___x_5010_);
v___x_5014_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_5014_, 0, v_v_5012_);
lean_ctor_set_uint8(v___x_5014_, sizeof(void*)*1, v_anyFailed_5011_);
lean_ctor_set_uint8(v___x_5014_, sizeof(void*)*1 + 1, v_anyUnlocated_5009_);
lean_ctor_set_uint8(v___x_5014_, sizeof(void*)*1 + 2, v_anyFailed_5011_);
v___x_5015_ = ((size_t)1ULL);
v___x_5016_ = lean_usize_add(v_i_5007_, v___x_5015_);
v___x_5017_ = lean_array_uset(v_bs_x27_5013_, v_i_5007_, v___x_5014_);
v_i_5007_ = v___x_5016_;
v_bs_5008_ = v___x_5017_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_5005_ = stack[0].m_obj;
size_t v_sz_5006_ = stack[1].m_num;
size_t v_i_5007_ = stack[2].m_num;
lean_object* v_bs_5008_ = stack[3].m_obj;
lean_object* v_res_5019_;
v_res_5019_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(v___x_5005_, v_sz_5006_, v_i_5007_, v_bs_5008_);
stack->m_obj
 = v_res_5019_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1___boxed(lean_object* v___x_5020_, lean_object* v_sz_5021_, lean_object* v_i_5022_, lean_object* v_bs_5023_){
_start:
{
size_t v_sz_boxed_5024_; size_t v_i_boxed_5025_; lean_object* v_res_5026_; 
v_sz_boxed_5024_ = lean_unbox_usize(v_sz_5021_);
lean_dec(v_sz_5021_);
v_i_boxed_5025_ = lean_unbox_usize(v_i_5022_);
lean_dec(v_i_5022_);
v_res_5026_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(v___x_5020_, v_sz_boxed_5024_, v_i_boxed_5025_, v_bs_5023_);
lean_dec(v___x_5020_);
return v_res_5026_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(lean_object* v_as_5027_, size_t v_i_5028_, size_t v_stop_5029_, lean_object* v_b_5030_){
_start:
{
uint8_t v___x_5031_; 
v___x_5031_ = lean_usize_dec_eq(v_i_5028_, v_stop_5029_);
if (v___x_5031_ == 0)
{
lean_object* v___x_5032_; lean_object* v_fst_5033_; lean_object* v_snd_5034_; uint8_t v___x_5035_; lean_object* v___x_5036_; size_t v___x_5037_; size_t v___x_5038_; 
v___x_5032_ = lean_array_uget_borrowed(v_as_5027_, v_i_5028_);
v_fst_5033_ = lean_ctor_get(v___x_5032_, 0);
v_snd_5034_ = lean_ctor_get(v___x_5032_, 1);
v___x_5035_ = lean_unbox(v_snd_5034_);
lean_inc(v_fst_5033_);
v___x_5036_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_b_5030_, v_fst_5033_, v___x_5035_);
v___x_5037_ = ((size_t)1ULL);
v___x_5038_ = lean_usize_add(v_i_5028_, v___x_5037_);
v_i_5028_ = v___x_5038_;
v_b_5030_ = v___x_5036_;
goto _start;
}
else
{
return v_b_5030_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_5027_ = stack[0].m_obj;
size_t v_i_5028_ = stack[1].m_num;
size_t v_stop_5029_ = stack[2].m_num;
lean_object* v_b_5030_ = stack[3].m_obj;
lean_object* v_res_5040_;
v_res_5040_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(v_as_5027_, v_i_5028_, v_stop_5029_, v_b_5030_);
stack->m_obj
 = v_res_5040_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2___boxed(lean_object* v_as_5041_, lean_object* v_i_5042_, lean_object* v_stop_5043_, lean_object* v_b_5044_){
_start:
{
size_t v_i_boxed_5045_; size_t v_stop_boxed_5046_; lean_object* v_res_5047_; 
v_i_boxed_5045_ = lean_unbox_usize(v_i_5042_);
lean_dec(v_i_5042_);
v_stop_boxed_5046_ = lean_unbox_usize(v_stop_5043_);
lean_dec(v_stop_5043_);
v_res_5047_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(v_as_5041_, v_i_boxed_5045_, v_stop_boxed_5046_, v_b_5044_);
lean_dec_ref(v_as_5041_);
return v_res_5047_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(lean_object* v___x_5057_, lean_object* v_checkImports_5058_, lean_object* v_args_5059_, lean_object* v___x_5060_, lean_object* v_as_5061_, size_t v_sz_5062_, size_t v_i_5063_, lean_object* v_b_5064_){
_start:
{
lean_object* v_a_5067_; lean_object* v___x_5071_; uint8_t v_anyFailed_5072_; uint8_t v_anyUnlocated_5073_; lean_object* v___x_5074_; lean_object* v_envLinterModule_5075_; uint8_t v___x_5076_; 
v___x_5071_ = lean_unsigned_to_nat(0u);
v_anyFailed_5072_ = lean_nat_dec_eq(v___x_5057_, v___x_5071_);
v_anyUnlocated_5073_ = 1;
v___x_5074_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__3));
v_envLinterModule_5075_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_envLinterModule_5075_, 0, v___x_5074_);
lean_ctor_set_uint8(v_envLinterModule_5075_, sizeof(void*)*1, v_anyFailed_5072_);
lean_ctor_set_uint8(v_envLinterModule_5075_, sizeof(void*)*1 + 1, v_anyUnlocated_5073_);
lean_ctor_set_uint8(v_envLinterModule_5075_, sizeof(void*)*1 + 2, v_anyFailed_5072_);
v___x_5076_ = lean_usize_dec_lt(v_i_5063_, v_sz_5062_);
if (v___x_5076_ == 0)
{
lean_object* v___x_5077_; 
lean_dec_ref_known(v_envLinterModule_5075_, 1);
lean_dec(v___x_5060_);
v___x_5077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5077_, 0, v_b_5064_);
return v___x_5077_;
}
else
{
lean_object* v_snd_5078_; lean_object* v_snd_5079_; lean_object* v_snd_5080_; lean_object* v_snd_5081_; lean_object* v_fst_5082_; lean_object* v___x_5084_; uint8_t v_isShared_5085_; uint8_t v_isSharedCheck_5395_; 
v_snd_5078_ = lean_ctor_get(v_b_5064_, 1);
lean_inc(v_snd_5078_);
v_snd_5079_ = lean_ctor_get(v_snd_5078_, 1);
lean_inc(v_snd_5079_);
v_snd_5080_ = lean_ctor_get(v_snd_5079_, 1);
lean_inc(v_snd_5080_);
v_snd_5081_ = lean_ctor_get(v_snd_5080_, 1);
lean_inc(v_snd_5081_);
v_fst_5082_ = lean_ctor_get(v_b_5064_, 0);
v_isSharedCheck_5395_ = !lean_is_exclusive(v_b_5064_);
if (v_isSharedCheck_5395_ == 0)
{
lean_object* v_unused_5396_; 
v_unused_5396_ = lean_ctor_get(v_b_5064_, 1);
lean_dec(v_unused_5396_);
v___x_5084_ = v_b_5064_;
v_isShared_5085_ = v_isSharedCheck_5395_;
goto v_resetjp_5083_;
}
else
{
lean_inc(v_fst_5082_);
lean_dec(v_b_5064_);
v___x_5084_ = lean_box(0);
v_isShared_5085_ = v_isSharedCheck_5395_;
goto v_resetjp_5083_;
}
v_resetjp_5083_:
{
lean_object* v_fst_5086_; lean_object* v___x_5088_; uint8_t v_isShared_5089_; uint8_t v_isSharedCheck_5393_; 
v_fst_5086_ = lean_ctor_get(v_snd_5078_, 0);
v_isSharedCheck_5393_ = !lean_is_exclusive(v_snd_5078_);
if (v_isSharedCheck_5393_ == 0)
{
lean_object* v_unused_5394_; 
v_unused_5394_ = lean_ctor_get(v_snd_5078_, 1);
lean_dec(v_unused_5394_);
v___x_5088_ = v_snd_5078_;
v_isShared_5089_ = v_isSharedCheck_5393_;
goto v_resetjp_5087_;
}
else
{
lean_inc(v_fst_5086_);
lean_dec(v_snd_5078_);
v___x_5088_ = lean_box(0);
v_isShared_5089_ = v_isSharedCheck_5393_;
goto v_resetjp_5087_;
}
v_resetjp_5087_:
{
lean_object* v_fst_5090_; lean_object* v___x_5092_; uint8_t v_isShared_5093_; uint8_t v_isSharedCheck_5391_; 
v_fst_5090_ = lean_ctor_get(v_snd_5079_, 0);
v_isSharedCheck_5391_ = !lean_is_exclusive(v_snd_5079_);
if (v_isSharedCheck_5391_ == 0)
{
lean_object* v_unused_5392_; 
v_unused_5392_ = lean_ctor_get(v_snd_5079_, 1);
lean_dec(v_unused_5392_);
v___x_5092_ = v_snd_5079_;
v_isShared_5093_ = v_isSharedCheck_5391_;
goto v_resetjp_5091_;
}
else
{
lean_inc(v_fst_5090_);
lean_dec(v_snd_5079_);
v___x_5092_ = lean_box(0);
v_isShared_5093_ = v_isSharedCheck_5391_;
goto v_resetjp_5091_;
}
v_resetjp_5091_:
{
lean_object* v_fst_5094_; lean_object* v___x_5096_; uint8_t v_isShared_5097_; uint8_t v_isSharedCheck_5389_; 
v_fst_5094_ = lean_ctor_get(v_snd_5080_, 0);
v_isSharedCheck_5389_ = !lean_is_exclusive(v_snd_5080_);
if (v_isSharedCheck_5389_ == 0)
{
lean_object* v_unused_5390_; 
v_unused_5390_ = lean_ctor_get(v_snd_5080_, 1);
lean_dec(v_unused_5390_);
v___x_5096_ = v_snd_5080_;
v_isShared_5097_ = v_isSharedCheck_5389_;
goto v_resetjp_5095_;
}
else
{
lean_inc(v_fst_5094_);
lean_dec(v_snd_5080_);
v___x_5096_ = lean_box(0);
v_isShared_5097_ = v_isSharedCheck_5389_;
goto v_resetjp_5095_;
}
v_resetjp_5095_:
{
lean_object* v_fst_5098_; lean_object* v_snd_5099_; lean_object* v___x_5101_; uint8_t v_isShared_5102_; uint8_t v_isSharedCheck_5388_; 
v_fst_5098_ = lean_ctor_get(v_snd_5081_, 0);
v_snd_5099_ = lean_ctor_get(v_snd_5081_, 1);
v_isSharedCheck_5388_ = !lean_is_exclusive(v_snd_5081_);
if (v_isSharedCheck_5388_ == 0)
{
v___x_5101_ = v_snd_5081_;
v_isShared_5102_ = v_isSharedCheck_5388_;
goto v_resetjp_5100_;
}
else
{
lean_inc(v_snd_5099_);
lean_inc(v_fst_5098_);
lean_dec(v_snd_5081_);
v___x_5101_ = lean_box(0);
v_isShared_5102_ = v_isSharedCheck_5388_;
goto v_resetjp_5100_;
}
v_resetjp_5100_:
{
lean_object* v___x_5103_; lean_object* v_a_5104_; lean_object* v___y_5106_; lean_object* v___y_5107_; uint8_t v_anyFailed_5108_; uint8_t v_anyUnlocated_5109_; lean_object* v_records_5110_; lean_object* v_codeQualityEntries_5111_; lean_object* v___y_5258_; lean_object* v___y_5259_; uint8_t v_anyFailed_5260_; uint8_t v_anyUnlocated_5261_; lean_object* v_records_5262_; lean_object* v_codeQualityEntries_5263_; lean_object* v___y_5281_; lean_object* v___y_5282_; lean_object* v___x_5321_; lean_object* v___x_5322_; 
v___x_5103_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v_a_5104_ = lean_array_uget_borrowed(v_as_5061_, v_i_5063_);
v___x_5321_ = lean_enable_initializer_execution();
lean_inc(v_a_5104_);
v___x_5322_ = l_Lean_findOLean(v_a_5104_);
if (lean_obj_tag(v___x_5322_) == 0)
{
lean_object* v_a_5323_; lean_object* v___x_5324_; 
v_a_5323_ = lean_ctor_get(v___x_5322_, 0);
lean_inc(v_a_5323_);
lean_dec_ref_known(v___x_5322_, 1);
v___x_5324_ = l_Lean_readModuleData(v_a_5323_);
lean_dec(v_a_5323_);
if (lean_obj_tag(v___x_5324_) == 0)
{
lean_object* v_a_5325_; lean_object* v_fst_5326_; lean_object* v_snd_5327_; uint8_t v___x_5328_; uint8_t v___y_5330_; 
v_a_5325_ = lean_ctor_get(v___x_5324_, 0);
lean_inc(v_a_5325_);
lean_dec_ref_known(v___x_5324_, 1);
v_fst_5326_ = lean_ctor_get(v_a_5325_, 0);
lean_inc(v_fst_5326_);
v_snd_5327_ = lean_ctor_get(v_a_5325_, 1);
lean_inc(v_snd_5327_);
lean_dec(v_a_5325_);
v___x_5328_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(v_fst_5326_);
lean_dec(v_fst_5326_);
if (v___x_5328_ == 0)
{
uint8_t v___x_5370_; 
v___x_5370_ = 2;
v___y_5330_ = v___x_5370_;
goto v___jp_5329_;
}
else
{
uint8_t v___x_5371_; 
v___x_5371_ = 1;
v___y_5330_ = v___x_5371_;
goto v___jp_5329_;
}
v___jp_5329_:
{
lean_object* v___x_5331_; 
v___x_5331_ = lean_compacted_region_free(v_snd_5327_);
if (lean_obj_tag(v___x_5331_) == 0)
{
lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; uint32_t v___x_5339_; lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; 
lean_dec_ref_known(v___x_5331_, 1);
lean_inc(v_a_5104_);
v___x_5332_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_5332_, 0, v_a_5104_);
lean_ctor_set_uint8(v___x_5332_, sizeof(void*)*1, v_anyFailed_5072_);
lean_ctor_set_uint8(v___x_5332_, sizeof(void*)*1 + 1, v_anyUnlocated_5073_);
lean_ctor_set_uint8(v___x_5332_, sizeof(void*)*1 + 2, v_anyFailed_5072_);
v___x_5333_ = lean_unsigned_to_nat(2u);
v___x_5334_ = lean_mk_empty_array_with_capacity(v___x_5333_);
v___x_5335_ = lean_array_push(v___x_5334_, v___x_5332_);
v___x_5336_ = lean_array_push(v___x_5335_, v_envLinterModule_5075_);
v___x_5337_ = l_Array_append___redArg(v___x_5336_, v_checkImports_5058_);
v___x_5338_ = l_Lean_Options_empty;
v___x_5339_ = 1024;
v___x_5340_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__4));
v___x_5341_ = lean_box(1);
v___x_5342_ = l_Lean_importModules(v___x_5337_, v___x_5338_, v___x_5339_, v___x_5340_, v_anyFailed_5072_, v_anyUnlocated_5073_, v___y_5330_, v___x_5341_);
if (lean_obj_tag(v___x_5342_) == 0)
{
lean_object* v_a_5343_; lean_object* v_linterOverrides_5344_; lean_object* v___x_5345_; uint8_t v___x_5346_; 
v_a_5343_ = lean_ctor_get(v___x_5342_, 0);
lean_inc(v_a_5343_);
lean_dec_ref_known(v___x_5342_, 1);
v_linterOverrides_5344_ = lean_ctor_get(v_args_5059_, 0);
v___x_5345_ = lean_array_get_size(v_linterOverrides_5344_);
v___x_5346_ = lean_nat_dec_lt(v___x_5071_, v___x_5345_);
if (v___x_5346_ == 0)
{
v___y_5281_ = v_a_5343_;
v___y_5282_ = v___x_5338_;
goto v___jp_5280_;
}
else
{
uint8_t v___x_5347_; 
v___x_5347_ = lean_nat_dec_le(v___x_5345_, v___x_5345_);
if (v___x_5347_ == 0)
{
if (v___x_5346_ == 0)
{
v___y_5281_ = v_a_5343_;
v___y_5282_ = v___x_5338_;
goto v___jp_5280_;
}
else
{
size_t v___x_5348_; size_t v___x_5349_; lean_object* v___x_5350_; 
v___x_5348_ = ((size_t)0ULL);
v___x_5349_ = lean_usize_of_nat(v___x_5345_);
v___x_5350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(v_linterOverrides_5344_, v___x_5348_, v___x_5349_, v___x_5338_);
v___y_5281_ = v_a_5343_;
v___y_5282_ = v___x_5350_;
goto v___jp_5280_;
}
}
else
{
size_t v___x_5351_; size_t v___x_5352_; lean_object* v___x_5353_; 
v___x_5351_ = ((size_t)0ULL);
v___x_5352_ = lean_usize_of_nat(v___x_5345_);
v___x_5353_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(v_linterOverrides_5344_, v___x_5351_, v___x_5352_, v___x_5338_);
v___y_5281_ = v_a_5343_;
v___y_5282_ = v___x_5353_;
goto v___jp_5280_;
}
}
}
else
{
lean_object* v_a_5354_; lean_object* v___x_5356_; uint8_t v_isShared_5357_; uint8_t v_isSharedCheck_5361_; 
lean_del_object(v___x_5101_);
lean_dec(v_snd_5099_);
lean_dec(v_fst_5098_);
lean_del_object(v___x_5096_);
lean_dec(v_fst_5094_);
lean_del_object(v___x_5092_);
lean_dec(v_fst_5090_);
lean_del_object(v___x_5088_);
lean_dec(v_fst_5086_);
lean_del_object(v___x_5084_);
lean_dec(v_fst_5082_);
lean_dec(v___x_5060_);
v_a_5354_ = lean_ctor_get(v___x_5342_, 0);
v_isSharedCheck_5361_ = !lean_is_exclusive(v___x_5342_);
if (v_isSharedCheck_5361_ == 0)
{
v___x_5356_ = v___x_5342_;
v_isShared_5357_ = v_isSharedCheck_5361_;
goto v_resetjp_5355_;
}
else
{
lean_inc(v_a_5354_);
lean_dec(v___x_5342_);
v___x_5356_ = lean_box(0);
v_isShared_5357_ = v_isSharedCheck_5361_;
goto v_resetjp_5355_;
}
v_resetjp_5355_:
{
lean_object* v___x_5359_; 
if (v_isShared_5357_ == 0)
{
v___x_5359_ = v___x_5356_;
goto v_reusejp_5358_;
}
else
{
lean_object* v_reuseFailAlloc_5360_; 
v_reuseFailAlloc_5360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5360_, 0, v_a_5354_);
v___x_5359_ = v_reuseFailAlloc_5360_;
goto v_reusejp_5358_;
}
v_reusejp_5358_:
{
return v___x_5359_;
}
}
}
}
else
{
lean_object* v_a_5362_; lean_object* v___x_5364_; uint8_t v_isShared_5365_; uint8_t v_isSharedCheck_5369_; 
lean_del_object(v___x_5101_);
lean_dec(v_snd_5099_);
lean_dec(v_fst_5098_);
lean_del_object(v___x_5096_);
lean_dec(v_fst_5094_);
lean_del_object(v___x_5092_);
lean_dec(v_fst_5090_);
lean_del_object(v___x_5088_);
lean_dec(v_fst_5086_);
lean_del_object(v___x_5084_);
lean_dec(v_fst_5082_);
lean_dec_ref_known(v_envLinterModule_5075_, 1);
lean_dec(v___x_5060_);
v_a_5362_ = lean_ctor_get(v___x_5331_, 0);
v_isSharedCheck_5369_ = !lean_is_exclusive(v___x_5331_);
if (v_isSharedCheck_5369_ == 0)
{
v___x_5364_ = v___x_5331_;
v_isShared_5365_ = v_isSharedCheck_5369_;
goto v_resetjp_5363_;
}
else
{
lean_inc(v_a_5362_);
lean_dec(v___x_5331_);
v___x_5364_ = lean_box(0);
v_isShared_5365_ = v_isSharedCheck_5369_;
goto v_resetjp_5363_;
}
v_resetjp_5363_:
{
lean_object* v___x_5367_; 
if (v_isShared_5365_ == 0)
{
v___x_5367_ = v___x_5364_;
goto v_reusejp_5366_;
}
else
{
lean_object* v_reuseFailAlloc_5368_; 
v_reuseFailAlloc_5368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5368_, 0, v_a_5362_);
v___x_5367_ = v_reuseFailAlloc_5368_;
goto v_reusejp_5366_;
}
v_reusejp_5366_:
{
return v___x_5367_;
}
}
}
}
}
else
{
lean_object* v_a_5372_; lean_object* v___x_5374_; uint8_t v_isShared_5375_; uint8_t v_isSharedCheck_5379_; 
lean_del_object(v___x_5101_);
lean_dec(v_snd_5099_);
lean_dec(v_fst_5098_);
lean_del_object(v___x_5096_);
lean_dec(v_fst_5094_);
lean_del_object(v___x_5092_);
lean_dec(v_fst_5090_);
lean_del_object(v___x_5088_);
lean_dec(v_fst_5086_);
lean_del_object(v___x_5084_);
lean_dec(v_fst_5082_);
lean_dec_ref_known(v_envLinterModule_5075_, 1);
lean_dec(v___x_5060_);
v_a_5372_ = lean_ctor_get(v___x_5324_, 0);
v_isSharedCheck_5379_ = !lean_is_exclusive(v___x_5324_);
if (v_isSharedCheck_5379_ == 0)
{
v___x_5374_ = v___x_5324_;
v_isShared_5375_ = v_isSharedCheck_5379_;
goto v_resetjp_5373_;
}
else
{
lean_inc(v_a_5372_);
lean_dec(v___x_5324_);
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
else
{
lean_object* v_a_5380_; lean_object* v___x_5382_; uint8_t v_isShared_5383_; uint8_t v_isSharedCheck_5387_; 
lean_del_object(v___x_5101_);
lean_dec(v_snd_5099_);
lean_dec(v_fst_5098_);
lean_del_object(v___x_5096_);
lean_dec(v_fst_5094_);
lean_del_object(v___x_5092_);
lean_dec(v_fst_5090_);
lean_del_object(v___x_5088_);
lean_dec(v_fst_5086_);
lean_del_object(v___x_5084_);
lean_dec(v_fst_5082_);
lean_dec_ref_known(v_envLinterModule_5075_, 1);
lean_dec(v___x_5060_);
v_a_5380_ = lean_ctor_get(v___x_5322_, 0);
v_isSharedCheck_5387_ = !lean_is_exclusive(v___x_5322_);
if (v_isSharedCheck_5387_ == 0)
{
v___x_5382_ = v___x_5322_;
v_isShared_5383_ = v_isSharedCheck_5387_;
goto v_resetjp_5381_;
}
else
{
lean_inc(v_a_5380_);
lean_dec(v___x_5322_);
v___x_5382_ = lean_box(0);
v_isShared_5383_ = v_isSharedCheck_5387_;
goto v_resetjp_5381_;
}
v_resetjp_5381_:
{
lean_object* v___x_5385_; 
if (v_isShared_5383_ == 0)
{
v___x_5385_ = v___x_5382_;
goto v_reusejp_5384_;
}
else
{
lean_object* v_reuseFailAlloc_5386_; 
v_reuseFailAlloc_5386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5386_, 0, v_a_5380_);
v___x_5385_ = v_reuseFailAlloc_5386_;
goto v_reusejp_5384_;
}
v_reusejp_5384_:
{
return v___x_5385_;
}
}
}
v___jp_5105_:
{
uint8_t v_mode_5112_; uint8_t v___x_5113_; uint8_t v___x_5114_; 
v_mode_5112_ = lean_ctor_get_uint8(v_args_5059_, sizeof(void*)*4 + 1);
v___x_5113_ = 2;
v___x_5114_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_5112_, v___x_5113_);
if (v___x_5114_ == 0)
{
lean_object* v___x_5115_; lean_object* v___x_5116_; 
v___x_5115_ = l_Lean_Name_getRoot(v_a_5104_);
lean_inc(v___x_5060_);
v___x_5116_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(v_args_5059_, v___y_5106_, v___x_5060_, v___y_5107_, v___x_5115_, v_fst_5098_);
lean_dec_ref(v___y_5106_);
if (lean_obj_tag(v___x_5116_) == 0)
{
lean_object* v_a_5117_; lean_object* v_outcome_5118_; 
v_a_5117_ = lean_ctor_get(v___x_5116_, 0);
lean_inc(v_a_5117_);
lean_dec_ref_known(v___x_5116_, 1);
v_outcome_5118_ = lean_ctor_get(v_a_5117_, 0);
if (lean_obj_tag(v_outcome_5118_) == 0)
{
uint8_t v_failed_5119_; 
v_failed_5119_ = lean_ctor_get_uint8(v_outcome_5118_, 0);
if (v_failed_5119_ == 0)
{
lean_object* v_checkedModules_5120_; lean_object* v___x_5122_; 
v_checkedModules_5120_ = lean_ctor_get(v_a_5117_, 1);
lean_inc(v_checkedModules_5120_);
lean_dec(v_a_5117_);
if (v_isShared_5102_ == 0)
{
lean_ctor_set(v___x_5101_, 0, v_checkedModules_5120_);
v___x_5122_ = v___x_5101_;
goto v_reusejp_5121_;
}
else
{
lean_object* v_reuseFailAlloc_5137_; 
v_reuseFailAlloc_5137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5137_, 0, v_checkedModules_5120_);
lean_ctor_set(v_reuseFailAlloc_5137_, 1, v_snd_5099_);
v___x_5122_ = v_reuseFailAlloc_5137_;
goto v_reusejp_5121_;
}
v_reusejp_5121_:
{
lean_object* v___x_5124_; 
if (v_isShared_5097_ == 0)
{
lean_ctor_set(v___x_5096_, 1, v___x_5122_);
lean_ctor_set(v___x_5096_, 0, v_codeQualityEntries_5111_);
v___x_5124_ = v___x_5096_;
goto v_reusejp_5123_;
}
else
{
lean_object* v_reuseFailAlloc_5136_; 
v_reuseFailAlloc_5136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5136_, 0, v_codeQualityEntries_5111_);
lean_ctor_set(v_reuseFailAlloc_5136_, 1, v___x_5122_);
v___x_5124_ = v_reuseFailAlloc_5136_;
goto v_reusejp_5123_;
}
v_reusejp_5123_:
{
lean_object* v___x_5126_; 
if (v_isShared_5093_ == 0)
{
lean_ctor_set(v___x_5092_, 1, v___x_5124_);
lean_ctor_set(v___x_5092_, 0, v_records_5110_);
v___x_5126_ = v___x_5092_;
goto v_reusejp_5125_;
}
else
{
lean_object* v_reuseFailAlloc_5135_; 
v_reuseFailAlloc_5135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5135_, 0, v_records_5110_);
lean_ctor_set(v_reuseFailAlloc_5135_, 1, v___x_5124_);
v___x_5126_ = v_reuseFailAlloc_5135_;
goto v_reusejp_5125_;
}
v_reusejp_5125_:
{
lean_object* v___x_5127_; lean_object* v___x_5129_; 
v___x_5127_ = lean_box(v_anyUnlocated_5109_);
if (v_isShared_5089_ == 0)
{
lean_ctor_set(v___x_5088_, 1, v___x_5126_);
lean_ctor_set(v___x_5088_, 0, v___x_5127_);
v___x_5129_ = v___x_5088_;
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
v___x_5130_ = lean_box(v_anyFailed_5108_);
if (v_isShared_5085_ == 0)
{
lean_ctor_set(v___x_5084_, 1, v___x_5129_);
lean_ctor_set(v___x_5084_, 0, v___x_5130_);
v___x_5132_ = v___x_5084_;
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
v_a_5067_ = v___x_5132_;
goto v___jp_5066_;
}
}
}
}
}
}
else
{
lean_object* v_checkedModules_5138_; lean_object* v___x_5140_; 
v_checkedModules_5138_ = lean_ctor_get(v_a_5117_, 1);
lean_inc(v_checkedModules_5138_);
lean_dec(v_a_5117_);
if (v_isShared_5102_ == 0)
{
lean_ctor_set(v___x_5101_, 0, v_checkedModules_5138_);
v___x_5140_ = v___x_5101_;
goto v_reusejp_5139_;
}
else
{
lean_object* v_reuseFailAlloc_5155_; 
v_reuseFailAlloc_5155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5155_, 0, v_checkedModules_5138_);
lean_ctor_set(v_reuseFailAlloc_5155_, 1, v_snd_5099_);
v___x_5140_ = v_reuseFailAlloc_5155_;
goto v_reusejp_5139_;
}
v_reusejp_5139_:
{
lean_object* v___x_5142_; 
if (v_isShared_5097_ == 0)
{
lean_ctor_set(v___x_5096_, 1, v___x_5140_);
lean_ctor_set(v___x_5096_, 0, v_codeQualityEntries_5111_);
v___x_5142_ = v___x_5096_;
goto v_reusejp_5141_;
}
else
{
lean_object* v_reuseFailAlloc_5154_; 
v_reuseFailAlloc_5154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5154_, 0, v_codeQualityEntries_5111_);
lean_ctor_set(v_reuseFailAlloc_5154_, 1, v___x_5140_);
v___x_5142_ = v_reuseFailAlloc_5154_;
goto v_reusejp_5141_;
}
v_reusejp_5141_:
{
lean_object* v___x_5144_; 
if (v_isShared_5093_ == 0)
{
lean_ctor_set(v___x_5092_, 1, v___x_5142_);
lean_ctor_set(v___x_5092_, 0, v_records_5110_);
v___x_5144_ = v___x_5092_;
goto v_reusejp_5143_;
}
else
{
lean_object* v_reuseFailAlloc_5153_; 
v_reuseFailAlloc_5153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5153_, 0, v_records_5110_);
lean_ctor_set(v_reuseFailAlloc_5153_, 1, v___x_5142_);
v___x_5144_ = v_reuseFailAlloc_5153_;
goto v_reusejp_5143_;
}
v_reusejp_5143_:
{
lean_object* v___x_5145_; lean_object* v___x_5147_; 
v___x_5145_ = lean_box(v_anyUnlocated_5109_);
if (v_isShared_5089_ == 0)
{
lean_ctor_set(v___x_5088_, 1, v___x_5144_);
lean_ctor_set(v___x_5088_, 0, v___x_5145_);
v___x_5147_ = v___x_5088_;
goto v_reusejp_5146_;
}
else
{
lean_object* v_reuseFailAlloc_5152_; 
v_reuseFailAlloc_5152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5152_, 0, v___x_5145_);
lean_ctor_set(v_reuseFailAlloc_5152_, 1, v___x_5144_);
v___x_5147_ = v_reuseFailAlloc_5152_;
goto v_reusejp_5146_;
}
v_reusejp_5146_:
{
lean_object* v___x_5148_; lean_object* v___x_5150_; 
v___x_5148_ = lean_box(v_anyUnlocated_5073_);
if (v_isShared_5085_ == 0)
{
lean_ctor_set(v___x_5084_, 1, v___x_5147_);
lean_ctor_set(v___x_5084_, 0, v___x_5148_);
v___x_5150_ = v___x_5084_;
goto v_reusejp_5149_;
}
else
{
lean_object* v_reuseFailAlloc_5151_; 
v_reuseFailAlloc_5151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5151_, 0, v___x_5148_);
lean_ctor_set(v_reuseFailAlloc_5151_, 1, v___x_5147_);
v___x_5150_ = v_reuseFailAlloc_5151_;
goto v_reusejp_5149_;
}
v_reusejp_5149_:
{
v_a_5067_ = v___x_5150_;
goto v___jp_5066_;
}
}
}
}
}
}
}
else
{
lean_object* v_checkedModules_5156_; lean_object* v_records_5157_; uint8_t v_unlocated_5158_; lean_object* v___x_5159_; 
lean_inc_ref(v_outcome_5118_);
v_checkedModules_5156_ = lean_ctor_get(v_a_5117_, 1);
lean_inc(v_checkedModules_5156_);
lean_dec(v_a_5117_);
v_records_5157_ = lean_ctor_get(v_outcome_5118_, 0);
lean_inc_ref(v_records_5157_);
v_unlocated_5158_ = lean_ctor_get_uint8(v_outcome_5118_, sizeof(void*)*1);
lean_dec_ref_known(v_outcome_5118_, 1);
v___x_5159_ = l_Array_append___redArg(v_records_5110_, v_records_5157_);
lean_dec_ref(v_records_5157_);
if (v_unlocated_5158_ == 0)
{
lean_object* v___x_5161_; 
if (v_isShared_5102_ == 0)
{
lean_ctor_set(v___x_5101_, 0, v_checkedModules_5156_);
v___x_5161_ = v___x_5101_;
goto v_reusejp_5160_;
}
else
{
lean_object* v_reuseFailAlloc_5176_; 
v_reuseFailAlloc_5176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5176_, 0, v_checkedModules_5156_);
lean_ctor_set(v_reuseFailAlloc_5176_, 1, v_snd_5099_);
v___x_5161_ = v_reuseFailAlloc_5176_;
goto v_reusejp_5160_;
}
v_reusejp_5160_:
{
lean_object* v___x_5163_; 
if (v_isShared_5097_ == 0)
{
lean_ctor_set(v___x_5096_, 1, v___x_5161_);
lean_ctor_set(v___x_5096_, 0, v_codeQualityEntries_5111_);
v___x_5163_ = v___x_5096_;
goto v_reusejp_5162_;
}
else
{
lean_object* v_reuseFailAlloc_5175_; 
v_reuseFailAlloc_5175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5175_, 0, v_codeQualityEntries_5111_);
lean_ctor_set(v_reuseFailAlloc_5175_, 1, v___x_5161_);
v___x_5163_ = v_reuseFailAlloc_5175_;
goto v_reusejp_5162_;
}
v_reusejp_5162_:
{
lean_object* v___x_5165_; 
if (v_isShared_5093_ == 0)
{
lean_ctor_set(v___x_5092_, 1, v___x_5163_);
lean_ctor_set(v___x_5092_, 0, v___x_5159_);
v___x_5165_ = v___x_5092_;
goto v_reusejp_5164_;
}
else
{
lean_object* v_reuseFailAlloc_5174_; 
v_reuseFailAlloc_5174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5174_, 0, v___x_5159_);
lean_ctor_set(v_reuseFailAlloc_5174_, 1, v___x_5163_);
v___x_5165_ = v_reuseFailAlloc_5174_;
goto v_reusejp_5164_;
}
v_reusejp_5164_:
{
lean_object* v___x_5166_; lean_object* v___x_5168_; 
v___x_5166_ = lean_box(v_anyUnlocated_5109_);
if (v_isShared_5089_ == 0)
{
lean_ctor_set(v___x_5088_, 1, v___x_5165_);
lean_ctor_set(v___x_5088_, 0, v___x_5166_);
v___x_5168_ = v___x_5088_;
goto v_reusejp_5167_;
}
else
{
lean_object* v_reuseFailAlloc_5173_; 
v_reuseFailAlloc_5173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5173_, 0, v___x_5166_);
lean_ctor_set(v_reuseFailAlloc_5173_, 1, v___x_5165_);
v___x_5168_ = v_reuseFailAlloc_5173_;
goto v_reusejp_5167_;
}
v_reusejp_5167_:
{
lean_object* v___x_5169_; lean_object* v___x_5171_; 
v___x_5169_ = lean_box(v_anyFailed_5108_);
if (v_isShared_5085_ == 0)
{
lean_ctor_set(v___x_5084_, 1, v___x_5168_);
lean_ctor_set(v___x_5084_, 0, v___x_5169_);
v___x_5171_ = v___x_5084_;
goto v_reusejp_5170_;
}
else
{
lean_object* v_reuseFailAlloc_5172_; 
v_reuseFailAlloc_5172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5172_, 0, v___x_5169_);
lean_ctor_set(v_reuseFailAlloc_5172_, 1, v___x_5168_);
v___x_5171_ = v_reuseFailAlloc_5172_;
goto v_reusejp_5170_;
}
v_reusejp_5170_:
{
v_a_5067_ = v___x_5171_;
goto v___jp_5066_;
}
}
}
}
}
}
else
{
lean_object* v___x_5178_; 
if (v_isShared_5102_ == 0)
{
lean_ctor_set(v___x_5101_, 0, v_checkedModules_5156_);
v___x_5178_ = v___x_5101_;
goto v_reusejp_5177_;
}
else
{
lean_object* v_reuseFailAlloc_5193_; 
v_reuseFailAlloc_5193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5193_, 0, v_checkedModules_5156_);
lean_ctor_set(v_reuseFailAlloc_5193_, 1, v_snd_5099_);
v___x_5178_ = v_reuseFailAlloc_5193_;
goto v_reusejp_5177_;
}
v_reusejp_5177_:
{
lean_object* v___x_5180_; 
if (v_isShared_5097_ == 0)
{
lean_ctor_set(v___x_5096_, 1, v___x_5178_);
lean_ctor_set(v___x_5096_, 0, v_codeQualityEntries_5111_);
v___x_5180_ = v___x_5096_;
goto v_reusejp_5179_;
}
else
{
lean_object* v_reuseFailAlloc_5192_; 
v_reuseFailAlloc_5192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5192_, 0, v_codeQualityEntries_5111_);
lean_ctor_set(v_reuseFailAlloc_5192_, 1, v___x_5178_);
v___x_5180_ = v_reuseFailAlloc_5192_;
goto v_reusejp_5179_;
}
v_reusejp_5179_:
{
lean_object* v___x_5182_; 
if (v_isShared_5093_ == 0)
{
lean_ctor_set(v___x_5092_, 1, v___x_5180_);
lean_ctor_set(v___x_5092_, 0, v___x_5159_);
v___x_5182_ = v___x_5092_;
goto v_reusejp_5181_;
}
else
{
lean_object* v_reuseFailAlloc_5191_; 
v_reuseFailAlloc_5191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5191_, 0, v___x_5159_);
lean_ctor_set(v_reuseFailAlloc_5191_, 1, v___x_5180_);
v___x_5182_ = v_reuseFailAlloc_5191_;
goto v_reusejp_5181_;
}
v_reusejp_5181_:
{
lean_object* v___x_5183_; lean_object* v___x_5185_; 
v___x_5183_ = lean_box(v_anyUnlocated_5073_);
if (v_isShared_5089_ == 0)
{
lean_ctor_set(v___x_5088_, 1, v___x_5182_);
lean_ctor_set(v___x_5088_, 0, v___x_5183_);
v___x_5185_ = v___x_5088_;
goto v_reusejp_5184_;
}
else
{
lean_object* v_reuseFailAlloc_5190_; 
v_reuseFailAlloc_5190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5190_, 0, v___x_5183_);
lean_ctor_set(v_reuseFailAlloc_5190_, 1, v___x_5182_);
v___x_5185_ = v_reuseFailAlloc_5190_;
goto v_reusejp_5184_;
}
v_reusejp_5184_:
{
lean_object* v___x_5186_; lean_object* v___x_5188_; 
v___x_5186_ = lean_box(v_anyFailed_5108_);
if (v_isShared_5085_ == 0)
{
lean_ctor_set(v___x_5084_, 1, v___x_5185_);
lean_ctor_set(v___x_5084_, 0, v___x_5186_);
v___x_5188_ = v___x_5084_;
goto v_reusejp_5187_;
}
else
{
lean_object* v_reuseFailAlloc_5189_; 
v_reuseFailAlloc_5189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5189_, 0, v___x_5186_);
lean_ctor_set(v_reuseFailAlloc_5189_, 1, v___x_5185_);
v___x_5188_ = v_reuseFailAlloc_5189_;
goto v_reusejp_5187_;
}
v_reusejp_5187_:
{
v_a_5067_ = v___x_5188_;
goto v___jp_5066_;
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
lean_object* v_a_5194_; lean_object* v___x_5196_; uint8_t v_isShared_5197_; uint8_t v_isSharedCheck_5201_; 
lean_dec_ref(v_codeQualityEntries_5111_);
lean_dec_ref(v_records_5110_);
lean_del_object(v___x_5101_);
lean_dec(v_snd_5099_);
lean_del_object(v___x_5096_);
lean_del_object(v___x_5092_);
lean_del_object(v___x_5088_);
lean_del_object(v___x_5084_);
lean_dec(v___x_5060_);
v_a_5194_ = lean_ctor_get(v___x_5116_, 0);
v_isSharedCheck_5201_ = !lean_is_exclusive(v___x_5116_);
if (v_isSharedCheck_5201_ == 0)
{
v___x_5196_ = v___x_5116_;
v_isShared_5197_ = v_isSharedCheck_5201_;
goto v_resetjp_5195_;
}
else
{
lean_inc(v_a_5194_);
lean_dec(v___x_5116_);
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
lean_object* v___x_5202_; lean_object* v_fst_5203_; lean_object* v_snd_5204_; lean_object* v___x_5206_; uint8_t v_isShared_5207_; uint8_t v_isSharedCheck_5256_; 
lean_del_object(v___x_5084_);
v___x_5202_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality(v_args_5059_, v___y_5106_, v___y_5107_, v_a_5104_, v_snd_5099_);
lean_dec_ref(v___y_5106_);
v_fst_5203_ = lean_ctor_get(v___x_5202_, 0);
v_snd_5204_ = lean_ctor_get(v___x_5202_, 1);
v_isSharedCheck_5256_ = !lean_is_exclusive(v___x_5202_);
if (v_isSharedCheck_5256_ == 0)
{
v___x_5206_ = v___x_5202_;
v_isShared_5207_ = v_isSharedCheck_5256_;
goto v_resetjp_5205_;
}
else
{
lean_inc(v_snd_5204_);
lean_inc(v_fst_5203_);
lean_dec(v___x_5202_);
v___x_5206_ = lean_box(0);
v_isShared_5207_ = v_isSharedCheck_5256_;
goto v_resetjp_5205_;
}
v_resetjp_5205_:
{
lean_object* v___x_5208_; lean_object* v___x_5209_; 
v___x_5208_ = l_Array_append___redArg(v_codeQualityEntries_5111_, v_fst_5203_);
lean_dec(v_fst_5203_);
lean_inc(v_a_5104_);
lean_inc(v___x_5060_);
v___x_5209_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(v___x_5060_, v___y_5107_, v_a_5104_);
if (lean_obj_tag(v___x_5209_) == 0)
{
lean_object* v_a_5210_; lean_object* v_entries_5211_; uint8_t v_failed_5212_; lean_object* v___x_5213_; 
v_a_5210_ = lean_ctor_get(v___x_5209_, 0);
lean_inc(v_a_5210_);
lean_dec_ref_known(v___x_5209_, 1);
v_entries_5211_ = lean_ctor_get(v_a_5210_, 0);
lean_inc_ref(v_entries_5211_);
v_failed_5212_ = lean_ctor_get_uint8(v_a_5210_, sizeof(void*)*1);
lean_dec(v_a_5210_);
v___x_5213_ = l_Array_append___redArg(v___x_5208_, v_entries_5211_);
lean_dec_ref(v_entries_5211_);
if (v_failed_5212_ == 0)
{
lean_object* v___x_5215_; 
if (v_isShared_5207_ == 0)
{
lean_ctor_set(v___x_5206_, 0, v_fst_5098_);
v___x_5215_ = v___x_5206_;
goto v_reusejp_5214_;
}
else
{
lean_object* v_reuseFailAlloc_5230_; 
v_reuseFailAlloc_5230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5230_, 0, v_fst_5098_);
lean_ctor_set(v_reuseFailAlloc_5230_, 1, v_snd_5204_);
v___x_5215_ = v_reuseFailAlloc_5230_;
goto v_reusejp_5214_;
}
v_reusejp_5214_:
{
lean_object* v___x_5217_; 
if (v_isShared_5102_ == 0)
{
lean_ctor_set(v___x_5101_, 1, v___x_5215_);
lean_ctor_set(v___x_5101_, 0, v___x_5213_);
v___x_5217_ = v___x_5101_;
goto v_reusejp_5216_;
}
else
{
lean_object* v_reuseFailAlloc_5229_; 
v_reuseFailAlloc_5229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5229_, 0, v___x_5213_);
lean_ctor_set(v_reuseFailAlloc_5229_, 1, v___x_5215_);
v___x_5217_ = v_reuseFailAlloc_5229_;
goto v_reusejp_5216_;
}
v_reusejp_5216_:
{
lean_object* v___x_5219_; 
if (v_isShared_5097_ == 0)
{
lean_ctor_set(v___x_5096_, 1, v___x_5217_);
lean_ctor_set(v___x_5096_, 0, v_records_5110_);
v___x_5219_ = v___x_5096_;
goto v_reusejp_5218_;
}
else
{
lean_object* v_reuseFailAlloc_5228_; 
v_reuseFailAlloc_5228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5228_, 0, v_records_5110_);
lean_ctor_set(v_reuseFailAlloc_5228_, 1, v___x_5217_);
v___x_5219_ = v_reuseFailAlloc_5228_;
goto v_reusejp_5218_;
}
v_reusejp_5218_:
{
lean_object* v___x_5220_; lean_object* v___x_5222_; 
v___x_5220_ = lean_box(v_anyUnlocated_5109_);
if (v_isShared_5093_ == 0)
{
lean_ctor_set(v___x_5092_, 1, v___x_5219_);
lean_ctor_set(v___x_5092_, 0, v___x_5220_);
v___x_5222_ = v___x_5092_;
goto v_reusejp_5221_;
}
else
{
lean_object* v_reuseFailAlloc_5227_; 
v_reuseFailAlloc_5227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5227_, 0, v___x_5220_);
lean_ctor_set(v_reuseFailAlloc_5227_, 1, v___x_5219_);
v___x_5222_ = v_reuseFailAlloc_5227_;
goto v_reusejp_5221_;
}
v_reusejp_5221_:
{
lean_object* v___x_5223_; lean_object* v___x_5225_; 
v___x_5223_ = lean_box(v_anyFailed_5108_);
if (v_isShared_5089_ == 0)
{
lean_ctor_set(v___x_5088_, 1, v___x_5222_);
lean_ctor_set(v___x_5088_, 0, v___x_5223_);
v___x_5225_ = v___x_5088_;
goto v_reusejp_5224_;
}
else
{
lean_object* v_reuseFailAlloc_5226_; 
v_reuseFailAlloc_5226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5226_, 0, v___x_5223_);
lean_ctor_set(v_reuseFailAlloc_5226_, 1, v___x_5222_);
v___x_5225_ = v_reuseFailAlloc_5226_;
goto v_reusejp_5224_;
}
v_reusejp_5224_:
{
v_a_5067_ = v___x_5225_;
goto v___jp_5066_;
}
}
}
}
}
}
else
{
lean_object* v___x_5232_; 
if (v_isShared_5207_ == 0)
{
lean_ctor_set(v___x_5206_, 0, v_fst_5098_);
v___x_5232_ = v___x_5206_;
goto v_reusejp_5231_;
}
else
{
lean_object* v_reuseFailAlloc_5247_; 
v_reuseFailAlloc_5247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5247_, 0, v_fst_5098_);
lean_ctor_set(v_reuseFailAlloc_5247_, 1, v_snd_5204_);
v___x_5232_ = v_reuseFailAlloc_5247_;
goto v_reusejp_5231_;
}
v_reusejp_5231_:
{
lean_object* v___x_5234_; 
if (v_isShared_5102_ == 0)
{
lean_ctor_set(v___x_5101_, 1, v___x_5232_);
lean_ctor_set(v___x_5101_, 0, v___x_5213_);
v___x_5234_ = v___x_5101_;
goto v_reusejp_5233_;
}
else
{
lean_object* v_reuseFailAlloc_5246_; 
v_reuseFailAlloc_5246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5246_, 0, v___x_5213_);
lean_ctor_set(v_reuseFailAlloc_5246_, 1, v___x_5232_);
v___x_5234_ = v_reuseFailAlloc_5246_;
goto v_reusejp_5233_;
}
v_reusejp_5233_:
{
lean_object* v___x_5236_; 
if (v_isShared_5097_ == 0)
{
lean_ctor_set(v___x_5096_, 1, v___x_5234_);
lean_ctor_set(v___x_5096_, 0, v_records_5110_);
v___x_5236_ = v___x_5096_;
goto v_reusejp_5235_;
}
else
{
lean_object* v_reuseFailAlloc_5245_; 
v_reuseFailAlloc_5245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5245_, 0, v_records_5110_);
lean_ctor_set(v_reuseFailAlloc_5245_, 1, v___x_5234_);
v___x_5236_ = v_reuseFailAlloc_5245_;
goto v_reusejp_5235_;
}
v_reusejp_5235_:
{
lean_object* v___x_5237_; lean_object* v___x_5239_; 
v___x_5237_ = lean_box(v_anyUnlocated_5109_);
if (v_isShared_5093_ == 0)
{
lean_ctor_set(v___x_5092_, 1, v___x_5236_);
lean_ctor_set(v___x_5092_, 0, v___x_5237_);
v___x_5239_ = v___x_5092_;
goto v_reusejp_5238_;
}
else
{
lean_object* v_reuseFailAlloc_5244_; 
v_reuseFailAlloc_5244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5244_, 0, v___x_5237_);
lean_ctor_set(v_reuseFailAlloc_5244_, 1, v___x_5236_);
v___x_5239_ = v_reuseFailAlloc_5244_;
goto v_reusejp_5238_;
}
v_reusejp_5238_:
{
lean_object* v___x_5240_; lean_object* v___x_5242_; 
v___x_5240_ = lean_box(v_anyUnlocated_5073_);
if (v_isShared_5089_ == 0)
{
lean_ctor_set(v___x_5088_, 1, v___x_5239_);
lean_ctor_set(v___x_5088_, 0, v___x_5240_);
v___x_5242_ = v___x_5088_;
goto v_reusejp_5241_;
}
else
{
lean_object* v_reuseFailAlloc_5243_; 
v_reuseFailAlloc_5243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5243_, 0, v___x_5240_);
lean_ctor_set(v_reuseFailAlloc_5243_, 1, v___x_5239_);
v___x_5242_ = v_reuseFailAlloc_5243_;
goto v_reusejp_5241_;
}
v_reusejp_5241_:
{
v_a_5067_ = v___x_5242_;
goto v___jp_5066_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5248_; lean_object* v___x_5250_; uint8_t v_isShared_5251_; uint8_t v_isSharedCheck_5255_; 
lean_dec_ref(v___x_5208_);
lean_del_object(v___x_5206_);
lean_dec(v_snd_5204_);
lean_dec_ref(v_records_5110_);
lean_del_object(v___x_5101_);
lean_dec(v_fst_5098_);
lean_del_object(v___x_5096_);
lean_del_object(v___x_5092_);
lean_del_object(v___x_5088_);
lean_dec(v___x_5060_);
v_a_5248_ = lean_ctor_get(v___x_5209_, 0);
v_isSharedCheck_5255_ = !lean_is_exclusive(v___x_5209_);
if (v_isSharedCheck_5255_ == 0)
{
v___x_5250_ = v___x_5209_;
v_isShared_5251_ = v_isSharedCheck_5255_;
goto v_resetjp_5249_;
}
else
{
lean_inc(v_a_5248_);
lean_dec(v___x_5209_);
v___x_5250_ = lean_box(0);
v_isShared_5251_ = v_isSharedCheck_5255_;
goto v_resetjp_5249_;
}
v_resetjp_5249_:
{
lean_object* v___x_5253_; 
if (v_isShared_5251_ == 0)
{
v___x_5253_ = v___x_5250_;
goto v_reusejp_5252_;
}
else
{
lean_object* v_reuseFailAlloc_5254_; 
v_reuseFailAlloc_5254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5254_, 0, v_a_5248_);
v___x_5253_ = v_reuseFailAlloc_5254_;
goto v_reusejp_5252_;
}
v_reusejp_5252_:
{
return v___x_5253_;
}
}
}
}
}
}
v___jp_5257_:
{
lean_object* v___x_5264_; 
lean_inc(v_a_5104_);
lean_inc_ref(v___y_5259_);
lean_inc(v___x_5060_);
lean_inc_ref(v___y_5258_);
v___x_5264_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(v_args_5059_, v___y_5258_, v___x_5060_, v___y_5259_, v_a_5104_);
if (lean_obj_tag(v___x_5264_) == 0)
{
lean_object* v_a_5265_; 
v_a_5265_ = lean_ctor_get(v___x_5264_, 0);
lean_inc(v_a_5265_);
lean_dec_ref_known(v___x_5264_, 1);
switch(lean_obj_tag(v_a_5265_))
{
case 0:
{
uint8_t v_failed_5266_; 
v_failed_5266_ = lean_ctor_get_uint8(v_a_5265_, 0);
lean_dec_ref_known(v_a_5265_, 0);
if (v_failed_5266_ == 0)
{
v___y_5106_ = v___y_5258_;
v___y_5107_ = v___y_5259_;
v_anyFailed_5108_ = v_anyFailed_5260_;
v_anyUnlocated_5109_ = v_anyUnlocated_5261_;
v_records_5110_ = v_records_5262_;
v_codeQualityEntries_5111_ = v_codeQualityEntries_5263_;
goto v___jp_5105_;
}
else
{
v___y_5106_ = v___y_5258_;
v___y_5107_ = v___y_5259_;
v_anyFailed_5108_ = v_anyUnlocated_5073_;
v_anyUnlocated_5109_ = v_anyUnlocated_5261_;
v_records_5110_ = v_records_5262_;
v_codeQualityEntries_5111_ = v_codeQualityEntries_5263_;
goto v___jp_5105_;
}
}
case 1:
{
lean_object* v_records_5267_; uint8_t v_unlocated_5268_; lean_object* v___x_5269_; 
v_records_5267_ = lean_ctor_get(v_a_5265_, 0);
lean_inc_ref(v_records_5267_);
v_unlocated_5268_ = lean_ctor_get_uint8(v_a_5265_, sizeof(void*)*1);
lean_dec_ref_known(v_a_5265_, 1);
v___x_5269_ = l_Array_append___redArg(v_records_5262_, v_records_5267_);
lean_dec_ref(v_records_5267_);
if (v_unlocated_5268_ == 0)
{
v___y_5106_ = v___y_5258_;
v___y_5107_ = v___y_5259_;
v_anyFailed_5108_ = v_anyFailed_5260_;
v_anyUnlocated_5109_ = v_anyUnlocated_5261_;
v_records_5110_ = v___x_5269_;
v_codeQualityEntries_5111_ = v_codeQualityEntries_5263_;
goto v___jp_5105_;
}
else
{
v___y_5106_ = v___y_5258_;
v___y_5107_ = v___y_5259_;
v_anyFailed_5108_ = v_anyFailed_5260_;
v_anyUnlocated_5109_ = v_anyUnlocated_5073_;
v_records_5110_ = v___x_5269_;
v_codeQualityEntries_5111_ = v_codeQualityEntries_5263_;
goto v___jp_5105_;
}
}
default: 
{
lean_object* v_entries_5270_; lean_object* v___x_5271_; 
v_entries_5270_ = lean_ctor_get(v_a_5265_, 0);
lean_inc_ref(v_entries_5270_);
lean_dec_ref_known(v_a_5265_, 1);
v___x_5271_ = l_Array_append___redArg(v_codeQualityEntries_5263_, v_entries_5270_);
lean_dec_ref(v_entries_5270_);
v___y_5106_ = v___y_5258_;
v___y_5107_ = v___y_5259_;
v_anyFailed_5108_ = v_anyFailed_5260_;
v_anyUnlocated_5109_ = v_anyUnlocated_5261_;
v_records_5110_ = v_records_5262_;
v_codeQualityEntries_5111_ = v___x_5271_;
goto v___jp_5105_;
}
}
}
else
{
lean_object* v_a_5272_; lean_object* v___x_5274_; uint8_t v_isShared_5275_; uint8_t v_isSharedCheck_5279_; 
lean_dec_ref(v_codeQualityEntries_5263_);
lean_dec_ref(v_records_5262_);
lean_dec_ref(v___y_5259_);
lean_dec_ref(v___y_5258_);
lean_del_object(v___x_5101_);
lean_dec(v_snd_5099_);
lean_dec(v_fst_5098_);
lean_del_object(v___x_5096_);
lean_del_object(v___x_5092_);
lean_del_object(v___x_5088_);
lean_del_object(v___x_5084_);
lean_dec(v___x_5060_);
v_a_5272_ = lean_ctor_get(v___x_5264_, 0);
v_isSharedCheck_5279_ = !lean_is_exclusive(v___x_5264_);
if (v_isSharedCheck_5279_ == 0)
{
v___x_5274_ = v___x_5264_;
v_isShared_5275_ = v_isSharedCheck_5279_;
goto v_resetjp_5273_;
}
else
{
lean_inc(v_a_5272_);
lean_dec(v___x_5264_);
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
v___jp_5280_:
{
lean_object* v___x_5283_; lean_object* v_toEnvExtension_5284_; lean_object* v_asyncMode_5285_; lean_object* v___x_5286_; lean_object* v___x_5287_; lean_object* v_merged_5288_; lean_object* v___x_5290_; uint8_t v_isShared_5291_; uint8_t v_isSharedCheck_5319_; 
v___x_5283_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_5284_ = lean_ctor_get(v___x_5283_, 0);
v_asyncMode_5285_ = lean_ctor_get(v_toEnvExtension_5284_, 2);
v___x_5286_ = lean_box(0);
lean_inc_ref(v___y_5281_);
v___x_5287_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_5103_, v___x_5283_, v___y_5281_, v_asyncMode_5285_, v___x_5286_, v_anyFailed_5072_);
v_merged_5288_ = lean_ctor_get(v___x_5287_, 0);
v_isSharedCheck_5319_ = !lean_is_exclusive(v___x_5287_);
if (v_isSharedCheck_5319_ == 0)
{
lean_object* v_unused_5320_; 
v_unused_5320_ = lean_ctor_get(v___x_5287_, 1);
lean_dec(v_unused_5320_);
v___x_5290_ = v___x_5287_;
v_isShared_5291_ = v_isSharedCheck_5319_;
goto v_resetjp_5289_;
}
else
{
lean_inc(v_merged_5288_);
lean_dec(v___x_5287_);
v___x_5290_ = lean_box(0);
v_isShared_5291_ = v_isSharedCheck_5319_;
goto v_resetjp_5289_;
}
v_resetjp_5289_:
{
lean_object* v___x_5293_; 
if (v_isShared_5291_ == 0)
{
lean_ctor_set(v___x_5290_, 1, v_merged_5288_);
lean_ctor_set(v___x_5290_, 0, v___y_5282_);
v___x_5293_ = v___x_5290_;
goto v_reusejp_5292_;
}
else
{
lean_object* v_reuseFailAlloc_5318_; 
v_reuseFailAlloc_5318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5318_, 0, v___y_5282_);
lean_ctor_set(v_reuseFailAlloc_5318_, 1, v_merged_5288_);
v___x_5293_ = v_reuseFailAlloc_5318_;
goto v_reusejp_5292_;
}
v_reusejp_5292_:
{
lean_object* v___x_5294_; 
v___x_5294_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(v_args_5059_, v___x_5293_, v___y_5281_, v_a_5104_);
if (lean_obj_tag(v___x_5294_) == 0)
{
lean_object* v_a_5295_; 
v_a_5295_ = lean_ctor_get(v___x_5294_, 0);
lean_inc(v_a_5295_);
lean_dec_ref_known(v___x_5294_, 1);
switch(lean_obj_tag(v_a_5295_))
{
case 0:
{
uint8_t v___x_5296_; 
v___x_5296_ = lean_unbox(v_fst_5082_);
lean_dec(v_fst_5082_);
if (v___x_5296_ == 0)
{
uint8_t v_failed_5297_; uint8_t v___x_5298_; 
v_failed_5297_ = lean_ctor_get_uint8(v_a_5295_, 0);
lean_dec_ref_known(v_a_5295_, 0);
v___x_5298_ = lean_unbox(v_fst_5086_);
lean_dec(v_fst_5086_);
v___y_5258_ = v___x_5293_;
v___y_5259_ = v___y_5281_;
v_anyFailed_5260_ = v_failed_5297_;
v_anyUnlocated_5261_ = v___x_5298_;
v_records_5262_ = v_fst_5090_;
v_codeQualityEntries_5263_ = v_fst_5094_;
goto v___jp_5257_;
}
else
{
uint8_t v___x_5299_; 
lean_dec_ref_known(v_a_5295_, 0);
v___x_5299_ = lean_unbox(v_fst_5086_);
lean_dec(v_fst_5086_);
v___y_5258_ = v___x_5293_;
v___y_5259_ = v___y_5281_;
v_anyFailed_5260_ = v_anyUnlocated_5073_;
v_anyUnlocated_5261_ = v___x_5299_;
v_records_5262_ = v_fst_5090_;
v_codeQualityEntries_5263_ = v_fst_5094_;
goto v___jp_5257_;
}
}
case 1:
{
lean_object* v_records_5300_; uint8_t v_unlocated_5301_; lean_object* v___x_5302_; 
v_records_5300_ = lean_ctor_get(v_a_5295_, 0);
lean_inc_ref(v_records_5300_);
v_unlocated_5301_ = lean_ctor_get_uint8(v_a_5295_, sizeof(void*)*1);
lean_dec_ref_known(v_a_5295_, 1);
v___x_5302_ = l_Array_append___redArg(v_fst_5090_, v_records_5300_);
lean_dec_ref(v_records_5300_);
if (v_unlocated_5301_ == 0)
{
uint8_t v___x_5303_; uint8_t v___x_5304_; 
v___x_5303_ = lean_unbox(v_fst_5082_);
lean_dec(v_fst_5082_);
v___x_5304_ = lean_unbox(v_fst_5086_);
lean_dec(v_fst_5086_);
v___y_5258_ = v___x_5293_;
v___y_5259_ = v___y_5281_;
v_anyFailed_5260_ = v___x_5303_;
v_anyUnlocated_5261_ = v___x_5304_;
v_records_5262_ = v___x_5302_;
v_codeQualityEntries_5263_ = v_fst_5094_;
goto v___jp_5257_;
}
else
{
uint8_t v___x_5305_; 
lean_dec(v_fst_5086_);
v___x_5305_ = lean_unbox(v_fst_5082_);
lean_dec(v_fst_5082_);
v___y_5258_ = v___x_5293_;
v___y_5259_ = v___y_5281_;
v_anyFailed_5260_ = v___x_5305_;
v_anyUnlocated_5261_ = v_anyUnlocated_5073_;
v_records_5262_ = v___x_5302_;
v_codeQualityEntries_5263_ = v_fst_5094_;
goto v___jp_5257_;
}
}
default: 
{
lean_object* v_entries_5306_; lean_object* v___x_5307_; uint8_t v___x_5308_; uint8_t v___x_5309_; 
v_entries_5306_ = lean_ctor_get(v_a_5295_, 0);
lean_inc_ref(v_entries_5306_);
lean_dec_ref_known(v_a_5295_, 1);
v___x_5307_ = l_Array_append___redArg(v_fst_5094_, v_entries_5306_);
lean_dec_ref(v_entries_5306_);
v___x_5308_ = lean_unbox(v_fst_5082_);
lean_dec(v_fst_5082_);
v___x_5309_ = lean_unbox(v_fst_5086_);
lean_dec(v_fst_5086_);
v___y_5258_ = v___x_5293_;
v___y_5259_ = v___y_5281_;
v_anyFailed_5260_ = v___x_5308_;
v_anyUnlocated_5261_ = v___x_5309_;
v_records_5262_ = v_fst_5090_;
v_codeQualityEntries_5263_ = v___x_5307_;
goto v___jp_5257_;
}
}
}
else
{
lean_object* v_a_5310_; lean_object* v___x_5312_; uint8_t v_isShared_5313_; uint8_t v_isSharedCheck_5317_; 
lean_dec_ref(v___x_5293_);
lean_dec_ref(v___y_5281_);
lean_del_object(v___x_5101_);
lean_dec(v_snd_5099_);
lean_dec(v_fst_5098_);
lean_del_object(v___x_5096_);
lean_dec(v_fst_5094_);
lean_del_object(v___x_5092_);
lean_dec(v_fst_5090_);
lean_del_object(v___x_5088_);
lean_dec(v_fst_5086_);
lean_del_object(v___x_5084_);
lean_dec(v_fst_5082_);
lean_dec(v___x_5060_);
v_a_5310_ = lean_ctor_get(v___x_5294_, 0);
v_isSharedCheck_5317_ = !lean_is_exclusive(v___x_5294_);
if (v_isSharedCheck_5317_ == 0)
{
v___x_5312_ = v___x_5294_;
v_isShared_5313_ = v_isSharedCheck_5317_;
goto v_resetjp_5311_;
}
else
{
lean_inc(v_a_5310_);
lean_dec(v___x_5294_);
v___x_5312_ = lean_box(0);
v_isShared_5313_ = v_isSharedCheck_5317_;
goto v_resetjp_5311_;
}
v_resetjp_5311_:
{
lean_object* v___x_5315_; 
if (v_isShared_5313_ == 0)
{
v___x_5315_ = v___x_5312_;
goto v_reusejp_5314_;
}
else
{
lean_object* v_reuseFailAlloc_5316_; 
v_reuseFailAlloc_5316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5316_, 0, v_a_5310_);
v___x_5315_ = v_reuseFailAlloc_5316_;
goto v_reusejp_5314_;
}
v_reusejp_5314_:
{
return v___x_5315_;
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
v___jp_5066_:
{
size_t v___x_5068_; size_t v___x_5069_; 
v___x_5068_ = ((size_t)1ULL);
v___x_5069_ = lean_usize_add(v_i_5063_, v___x_5068_);
v_i_5063_ = v___x_5069_;
v_b_5064_ = v_a_5067_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_5057_ = stack[0].m_obj;
lean_object* v_checkImports_5058_ = stack[1].m_obj;
lean_object* v_args_5059_ = stack[2].m_obj;
lean_object* v___x_5060_ = stack[3].m_obj;
lean_object* v_as_5061_ = stack[4].m_obj;
size_t v_sz_5062_ = stack[5].m_num;
size_t v_i_5063_ = stack[6].m_num;
lean_object* v_b_5064_ = stack[7].m_obj;
lean_object* v_res_5397_;
v_res_5397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(v___x_5057_, v_checkImports_5058_, v_args_5059_, v___x_5060_, v_as_5061_, v_sz_5062_, v_i_5063_, v_b_5064_);
stack->m_obj
 = v_res_5397_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___boxed(lean_object* v___x_5398_, lean_object* v_checkImports_5399_, lean_object* v_args_5400_, lean_object* v___x_5401_, lean_object* v_as_5402_, lean_object* v_sz_5403_, lean_object* v_i_5404_, lean_object* v_b_5405_, lean_object* v___y_5406_){
_start:
{
size_t v_sz_boxed_5407_; size_t v_i_boxed_5408_; lean_object* v_res_5409_; 
v_sz_boxed_5407_ = lean_unbox_usize(v_sz_5403_);
lean_dec(v_sz_5403_);
v_i_boxed_5408_ = lean_unbox_usize(v_i_5404_);
lean_dec(v_i_5404_);
v_res_5409_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(v___x_5398_, v_checkImports_5399_, v_args_5400_, v___x_5401_, v_as_5402_, v_sz_boxed_5407_, v_i_boxed_5408_, v_b_5405_);
lean_dec_ref(v_as_5402_);
lean_dec_ref(v_args_5400_);
lean_dec_ref(v_checkImports_5399_);
lean_dec(v___x_5398_);
return v_res_5409_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__0(void){
_start:
{
lean_object* v___x_5410_; lean_object* v___x_5411_; 
v___x_5410_ = l_Lean_NameSet_empty;
v___x_5411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5411_, 0, v___x_5410_);
lean_ctor_set(v___x_5411_, 1, v___x_5410_);
return v___x_5411_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__1(void){
_start:
{
lean_object* v___x_5412_; lean_object* v___x_5413_; lean_object* v___x_5414_; 
v___x_5412_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__0, &l_Lake_BuiltinLint_run___closed__0_once, _init_l_Lake_BuiltinLint_run___closed__0);
v___x_5413_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_5414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5414_, 0, v___x_5413_);
lean_ctor_set(v___x_5414_, 1, v___x_5412_);
return v___x_5414_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__2(void){
_start:
{
lean_object* v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; 
v___x_5415_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__1, &l_Lake_BuiltinLint_run___closed__1_once, _init_l_Lake_BuiltinLint_run___closed__1);
v___x_5416_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_5417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5417_, 0, v___x_5416_);
lean_ctor_set(v___x_5417_, 1, v___x_5415_);
return v___x_5417_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__1(void){
_start:
{
uint32_t v___x_5419_; lean_object* v___x_5420_; 
v___x_5419_ = 0;
v___x_5420_ = lean_box_uint32(v___x_5419_);
return v___x_5420_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__2(void){
_start:
{
uint32_t v___x_5421_; lean_object* v___x_5422_; 
v___x_5421_ = 1;
v___x_5422_ = lean_box_uint32(v___x_5421_);
return v___x_5422_;
}
}
lean_object* l_Lake_BuiltinLint_run(lean_object* v_args_5423_){
_start:
{
lean_object* v_mods_5425_; uint8_t v_mode_5426_; lean_object* v_checks_5427_; lean_object* v_srcSearchPath_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; uint8_t v_anyFailed_5431_; 
v_mods_5425_ = lean_ctor_get(v_args_5423_, 1);
lean_inc_ref(v_mods_5425_);
v_mode_5426_ = lean_ctor_get_uint8(v_args_5423_, sizeof(void*)*4 + 1);
v_checks_5427_ = lean_ctor_get(v_args_5423_, 2);
v_srcSearchPath_5428_ = lean_ctor_get(v_args_5423_, 3);
v___x_5429_ = lean_array_get_size(v_mods_5425_);
v___x_5430_ = lean_unsigned_to_nat(0u);
v_anyFailed_5431_ = lean_nat_dec_eq(v___x_5429_, v___x_5430_);
if (v_anyFailed_5431_ == 0)
{
size_t v_sz_5432_; size_t v___x_5433_; lean_object* v_checkImports_5434_; lean_object* v___x_5435_; 
v_sz_5432_ = lean_array_size(v_checks_5427_);
v___x_5433_ = ((size_t)0ULL);
lean_inc_ref(v_checks_5427_);
v_checkImports_5434_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(v___x_5429_, v_sz_5432_, v___x_5433_, v_checks_5427_);
v___x_5435_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_5435_) == 0)
{
lean_object* v_a_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; lean_object* v___x_5440_; lean_object* v___x_5441_; lean_object* v___x_5442_; size_t v_sz_5443_; lean_object* v___x_5444_; 
v_a_5436_ = lean_ctor_get(v___x_5435_, 0);
lean_inc(v_a_5436_);
lean_dec_ref_known(v___x_5435_, 1);
lean_inc(v_srcSearchPath_5428_);
v___x_5437_ = l_List_appendTR___redArg(v_srcSearchPath_5428_, v_a_5436_);
v___x_5438_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__2, &l_Lake_BuiltinLint_run___closed__2_once, _init_l_Lake_BuiltinLint_run___closed__2);
v___x_5439_ = lean_box(v_anyFailed_5431_);
v___x_5440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5440_, 0, v___x_5439_);
lean_ctor_set(v___x_5440_, 1, v___x_5438_);
v___x_5441_ = lean_box(v_anyFailed_5431_);
v___x_5442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5442_, 0, v___x_5441_);
lean_ctor_set(v___x_5442_, 1, v___x_5440_);
v_sz_5443_ = lean_array_size(v_mods_5425_);
v___x_5444_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(v___x_5429_, v_checkImports_5434_, v_args_5423_, v___x_5437_, v_mods_5425_, v_sz_5443_, v___x_5433_, v___x_5442_);
lean_dec_ref(v_mods_5425_);
lean_dec_ref(v_args_5423_);
lean_dec_ref(v_checkImports_5434_);
if (lean_obj_tag(v___x_5444_) == 0)
{
lean_object* v_a_5445_; lean_object* v___x_5447_; uint8_t v_isShared_5448_; uint8_t v_isSharedCheck_5516_; 
v_a_5445_ = lean_ctor_get(v___x_5444_, 0);
v_isSharedCheck_5516_ = !lean_is_exclusive(v___x_5444_);
if (v_isSharedCheck_5516_ == 0)
{
v___x_5447_ = v___x_5444_;
v_isShared_5448_ = v_isSharedCheck_5516_;
goto v_resetjp_5446_;
}
else
{
lean_inc(v_a_5445_);
lean_dec(v___x_5444_);
v___x_5447_ = lean_box(0);
v_isShared_5448_ = v_isSharedCheck_5516_;
goto v_resetjp_5446_;
}
v_resetjp_5446_:
{
switch(v_mode_5426_)
{
case 0:
{
lean_object* v_fst_5449_; uint8_t v___x_5450_; 
v_fst_5449_ = lean_ctor_get(v_a_5445_, 0);
lean_inc(v_fst_5449_);
lean_dec(v_a_5445_);
v___x_5450_ = lean_unbox(v_fst_5449_);
lean_dec(v_fst_5449_);
if (v___x_5450_ == 0)
{
lean_object* v___x_5451_; lean_object* v___x_5453_; 
v___x_5451_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5448_ == 0)
{
lean_ctor_set(v___x_5447_, 0, v___x_5451_);
v___x_5453_ = v___x_5447_;
goto v_reusejp_5452_;
}
else
{
lean_object* v_reuseFailAlloc_5454_; 
v_reuseFailAlloc_5454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5454_, 0, v___x_5451_);
v___x_5453_ = v_reuseFailAlloc_5454_;
goto v_reusejp_5452_;
}
v_reusejp_5452_:
{
return v___x_5453_;
}
}
else
{
lean_object* v___x_5455_; lean_object* v___x_5457_; 
v___x_5455_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5448_ == 0)
{
lean_ctor_set(v___x_5447_, 0, v___x_5455_);
v___x_5457_ = v___x_5447_;
goto v_reusejp_5456_;
}
else
{
lean_object* v_reuseFailAlloc_5458_; 
v_reuseFailAlloc_5458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5458_, 0, v___x_5455_);
v___x_5457_ = v_reuseFailAlloc_5458_;
goto v_reusejp_5456_;
}
v_reusejp_5456_:
{
return v___x_5457_;
}
}
}
case 1:
{
lean_object* v_snd_5459_; lean_object* v_snd_5460_; lean_object* v_fst_5461_; lean_object* v_fst_5462_; lean_object* v___x_5463_; 
v_snd_5459_ = lean_ctor_get(v_a_5445_, 1);
lean_inc(v_snd_5459_);
lean_del_object(v___x_5447_);
lean_dec(v_a_5445_);
v_snd_5460_ = lean_ctor_get(v_snd_5459_, 1);
lean_inc(v_snd_5460_);
v_fst_5461_ = lean_ctor_get(v_snd_5459_, 0);
lean_inc(v_fst_5461_);
lean_dec(v_snd_5459_);
v_fst_5462_ = lean_ctor_get(v_snd_5460_, 0);
lean_inc(v_fst_5462_);
lean_dec(v_snd_5460_);
v___x_5463_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(v_fst_5462_);
lean_dec(v_fst_5462_);
if (lean_obj_tag(v___x_5463_) == 0)
{
lean_object* v___x_5465_; uint8_t v_isShared_5466_; uint8_t v_isSharedCheck_5476_; 
v_isSharedCheck_5476_ = !lean_is_exclusive(v___x_5463_);
if (v_isSharedCheck_5476_ == 0)
{
lean_object* v_unused_5477_; 
v_unused_5477_ = lean_ctor_get(v___x_5463_, 0);
lean_dec(v_unused_5477_);
v___x_5465_ = v___x_5463_;
v_isShared_5466_ = v_isSharedCheck_5476_;
goto v_resetjp_5464_;
}
else
{
lean_dec(v___x_5463_);
v___x_5465_ = lean_box(0);
v_isShared_5466_ = v_isSharedCheck_5476_;
goto v_resetjp_5464_;
}
v_resetjp_5464_:
{
uint8_t v___x_5467_; 
v___x_5467_ = lean_unbox(v_fst_5461_);
lean_dec(v_fst_5461_);
if (v___x_5467_ == 0)
{
lean_object* v___x_5468_; lean_object* v___x_5470_; 
v___x_5468_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5466_ == 0)
{
lean_ctor_set(v___x_5465_, 0, v___x_5468_);
v___x_5470_ = v___x_5465_;
goto v_reusejp_5469_;
}
else
{
lean_object* v_reuseFailAlloc_5471_; 
v_reuseFailAlloc_5471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5471_, 0, v___x_5468_);
v___x_5470_ = v_reuseFailAlloc_5471_;
goto v_reusejp_5469_;
}
v_reusejp_5469_:
{
return v___x_5470_;
}
}
else
{
lean_object* v___x_5472_; lean_object* v___x_5474_; 
v___x_5472_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5466_ == 0)
{
lean_ctor_set(v___x_5465_, 0, v___x_5472_);
v___x_5474_ = v___x_5465_;
goto v_reusejp_5473_;
}
else
{
lean_object* v_reuseFailAlloc_5475_; 
v_reuseFailAlloc_5475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5475_, 0, v___x_5472_);
v___x_5474_ = v_reuseFailAlloc_5475_;
goto v_reusejp_5473_;
}
v_reusejp_5473_:
{
return v___x_5474_;
}
}
}
}
else
{
lean_object* v_a_5478_; lean_object* v___x_5480_; uint8_t v_isShared_5481_; uint8_t v_isSharedCheck_5485_; 
lean_dec(v_fst_5461_);
v_a_5478_ = lean_ctor_get(v___x_5463_, 0);
v_isSharedCheck_5485_ = !lean_is_exclusive(v___x_5463_);
if (v_isSharedCheck_5485_ == 0)
{
v___x_5480_ = v___x_5463_;
v_isShared_5481_ = v_isSharedCheck_5485_;
goto v_resetjp_5479_;
}
else
{
lean_inc(v_a_5478_);
lean_dec(v___x_5463_);
v___x_5480_ = lean_box(0);
v_isShared_5481_ = v_isSharedCheck_5485_;
goto v_resetjp_5479_;
}
v_resetjp_5479_:
{
lean_object* v___x_5483_; 
if (v_isShared_5481_ == 0)
{
v___x_5483_ = v___x_5480_;
goto v_reusejp_5482_;
}
else
{
lean_object* v_reuseFailAlloc_5484_; 
v_reuseFailAlloc_5484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5484_, 0, v_a_5478_);
v___x_5483_ = v_reuseFailAlloc_5484_;
goto v_reusejp_5482_;
}
v_reusejp_5482_:
{
return v___x_5483_;
}
}
}
}
default: 
{
lean_object* v_snd_5486_; lean_object* v_snd_5487_; lean_object* v_snd_5488_; lean_object* v_fst_5489_; lean_object* v_fst_5490_; lean_object* v___x_5491_; size_t v_sz_5492_; lean_object* v___x_5493_; 
v_snd_5486_ = lean_ctor_get(v_a_5445_, 1);
lean_del_object(v___x_5447_);
v_snd_5487_ = lean_ctor_get(v_snd_5486_, 1);
v_snd_5488_ = lean_ctor_get(v_snd_5487_, 1);
lean_inc(v_snd_5488_);
v_fst_5489_ = lean_ctor_get(v_a_5445_, 0);
lean_inc(v_fst_5489_);
lean_dec(v_a_5445_);
v_fst_5490_ = lean_ctor_get(v_snd_5488_, 0);
lean_inc(v_fst_5490_);
lean_dec(v_snd_5488_);
v___x_5491_ = lean_box(0);
v_sz_5492_ = lean_array_size(v_fst_5490_);
v___x_5493_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(v_fst_5490_, v_sz_5492_, v___x_5433_, v___x_5491_);
lean_dec(v_fst_5490_);
if (lean_obj_tag(v___x_5493_) == 0)
{
lean_object* v___x_5495_; uint8_t v_isShared_5496_; uint8_t v_isSharedCheck_5506_; 
v_isSharedCheck_5506_ = !lean_is_exclusive(v___x_5493_);
if (v_isSharedCheck_5506_ == 0)
{
lean_object* v_unused_5507_; 
v_unused_5507_ = lean_ctor_get(v___x_5493_, 0);
lean_dec(v_unused_5507_);
v___x_5495_ = v___x_5493_;
v_isShared_5496_ = v_isSharedCheck_5506_;
goto v_resetjp_5494_;
}
else
{
lean_dec(v___x_5493_);
v___x_5495_ = lean_box(0);
v_isShared_5496_ = v_isSharedCheck_5506_;
goto v_resetjp_5494_;
}
v_resetjp_5494_:
{
uint8_t v___x_5497_; 
v___x_5497_ = lean_unbox(v_fst_5489_);
lean_dec(v_fst_5489_);
if (v___x_5497_ == 0)
{
lean_object* v___x_5498_; lean_object* v___x_5500_; 
v___x_5498_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5496_ == 0)
{
lean_ctor_set(v___x_5495_, 0, v___x_5498_);
v___x_5500_ = v___x_5495_;
goto v_reusejp_5499_;
}
else
{
lean_object* v_reuseFailAlloc_5501_; 
v_reuseFailAlloc_5501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5501_, 0, v___x_5498_);
v___x_5500_ = v_reuseFailAlloc_5501_;
goto v_reusejp_5499_;
}
v_reusejp_5499_:
{
return v___x_5500_;
}
}
else
{
lean_object* v___x_5502_; lean_object* v___x_5504_; 
v___x_5502_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5496_ == 0)
{
lean_ctor_set(v___x_5495_, 0, v___x_5502_);
v___x_5504_ = v___x_5495_;
goto v_reusejp_5503_;
}
else
{
lean_object* v_reuseFailAlloc_5505_; 
v_reuseFailAlloc_5505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5505_, 0, v___x_5502_);
v___x_5504_ = v_reuseFailAlloc_5505_;
goto v_reusejp_5503_;
}
v_reusejp_5503_:
{
return v___x_5504_;
}
}
}
}
else
{
lean_object* v_a_5508_; lean_object* v___x_5510_; uint8_t v_isShared_5511_; uint8_t v_isSharedCheck_5515_; 
lean_dec(v_fst_5489_);
v_a_5508_ = lean_ctor_get(v___x_5493_, 0);
v_isSharedCheck_5515_ = !lean_is_exclusive(v___x_5493_);
if (v_isSharedCheck_5515_ == 0)
{
v___x_5510_ = v___x_5493_;
v_isShared_5511_ = v_isSharedCheck_5515_;
goto v_resetjp_5509_;
}
else
{
lean_inc(v_a_5508_);
lean_dec(v___x_5493_);
v___x_5510_ = lean_box(0);
v_isShared_5511_ = v_isSharedCheck_5515_;
goto v_resetjp_5509_;
}
v_resetjp_5509_:
{
lean_object* v___x_5513_; 
if (v_isShared_5511_ == 0)
{
v___x_5513_ = v___x_5510_;
goto v_reusejp_5512_;
}
else
{
lean_object* v_reuseFailAlloc_5514_; 
v_reuseFailAlloc_5514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5514_, 0, v_a_5508_);
v___x_5513_ = v_reuseFailAlloc_5514_;
goto v_reusejp_5512_;
}
v_reusejp_5512_:
{
return v___x_5513_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5517_; lean_object* v___x_5519_; uint8_t v_isShared_5520_; uint8_t v_isSharedCheck_5524_; 
v_a_5517_ = lean_ctor_get(v___x_5444_, 0);
v_isSharedCheck_5524_ = !lean_is_exclusive(v___x_5444_);
if (v_isSharedCheck_5524_ == 0)
{
v___x_5519_ = v___x_5444_;
v_isShared_5520_ = v_isSharedCheck_5524_;
goto v_resetjp_5518_;
}
else
{
lean_inc(v_a_5517_);
lean_dec(v___x_5444_);
v___x_5519_ = lean_box(0);
v_isShared_5520_ = v_isSharedCheck_5524_;
goto v_resetjp_5518_;
}
v_resetjp_5518_:
{
lean_object* v___x_5522_; 
if (v_isShared_5520_ == 0)
{
v___x_5522_ = v___x_5519_;
goto v_reusejp_5521_;
}
else
{
lean_object* v_reuseFailAlloc_5523_; 
v_reuseFailAlloc_5523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5523_, 0, v_a_5517_);
v___x_5522_ = v_reuseFailAlloc_5523_;
goto v_reusejp_5521_;
}
v_reusejp_5521_:
{
return v___x_5522_;
}
}
}
}
else
{
lean_object* v_a_5525_; lean_object* v___x_5527_; uint8_t v_isShared_5528_; uint8_t v_isSharedCheck_5532_; 
lean_dec_ref(v_checkImports_5434_);
lean_dec_ref(v_mods_5425_);
lean_dec_ref(v_args_5423_);
v_a_5525_ = lean_ctor_get(v___x_5435_, 0);
v_isSharedCheck_5532_ = !lean_is_exclusive(v___x_5435_);
if (v_isSharedCheck_5532_ == 0)
{
v___x_5527_ = v___x_5435_;
v_isShared_5528_ = v_isSharedCheck_5532_;
goto v_resetjp_5526_;
}
else
{
lean_inc(v_a_5525_);
lean_dec(v___x_5435_);
v___x_5527_ = lean_box(0);
v_isShared_5528_ = v_isSharedCheck_5532_;
goto v_resetjp_5526_;
}
v_resetjp_5526_:
{
lean_object* v___x_5530_; 
if (v_isShared_5528_ == 0)
{
v___x_5530_ = v___x_5527_;
goto v_reusejp_5529_;
}
else
{
lean_object* v_reuseFailAlloc_5531_; 
v_reuseFailAlloc_5531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5531_, 0, v_a_5525_);
v___x_5530_ = v_reuseFailAlloc_5531_;
goto v_reusejp_5529_;
}
v_reusejp_5529_:
{
return v___x_5530_;
}
}
}
}
else
{
lean_object* v___x_5533_; lean_object* v___x_5534_; 
lean_dec_ref(v_mods_5425_);
lean_dec_ref(v_args_5423_);
v___x_5533_ = ((lean_object*)(l_Lake_BuiltinLint_run___closed__3));
v___x_5534_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_5533_);
if (lean_obj_tag(v___x_5534_) == 0)
{
lean_object* v___x_5536_; uint8_t v_isShared_5537_; uint8_t v_isSharedCheck_5542_; 
v_isSharedCheck_5542_ = !lean_is_exclusive(v___x_5534_);
if (v_isSharedCheck_5542_ == 0)
{
lean_object* v_unused_5543_; 
v_unused_5543_ = lean_ctor_get(v___x_5534_, 0);
lean_dec(v_unused_5543_);
v___x_5536_ = v___x_5534_;
v_isShared_5537_ = v_isSharedCheck_5542_;
goto v_resetjp_5535_;
}
else
{
lean_dec(v___x_5534_);
v___x_5536_ = lean_box(0);
v_isShared_5537_ = v_isSharedCheck_5542_;
goto v_resetjp_5535_;
}
v_resetjp_5535_:
{
lean_object* v___x_5538_; lean_object* v___x_5540_; 
v___x_5538_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5537_ == 0)
{
lean_ctor_set(v___x_5536_, 0, v___x_5538_);
v___x_5540_ = v___x_5536_;
goto v_reusejp_5539_;
}
else
{
lean_object* v_reuseFailAlloc_5541_; 
v_reuseFailAlloc_5541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5541_, 0, v___x_5538_);
v___x_5540_ = v_reuseFailAlloc_5541_;
goto v_reusejp_5539_;
}
v_reusejp_5539_:
{
return v___x_5540_;
}
}
}
else
{
lean_object* v_a_5544_; lean_object* v___x_5546_; uint8_t v_isShared_5547_; uint8_t v_isSharedCheck_5551_; 
v_a_5544_ = lean_ctor_get(v___x_5534_, 0);
v_isSharedCheck_5551_ = !lean_is_exclusive(v___x_5534_);
if (v_isSharedCheck_5551_ == 0)
{
v___x_5546_ = v___x_5534_;
v_isShared_5547_ = v_isSharedCheck_5551_;
goto v_resetjp_5545_;
}
else
{
lean_inc(v_a_5544_);
lean_dec(v___x_5534_);
v___x_5546_ = lean_box(0);
v_isShared_5547_ = v_isSharedCheck_5551_;
goto v_resetjp_5545_;
}
v_resetjp_5545_:
{
lean_object* v___x_5549_; 
if (v_isShared_5547_ == 0)
{
v___x_5549_ = v___x_5546_;
goto v_reusejp_5548_;
}
else
{
lean_object* v_reuseFailAlloc_5550_; 
v_reuseFailAlloc_5550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5550_, 0, v_a_5544_);
v___x_5549_ = v_reuseFailAlloc_5550_;
goto v_reusejp_5548_;
}
v_reusejp_5548_:
{
return v___x_5549_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_BuiltinLint_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_5423_ = stack[0].m_obj;
lean_object* v_res_5552_;
v_res_5552_ = l_Lake_BuiltinLint_run(v_args_5423_);
stack->m_obj
 = v_res_5552_;
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed(lean_object* v_args_5553_, lean_object* v_a_5554_){
_start:
{
lean_object* v_res_5555_; 
v_res_5555_ = l_Lake_BuiltinLint_run(v_args_5553_);
return v_res_5555_;
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
