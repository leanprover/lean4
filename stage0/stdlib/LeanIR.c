// Lean compiler output
// Module: LeanIR
// Imports: public import Init public meta import Init import Lean.CoreM import Lean.Util.ForEachExpr import all Lean.Util.Path import all Lean.Environment import Lean.Compiler.Options import Lean.Compiler.IR.CompilerM import all Lean.Compiler.CSimpAttr import Lean.Compiler.LCNF.EmitC import Lean.Language.Lean import Lean.Compiler.LCNF.PhaseExt import Lean.Compiler.LCNF.Main
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Elab_mkMessageCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_importModulesCore(lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_instDecidableEqOLeanLevel(uint8_t, uint8_t);
lean_object* l_Lean_finalizeImport(lean_object*, lean_object*, lean_object*, uint32_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_String_instHashableRaw_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_resumeCompilation(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_output;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_serve;
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* l_Lean_Message_toString(lean_object*, uint8_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stderr();
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___redArg(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecls();
lean_object* l_String_Slice_toName(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_setOption(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__5_spec__11_spec__15_spec__17(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_ir_export_entries(lean_object*);
lean_object* l_Lean_mkModuleData(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_get_ir_extra_const_names(lean_object*, uint8_t, uint8_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_IO_println___at___00Lean_Environment_displayStats_spec__1(lean_object*);
lean_object* l_Lean_ModuleSetup_load(lean_object*);
lean_object* l_Lean_LeanOptions_toOptions(lean_object*);
lean_object* lean_init_search_path();
lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedClassState_default;
extern lean_object* l_Lean_Meta_Match_Extension_instInhabitedState;
extern lean_object* l_Lean_Compiler_compiler_inLeanIR;
lean_object* l_Lean_Option_set___at___00Lean_Environment_realizeConst_spec__0(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_maxHeartbeats;
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_saveModuleDataParts(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_io_get_num_heartbeats();
extern lean_object* l_Lean_diagnostics;
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Compiler_LCNF_emitC(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_io_prim_handle_write(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_display_cumulative_profiling_times();
lean_object* l_Lean_Environment_displayStats(lean_object*);
lean_object* l_Lean_Core_getAndEmptyMessageLog___redArg(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
extern lean_object* l_instInhabitedError;
lean_object* l_instInhabitedEIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_setState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_setState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_postponedCompileDeclsExt;
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
extern lean_object* l_Lean_inheritedTraceOptions;
extern lean_object* l_Lean_instInhabitedFileMap_default;
extern lean_object* l_Lean_IR_declMapExt;
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_name(lean_object*);
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_setDeclPublic(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_impureSigExt;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedImportState_default;
lean_object* l_Lean_withImporting___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_CSimp_ext;
lean_object* l_Lean_Environment_setMainModule(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instanceExtension;
extern lean_object* l_Lean_classExtension;
extern lean_object* l_Lean_Meta_Match_Extension_extension;
lean_object* l_Lean_Environment_getModuleIdx_x3f(lean_object*, lean_object*);
uint8_t l_Lean_instOrdOLeanLevel_ord(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_LeanIR_0__mkIRSigData(lean_object*);
LEAN_EXPORT lean_object* l___private_LeanIR_0__mkIRSigData___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_LeanIR_0__mkIRData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_LeanIR_0__mkIRData___closed__0 = (const lean_object*)&l___private_LeanIR_0__mkIRData___closed__0_value;
static const lean_array_object l___private_LeanIR_0__mkIRData___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_LeanIR_0__mkIRData___closed__1 = (const lean_object*)&l___private_LeanIR_0__mkIRData___closed__1_value;
LEAN_EXPORT lean_object* l___private_LeanIR_0__mkIRData(lean_object*);
LEAN_EXPORT lean_object* l___private_LeanIR_0__mkIRData___boxed(lean_object*, lean_object*);
static const lean_string_object l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-D"};
static const lean_object* l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__0 = (const lean_object*)&l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanIR_0__setConfigOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "unknown option '"};
static const lean_object* l___private_LeanIR_0__setConfigOption___closed__0 = (const lean_object*)&l___private_LeanIR_0__setConfigOption___closed__0_value;
static const lean_string_object l___private_LeanIR_0__setConfigOption___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_LeanIR_0__setConfigOption___closed__1 = (const lean_object*)&l___private_LeanIR_0__setConfigOption___closed__1_value;
static const lean_string_object l___private_LeanIR_0__setConfigOption___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "invalid -D parameter, argument must contain '='"};
static const lean_object* l___private_LeanIR_0__setConfigOption___closed__2 = (const lean_object*)&l___private_LeanIR_0__setConfigOption___closed__2_value;
static const lean_ctor_object l___private_LeanIR_0__setConfigOption___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_LeanIR_0__setConfigOption___closed__2_value)}};
static const lean_object* l___private_LeanIR_0__setConfigOption___closed__3 = (const lean_object*)&l___private_LeanIR_0__setConfigOption___closed__3_value;
static const lean_string_object l___private_LeanIR_0__setConfigOption___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "invalid trailing argument `"};
static const lean_object* l___private_LeanIR_0__setConfigOption___closed__4 = (const lean_object*)&l___private_LeanIR_0__setConfigOption___closed__4_value;
static const lean_string_object l___private_LeanIR_0__setConfigOption___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "`, expected argument of the form `-Dopt=val`"};
static const lean_object* l___private_LeanIR_0__setConfigOption___closed__5 = (const lean_object*)&l___private_LeanIR_0__setConfigOption___closed__5_value;
LEAN_EXPORT lean_object* l___private_LeanIR_0__setConfigOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanIR_0__setConfigOption___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_main___elam__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_main___elam__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_main___elam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_main___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00main_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00main_spec__4___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00main_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00main_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00main_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_main___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_main___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_main___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "internal exception "};
static const lean_object* l_main___lam__1___closed__0 = (const lean_object*)&l_main___lam__1___closed__0_value;
static const lean_string_object l_main___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l_main___lam__1___closed__1 = (const lean_object*)&l_main___lam__1___closed__1_value;
static const lean_string_object l_main___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " (unknown)"};
static const lean_object* l_main___lam__1___closed__2 = (const lean_object*)&l_main___lam__1___closed__2_value;
LEAN_EXPORT lean_object* l_main___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_main___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00main_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "--stat"};
static const lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__5_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__5_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__5___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_boxed"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23_spec__35___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23_spec__35___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15_spec__19_spec__30___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15_spec__19_spec__30___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15_spec__19___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15_spec__19___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25_spec__39_spec__46___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25_spec__39_spec__46___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25_spec__39_spec__46___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25_spec__39_spec__46___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25_spec__39_spec__46___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25_spec__39(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25_spec__39___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25_spec__38(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25_spec__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__41___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__41___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__13___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0(uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0;
static lean_once_cell_t l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1;
static lean_once_cell_t l_Lean_addTraceAsMessages___at___00main_spec__9___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTraceAsMessages___at___00main_spec__9___closed__2;
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__38___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__38___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__38___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__38___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__38___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24_spec__36_spec__50___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24_spec__36_spec__50___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24_spec__36_spec__50___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24_spec__36_spec__50___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24_spec__36_spec__50___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24_spec__36(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24_spec__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24_spec__35(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24_spec__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__9_spec__14(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__9_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__9(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__8_spec__12_spec__25(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__8_spec__12_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__8_spec__12(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__8_spec__11(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__6___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_main___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "usage: leanir <setup.json> <output.ir> <output.c> [--stat] <-Dopt=val>..."};
static const lean_object* l_main___closed__0 = (const lean_object*)&l_main___closed__0_value;
static const lean_closure_object l_main___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_main___closed__1 = (const lean_object*)&l_main___closed__1_value;
static const lean_closure_object l_main___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_main___closed__2 = (const lean_object*)&l_main___closed__2_value;
static lean_once_cell_t l_main___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__3;
static lean_once_cell_t l_main___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__4;
static lean_once_cell_t l_main___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__5;
static lean_once_cell_t l_main___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__6;
static lean_once_cell_t l_main___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__7;
static lean_once_cell_t l_main___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__8;
static lean_once_cell_t l_main___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__9;
static const lean_ctor_object l_main___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_main___closed__10 = (const lean_object*)&l_main___closed__10_value;
static const lean_string_object l_main___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sig"};
static const lean_object* l_main___closed__11 = (const lean_object*)&l_main___closed__11_value;
static const lean_string_object l_main___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ir"};
static const lean_object* l_main___closed__12 = (const lean_object*)&l_main___closed__12_value;
static const lean_ctor_object l_main___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__12_value),LEAN_SCALAR_PTR_LITERAL(157, 0, 67, 166, 172, 92, 38, 85)}};
static const lean_object* l_main___closed__13 = (const lean_object*)&l_main___closed__13_value;
static const lean_string_object l_main___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "C code generation"};
static const lean_object* l_main___closed__14 = (const lean_object*)&l_main___closed__14_value;
static lean_once_cell_t l_main___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__15;
static const lean_string_object l_main___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "failed to create '"};
static const lean_object* l_main___closed__16 = (const lean_object*)&l_main___closed__16_value;
static const lean_string_object l_main___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "LeanIR"};
static const lean_object* l_main___closed__17 = (const lean_object*)&l_main___closed__17_value;
static const lean_string_object l_main___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "main"};
static const lean_object* l_main___closed__18 = (const lean_object*)&l_main___closed__18_value;
static const lean_string_object l_main___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_main___closed__19 = (const lean_object*)&l_main___closed__19_value;
static lean_once_cell_t l_main___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__20;
static const lean_string_object l_main___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "import"};
static const lean_object* l_main___closed__21 = (const lean_object*)&l_main___closed__21_value;
static lean_once_cell_t l_main___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__22;
static lean_once_cell_t l_main___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__23;
static const lean_string_object l_main___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l_main___closed__24 = (const lean_object*)&l_main___closed__24_value;
static const lean_ctor_object l_main___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__24_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l_main___closed__25 = (const lean_object*)&l_main___closed__25_value;
static const lean_ctor_object l_main___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_main___closed__25_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_main___closed__26 = (const lean_object*)&l_main___closed__26_value;
static lean_once_cell_t l_main___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__27;
static lean_once_cell_t l_main___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__28;
static lean_once_cell_t l_main___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__29;
static lean_once_cell_t l_main___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__30;
static lean_once_cell_t l_main___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__31;
static lean_once_cell_t l_main___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__32;
static const lean_array_object l_main___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_main___closed__33 = (const lean_object*)&l_main___closed__33_value;
static const lean_array_object l_main___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_main___closed__34 = (const lean_object*)&l_main___closed__34_value;
static const lean_string_object l_main___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "module '"};
static const lean_object* l_main___closed__35 = (const lean_object*)&l_main___closed__35_value;
static const lean_string_object l_main___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "' not found"};
static const lean_object* l_main___closed__36 = (const lean_object*)&l_main___closed__36_value;
static lean_once_cell_t l_main___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_main___closed__37;
LEAN_EXPORT lean_object* l_main___boxed__const__1;
LEAN_EXPORT lean_object* l_main___boxed__const__2;
LEAN_EXPORT lean_object* _lean_main(lean_object*);
LEAN_EXPORT lean_object* l_main___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15_spec__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15_spec__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__38(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15_spec__19_spec__30(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15_spec__19_spec__30___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23_spec__35(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23_spec__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__41(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__41___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24_spec__36_spec__50(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24_spec__36_spec__50___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25_spec__39_spec__46(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25_spec__39_spec__46___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanIR_0__mkIRSigData(lean_object* v_env_1_){
_start:
{
uint8_t v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_3_ = 0;
v___x_4_ = lean_box(0);
lean_inc_ref(v_env_1_);
v___x_5_ = l_Lean_mkModuleData(v_env_1_, v___x_3_, v___x_4_);
if (lean_obj_tag(v___x_5_) == 0)
{
lean_object* v_a_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_28_; 
v_a_6_ = lean_ctor_get(v___x_5_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_5_);
if (v_isSharedCheck_28_ == 0)
{
v___x_8_ = v___x_5_;
v_isShared_9_ = v_isSharedCheck_28_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_a_6_);
lean_dec(v___x_5_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_28_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
uint8_t v_isModule_10_; lean_object* v_imports_11_; lean_object* v_constNames_12_; lean_object* v_constants_13_; lean_object* v_entries_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_26_; 
v_isModule_10_ = lean_ctor_get_uint8(v_a_6_, sizeof(void*)*5);
v_imports_11_ = lean_ctor_get(v_a_6_, 0);
v_constNames_12_ = lean_ctor_get(v_a_6_, 1);
v_constants_13_ = lean_ctor_get(v_a_6_, 2);
v_entries_14_ = lean_ctor_get(v_a_6_, 4);
v_isSharedCheck_26_ = !lean_is_exclusive(v_a_6_);
if (v_isSharedCheck_26_ == 0)
{
lean_object* v_unused_27_; 
v_unused_27_ = lean_ctor_get(v_a_6_, 3);
lean_dec(v_unused_27_);
v___x_16_ = v_a_6_;
v_isShared_17_ = v_isSharedCheck_26_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_entries_14_);
lean_inc(v_constants_13_);
lean_inc(v_constNames_12_);
lean_inc(v_imports_11_);
lean_dec(v_a_6_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_26_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
uint8_t v___x_18_; lean_object* v___x_19_; lean_object* v___x_21_; 
v___x_18_ = 0;
v___x_19_ = lean_get_ir_extra_const_names(v_env_1_, v___x_3_, v___x_18_);
if (v_isShared_17_ == 0)
{
lean_ctor_set(v___x_16_, 3, v___x_19_);
v___x_21_ = v___x_16_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v_imports_11_);
lean_ctor_set(v_reuseFailAlloc_25_, 1, v_constNames_12_);
lean_ctor_set(v_reuseFailAlloc_25_, 2, v_constants_13_);
lean_ctor_set(v_reuseFailAlloc_25_, 3, v___x_19_);
lean_ctor_set(v_reuseFailAlloc_25_, 4, v_entries_14_);
lean_ctor_set_uint8(v_reuseFailAlloc_25_, sizeof(void*)*5, v_isModule_10_);
v___x_21_ = v_reuseFailAlloc_25_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
lean_object* v___x_23_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 0, v___x_21_);
v___x_23_ = v___x_8_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v___x_21_);
v___x_23_ = v_reuseFailAlloc_24_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
return v___x_23_;
}
}
}
}
}
else
{
lean_dec_ref(v_env_1_);
return v___x_5_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__mkIRSigData___boxed(lean_object* v_env_29_, lean_object* v_a_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l___private_LeanIR_0__mkIRSigData(v_env_29_);
return v_res_31_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1_spec__1(lean_object* v_a_32_, lean_object* v_as_33_, size_t v_i_34_, size_t v_stop_35_){
_start:
{
uint8_t v___x_36_; 
v___x_36_ = lean_usize_dec_eq(v_i_34_, v_stop_35_);
if (v___x_36_ == 0)
{
lean_object* v___x_37_; uint8_t v___x_38_; 
v___x_37_ = lean_array_uget_borrowed(v_as_33_, v_i_34_);
v___x_38_ = lean_name_eq(v_a_32_, v___x_37_);
if (v___x_38_ == 0)
{
size_t v___x_39_; size_t v___x_40_; 
v___x_39_ = ((size_t)1ULL);
v___x_40_ = lean_usize_add(v_i_34_, v___x_39_);
v_i_34_ = v___x_40_;
goto _start;
}
else
{
return v___x_38_;
}
}
else
{
uint8_t v___x_42_; 
v___x_42_ = 0;
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1_spec__1___boxed(lean_object* v_a_43_, lean_object* v_as_44_, lean_object* v_i_45_, lean_object* v_stop_46_){
_start:
{
size_t v_i_boxed_47_; size_t v_stop_boxed_48_; uint8_t v_res_49_; lean_object* v_r_50_; 
v_i_boxed_47_ = lean_unbox_usize(v_i_45_);
lean_dec(v_i_45_);
v_stop_boxed_48_ = lean_unbox_usize(v_stop_46_);
lean_dec(v_stop_46_);
v_res_49_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1_spec__1(v_a_43_, v_as_44_, v_i_boxed_47_, v_stop_boxed_48_);
lean_dec_ref(v_as_44_);
lean_dec(v_a_43_);
v_r_50_ = lean_box(v_res_49_);
return v_r_50_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1(lean_object* v_as_51_, lean_object* v_a_52_){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; uint8_t v___x_55_; 
v___x_53_ = lean_unsigned_to_nat(0u);
v___x_54_ = lean_array_get_size(v_as_51_);
v___x_55_ = lean_nat_dec_lt(v___x_53_, v___x_54_);
if (v___x_55_ == 0)
{
return v___x_55_;
}
else
{
if (v___x_55_ == 0)
{
return v___x_55_;
}
else
{
size_t v___x_56_; size_t v___x_57_; uint8_t v___x_58_; 
v___x_56_ = ((size_t)0ULL);
v___x_57_ = lean_usize_of_nat(v___x_54_);
v___x_58_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1_spec__1(v_a_52_, v_as_51_, v___x_56_, v___x_57_);
return v___x_58_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1___boxed(lean_object* v_as_59_, lean_object* v_a_60_){
_start:
{
uint8_t v_res_61_; lean_object* v_r_62_; 
v_res_61_ = l_Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1(v_as_59_, v_a_60_);
lean_dec(v_a_60_);
lean_dec_ref(v_as_59_);
v_r_62_ = lean_box(v_res_61_);
return v_r_62_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2(lean_object* v_irExtNames_63_, lean_object* v_as_64_, size_t v_i_65_, size_t v_stop_66_, lean_object* v_b_67_){
_start:
{
lean_object* v___y_69_; uint8_t v___x_73_; 
v___x_73_ = lean_usize_dec_eq(v_i_65_, v_stop_66_);
if (v___x_73_ == 0)
{
lean_object* v___x_74_; lean_object* v_fst_75_; uint8_t v___x_76_; 
v___x_74_ = lean_array_uget_borrowed(v_as_64_, v_i_65_);
v_fst_75_ = lean_ctor_get(v___x_74_, 0);
v___x_76_ = l_Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1(v_irExtNames_63_, v_fst_75_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; 
lean_inc(v___x_74_);
v___x_77_ = lean_array_push(v_b_67_, v___x_74_);
v___y_69_ = v___x_77_;
goto v___jp_68_;
}
else
{
v___y_69_ = v_b_67_;
goto v___jp_68_;
}
}
else
{
return v_b_67_;
}
v___jp_68_:
{
size_t v___x_70_; size_t v___x_71_; 
v___x_70_ = ((size_t)1ULL);
v___x_71_ = lean_usize_add(v_i_65_, v___x_70_);
v_i_65_ = v___x_71_;
v_b_67_ = v___y_69_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2___boxed(lean_object* v_irExtNames_78_, lean_object* v_as_79_, lean_object* v_i_80_, lean_object* v_stop_81_, lean_object* v_b_82_){
_start:
{
size_t v_i_boxed_83_; size_t v_stop_boxed_84_; lean_object* v_res_85_; 
v_i_boxed_83_ = lean_unbox_usize(v_i_80_);
lean_dec(v_i_80_);
v_stop_boxed_84_ = lean_unbox_usize(v_stop_81_);
lean_dec(v_stop_81_);
v_res_85_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2(v_irExtNames_78_, v_as_79_, v_i_boxed_83_, v_stop_boxed_84_, v_b_82_);
lean_dec_ref(v_as_79_);
lean_dec_ref(v_irExtNames_78_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0(size_t v_sz_86_, size_t v_i_87_, lean_object* v_bs_88_){
_start:
{
uint8_t v___x_89_; 
v___x_89_ = lean_usize_dec_lt(v_i_87_, v_sz_86_);
if (v___x_89_ == 0)
{
return v_bs_88_;
}
else
{
lean_object* v_v_90_; lean_object* v_fst_91_; lean_object* v___x_92_; lean_object* v_bs_x27_93_; size_t v___x_94_; size_t v___x_95_; lean_object* v___x_96_; 
v_v_90_ = lean_array_uget_borrowed(v_bs_88_, v_i_87_);
v_fst_91_ = lean_ctor_get(v_v_90_, 0);
lean_inc(v_fst_91_);
v___x_92_ = lean_unsigned_to_nat(0u);
v_bs_x27_93_ = lean_array_uset(v_bs_88_, v_i_87_, v___x_92_);
v___x_94_ = ((size_t)1ULL);
v___x_95_ = lean_usize_add(v_i_87_, v___x_94_);
v___x_96_ = lean_array_uset(v_bs_x27_93_, v_i_87_, v_fst_91_);
v_i_87_ = v___x_95_;
v_bs_88_ = v___x_96_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0___boxed(lean_object* v_sz_98_, lean_object* v_i_99_, lean_object* v_bs_100_){
_start:
{
size_t v_sz_boxed_101_; size_t v_i_boxed_102_; lean_object* v_res_103_; 
v_sz_boxed_101_ = lean_unbox_usize(v_sz_98_);
lean_dec(v_sz_98_);
v_i_boxed_102_ = lean_unbox_usize(v_i_99_);
lean_dec(v_i_99_);
v_res_103_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0(v_sz_boxed_101_, v_i_boxed_102_, v_bs_100_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__mkIRData(lean_object* v_env_108_){
_start:
{
lean_object* v_irEntries_110_; uint8_t v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
lean_inc_ref_n(v_env_108_, 2);
v_irEntries_110_ = lean_ir_export_entries(v_env_108_);
v___x_111_ = 2;
v___x_112_ = lean_box(0);
v___x_113_ = l_Lean_mkModuleData(v_env_108_, v___x_111_, v___x_112_);
if (lean_obj_tag(v___x_113_) == 0)
{
lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_144_; 
v_a_114_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_144_ == 0)
{
v___x_116_ = v___x_113_;
v_isShared_117_ = v_isSharedCheck_144_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_dec(v___x_113_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_144_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___y_119_; lean_object* v_entries_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; uint8_t v___x_135_; 
v_entries_131_ = lean_ctor_get(v_a_114_, 4);
lean_inc_ref(v_entries_131_);
lean_dec(v_a_114_);
v___x_132_ = lean_unsigned_to_nat(0u);
v___x_133_ = lean_array_get_size(v_entries_131_);
v___x_134_ = ((lean_object*)(l___private_LeanIR_0__mkIRData___closed__1));
v___x_135_ = lean_nat_dec_lt(v___x_132_, v___x_133_);
if (v___x_135_ == 0)
{
lean_dec_ref(v_entries_131_);
v___y_119_ = v___x_134_;
goto v___jp_118_;
}
else
{
size_t v_sz_136_; size_t v___x_137_; lean_object* v_irExtNames_138_; uint8_t v___x_139_; 
v_sz_136_ = lean_array_size(v_irEntries_110_);
v___x_137_ = ((size_t)0ULL);
lean_inc_ref(v_irEntries_110_);
v_irExtNames_138_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0(v_sz_136_, v___x_137_, v_irEntries_110_);
v___x_139_ = lean_nat_dec_le(v___x_133_, v___x_133_);
if (v___x_139_ == 0)
{
if (v___x_135_ == 0)
{
lean_dec_ref(v_irExtNames_138_);
lean_dec_ref(v_entries_131_);
v___y_119_ = v___x_134_;
goto v___jp_118_;
}
else
{
size_t v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_usize_of_nat(v___x_133_);
v___x_141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2(v_irExtNames_138_, v_entries_131_, v___x_137_, v___x_140_, v___x_134_);
lean_dec_ref(v_entries_131_);
lean_dec_ref(v_irExtNames_138_);
v___y_119_ = v___x_141_;
goto v___jp_118_;
}
}
else
{
size_t v___x_142_; lean_object* v___x_143_; 
v___x_142_ = lean_usize_of_nat(v___x_133_);
v___x_143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2(v_irExtNames_138_, v_entries_131_, v___x_137_, v___x_142_, v___x_134_);
lean_dec_ref(v_entries_131_);
lean_dec_ref(v_irExtNames_138_);
v___y_119_ = v___x_143_;
goto v___jp_118_;
}
}
v___jp_118_:
{
lean_object* v___x_120_; uint8_t v_isModule_121_; lean_object* v_imports_122_; lean_object* v___x_123_; uint8_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_129_; 
v___x_120_ = l_Lean_Environment_header(v_env_108_);
v_isModule_121_ = lean_ctor_get_uint8(v___x_120_, sizeof(void*)*7 + 4);
v_imports_122_ = lean_ctor_get(v___x_120_, 1);
lean_inc_ref(v_imports_122_);
lean_dec_ref(v___x_120_);
v___x_123_ = ((lean_object*)(l___private_LeanIR_0__mkIRData___closed__0));
v___x_124_ = 1;
v___x_125_ = lean_get_ir_extra_const_names(v_env_108_, v___x_111_, v___x_124_);
v___x_126_ = l_Array_append___redArg(v_irEntries_110_, v___y_119_);
lean_dec_ref(v___y_119_);
v___x_127_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_127_, 0, v_imports_122_);
lean_ctor_set(v___x_127_, 1, v___x_123_);
lean_ctor_set(v___x_127_, 2, v___x_123_);
lean_ctor_set(v___x_127_, 3, v___x_125_);
lean_ctor_set(v___x_127_, 4, v___x_126_);
lean_ctor_set_uint8(v___x_127_, sizeof(void*)*5, v_isModule_121_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 0, v___x_127_);
v___x_129_ = v___x_116_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_127_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
else
{
lean_dec_ref(v_irEntries_110_);
lean_dec_ref(v_env_108_);
return v___x_113_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__mkIRData___boxed(lean_object* v_env_145_, lean_object* v_a_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l___private_LeanIR_0__mkIRData(v_env_145_);
return v_res_147_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__0));
v___x_150_ = lean_string_utf8_byte_size(v___x_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(lean_object* v_s_151_){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_152_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__0));
v___x_153_ = lean_string_utf8_byte_size(v_s_151_);
v___x_154_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__1, &l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__1);
v___x_155_ = lean_nat_dec_le(v___x_154_, v___x_153_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; 
lean_dec_ref(v_s_151_);
v___x_156_ = lean_box(0);
return v___x_156_;
}
else
{
lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_157_ = lean_unsigned_to_nat(0u);
v___x_158_ = lean_string_memcmp(v_s_151_, v___x_152_, v___x_157_, v___x_157_, v___x_154_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; 
lean_dec_ref(v_s_151_);
v___x_159_ = lean_box(0);
return v___x_159_;
}
else
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
lean_inc_ref(v_s_151_);
v___x_160_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_160_, 0, v_s_151_);
lean_ctor_set(v___x_160_, 1, v___x_157_);
lean_ctor_set(v___x_160_, 2, v___x_153_);
v___x_161_ = l_String_Slice_pos_x21(v___x_160_, v___x_154_);
lean_dec_ref_known(v___x_160_, 3);
v___x_162_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_162_, 0, v_s_151_);
lean_ctor_set(v___x_162_, 1, v___x_161_);
lean_ctor_set(v___x_162_, 2, v___x_153_);
v___x_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
return v___x_163_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0(lean_object* v_s_164_, lean_object* v_pat_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(v_s_164_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___boxed(lean_object* v_s_167_, lean_object* v_pat_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0(v_s_167_, v_pat_168_);
lean_dec_ref(v_pat_168_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg(lean_object* v_val_170_, lean_object* v_a_171_, lean_object* v_b_172_){
_start:
{
lean_object* v_str_173_; lean_object* v_startInclusive_174_; lean_object* v_endExclusive_175_; lean_object* v___x_176_; uint8_t v___x_177_; 
v_str_173_ = lean_ctor_get(v_val_170_, 0);
v_startInclusive_174_ = lean_ctor_get(v_val_170_, 1);
v_endExclusive_175_ = lean_ctor_get(v_val_170_, 2);
v___x_176_ = lean_nat_sub(v_endExclusive_175_, v_startInclusive_174_);
v___x_177_ = lean_nat_dec_eq(v_a_171_, v___x_176_);
lean_dec(v___x_176_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; uint32_t v___x_179_; uint32_t v___x_180_; uint8_t v___x_181_; 
v___x_178_ = lean_nat_add(v_startInclusive_174_, v_a_171_);
v___x_179_ = lean_string_utf8_get_fast(v_str_173_, v___x_178_);
v___x_180_ = 61;
v___x_181_ = lean_uint32_dec_eq(v___x_179_, v___x_180_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
lean_dec(v_a_171_);
v___x_182_ = lean_box(0);
v___x_183_ = lean_string_utf8_next_fast(v_str_173_, v___x_178_);
lean_dec(v___x_178_);
v___x_184_ = lean_nat_sub(v___x_183_, v_startInclusive_174_);
v_a_171_ = v___x_184_;
v_b_172_ = v___x_182_;
goto _start;
}
else
{
lean_object* v___x_186_; 
lean_dec(v___x_178_);
v___x_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_186_, 0, v_a_171_);
return v___x_186_;
}
}
else
{
lean_dec(v_a_171_);
lean_inc(v_b_172_);
return v_b_172_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg___boxed(lean_object* v_val_187_, lean_object* v_a_188_, lean_object* v_b_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg(v_val_187_, v_a_188_, v_b_189_);
lean_dec(v_b_189_);
lean_dec_ref(v_val_187_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__setConfigOption(lean_object* v_opts_198_, lean_object* v_arg_199_){
_start:
{
lean_object* v___x_201_; 
lean_inc_ref(v_arg_199_);
v___x_201_ = l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(v_arg_199_);
if (lean_obj_tag(v___x_201_) == 1)
{
lean_object* v_val_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_266_; 
lean_dec_ref(v_arg_199_);
v_val_202_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_266_ == 0)
{
v___x_204_ = v___x_201_;
v_isShared_205_ = v_isSharedCheck_266_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_val_202_);
lean_dec(v___x_201_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_266_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___y_207_; lean_object* v_searcher_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v_searcher_259_ = lean_unsigned_to_nat(0u);
v___x_260_ = lean_box(0);
v___x_261_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg(v_val_202_, v_searcher_259_, v___x_260_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_startInclusive_262_; lean_object* v_endExclusive_263_; lean_object* v___x_264_; 
v_startInclusive_262_ = lean_ctor_get(v_val_202_, 1);
v_endExclusive_263_ = lean_ctor_get(v_val_202_, 2);
v___x_264_ = lean_nat_sub(v_endExclusive_263_, v_startInclusive_262_);
v___y_207_ = v___x_264_;
goto v___jp_206_;
}
else
{
lean_object* v_val_265_; 
v_val_265_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_val_265_);
lean_dec_ref_known(v___x_261_, 1);
v___y_207_ = v_val_265_;
goto v___jp_206_;
}
v___jp_206_:
{
lean_object* v_str_208_; lean_object* v_startInclusive_209_; lean_object* v_endExclusive_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_258_; 
v_str_208_ = lean_ctor_get(v_val_202_, 0);
v_startInclusive_209_ = lean_ctor_get(v_val_202_, 1);
v_endExclusive_210_ = lean_ctor_get(v_val_202_, 2);
v_isSharedCheck_258_ = !lean_is_exclusive(v_val_202_);
if (v_isSharedCheck_258_ == 0)
{
v___x_212_ = v_val_202_;
v_isShared_213_ = v_isSharedCheck_258_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_endExclusive_210_);
lean_inc(v_startInclusive_209_);
lean_inc(v_str_208_);
lean_dec(v_val_202_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_258_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_214_ = lean_nat_sub(v_endExclusive_210_, v_startInclusive_209_);
v___x_215_ = lean_nat_dec_eq(v___y_207_, v___x_214_);
lean_dec(v___x_214_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_245_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_245_ == 0)
{
v___x_219_ = v___x_216_;
v_isShared_220_ = v_isSharedCheck_245_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_216_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_245_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_221_; lean_object* v___x_223_; 
v___x_221_ = lean_nat_add(v_startInclusive_209_, v___y_207_);
lean_dec(v___y_207_);
lean_inc(v___x_221_);
lean_inc(v_startInclusive_209_);
lean_inc_ref(v_str_208_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 2, v___x_221_);
v___x_223_ = v___x_212_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_str_208_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v_startInclusive_209_);
lean_ctor_set(v_reuseFailAlloc_244_, 2, v___x_221_);
v___x_223_ = v_reuseFailAlloc_244_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
lean_object* v_name_224_; lean_object* v___x_225_; 
v_name_224_ = l_String_Slice_toName(v___x_223_);
lean_dec_ref(v___x_223_);
v___x_225_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_217_, v_name_224_);
lean_dec(v_a_217_);
if (lean_obj_tag(v___x_225_) == 1)
{
lean_object* v_val_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v_val_230_; lean_object* v___x_231_; 
lean_del_object(v___x_219_);
lean_del_object(v___x_204_);
v_val_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_val_226_);
lean_dec_ref_known(v___x_225_, 1);
v___x_227_ = lean_string_utf8_next_fast(v_str_208_, v___x_221_);
lean_dec(v___x_221_);
v___x_228_ = lean_nat_sub(v___x_227_, v_startInclusive_209_);
v___x_229_ = lean_nat_add(v_startInclusive_209_, v___x_228_);
lean_dec(v___x_228_);
lean_dec(v_startInclusive_209_);
v_val_230_ = lean_string_utf8_extract_fast(v_str_208_, v___x_229_, v_endExclusive_210_);
lean_dec(v_endExclusive_210_);
lean_dec(v___x_229_);
lean_dec_ref(v_str_208_);
v___x_231_ = l_Lean_Language_Lean_setOption(v_opts_198_, v_val_226_, v_name_224_, v_val_230_);
return v___x_231_;
}
else
{
lean_object* v___x_232_; uint8_t v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
lean_dec(v___x_225_);
lean_dec(v___x_221_);
lean_dec(v_endExclusive_210_);
lean_dec(v_startInclusive_209_);
lean_dec_ref(v_str_208_);
lean_dec_ref(v_opts_198_);
v___x_232_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__0));
v___x_233_ = 1;
v___x_234_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_224_, v___x_233_);
v___x_235_ = lean_string_append(v___x_232_, v___x_234_);
lean_dec_ref(v___x_234_);
v___x_236_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__1));
v___x_237_ = lean_string_append(v___x_235_, v___x_236_);
if (v_isShared_205_ == 0)
{
lean_ctor_set_tag(v___x_204_, 18);
lean_ctor_set(v___x_204_, 0, v___x_237_);
v___x_239_ = v___x_204_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_237_);
v___x_239_ = v_reuseFailAlloc_243_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
lean_object* v___x_241_; 
if (v_isShared_220_ == 0)
{
lean_ctor_set_tag(v___x_219_, 1);
lean_ctor_set(v___x_219_, 0, v___x_239_);
v___x_241_ = v___x_219_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
}
}
else
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
lean_del_object(v___x_212_);
lean_dec(v_endExclusive_210_);
lean_dec(v_startInclusive_209_);
lean_dec_ref(v_str_208_);
lean_dec(v___y_207_);
lean_del_object(v___x_204_);
lean_dec_ref(v_opts_198_);
v_a_246_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_253_ == 0)
{
v___x_248_ = v___x_216_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_216_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_a_246_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
}
else
{
lean_object* v___x_254_; lean_object* v___x_256_; 
lean_del_object(v___x_212_);
lean_dec(v_endExclusive_210_);
lean_dec(v_startInclusive_209_);
lean_dec_ref(v_str_208_);
lean_dec(v___y_207_);
lean_dec_ref(v_opts_198_);
v___x_254_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__3));
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v___x_254_);
v___x_256_ = v___x_204_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_254_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
}
}
else
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
lean_dec(v___x_201_);
lean_dec_ref(v_opts_198_);
v___x_267_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__4));
v___x_268_ = lean_string_append(v___x_267_, v_arg_199_);
lean_dec_ref(v_arg_199_);
v___x_269_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__5));
v___x_270_ = lean_string_append(v___x_268_, v___x_269_);
v___x_271_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
v___x_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
return v___x_272_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__setConfigOption___boxed(lean_object* v_opts_273_, lean_object* v_arg_274_, lean_object* v_a_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l___private_LeanIR_0__setConfigOption(v_opts_273_, v_arg_274_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1(lean_object* v_val_277_, lean_object* v_inst_278_, lean_object* v_R_279_, lean_object* v_a_280_, lean_object* v_b_281_, lean_object* v_c_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg(v_val_277_, v_a_280_, v_b_281_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___boxed(lean_object* v_val_284_, lean_object* v_inst_285_, lean_object* v_R_286_, lean_object* v_a_287_, lean_object* v_b_288_, lean_object* v_c_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1(v_val_284_, v_inst_285_, v_R_286_, v_a_287_, v_b_288_, v_c_289_);
lean_dec(v_b_288_);
lean_dec_ref(v_val_284_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0___redArg(lean_object* v___x_291_, lean_object* v_inst_292_, lean_object* v_ext_293_, lean_object* v_env_294_){
_start:
{
lean_object* v_toEnvExtension_296_; lean_object* v_addImportedFn_297_; lean_object* v_asyncMode_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v_importedEntries_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_329_; 
v_toEnvExtension_296_ = lean_ctor_get(v_ext_293_, 0);
lean_inc_ref(v_toEnvExtension_296_);
v_addImportedFn_297_ = lean_ctor_get(v_ext_293_, 2);
lean_inc_ref(v_addImportedFn_297_);
lean_dec_ref(v_ext_293_);
v_asyncMode_298_ = lean_ctor_get(v_toEnvExtension_296_, 2);
v___x_299_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v_inst_292_);
lean_inc_ref(v_env_294_);
v___x_300_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_299_, v_toEnvExtension_296_, v_env_294_, v_asyncMode_298_, v___x_291_);
lean_dec_ref(v___x_299_);
v_importedEntries_301_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_329_ == 0)
{
lean_object* v_unused_330_; 
v_unused_330_ = lean_ctor_get(v___x_300_, 1);
lean_dec(v_unused_330_);
v___x_303_ = v___x_300_;
v_isShared_304_ = v_isSharedCheck_329_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_importedEntries_301_);
lean_dec(v___x_300_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_329_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_305_ = l_Lean_Options_empty;
lean_inc_ref(v_env_294_);
v___x_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_306_, 0, v_env_294_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
lean_inc_ref(v_importedEntries_301_);
v___x_307_ = lean_apply_3(v_addImportedFn_297_, v_importedEntries_301_, v___x_306_, lean_box(0));
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_320_; 
v_a_308_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_320_ == 0)
{
v___x_310_ = v___x_307_;
v_isShared_311_ = v_isSharedCheck_320_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_307_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_320_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 1, v_a_308_);
v___x_313_ = v___x_303_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_importedEntries_301_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_a_308_);
v___x_313_ = v_reuseFailAlloc_319_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_317_; 
v___x_314_ = lean_box(0);
v___x_315_ = l_Lean_EnvExtension_setState___redArg(v_toEnvExtension_296_, v_env_294_, v___x_313_, v___x_314_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 0, v___x_315_);
v___x_317_ = v___x_310_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_315_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
else
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
lean_del_object(v___x_303_);
lean_dec_ref(v_importedEntries_301_);
lean_dec_ref(v_toEnvExtension_296_);
lean_dec_ref(v_env_294_);
v_a_321_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_328_ == 0)
{
v___x_323_ = v___x_307_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_307_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_321_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___elam__0___redArg___boxed(lean_object* v___x_331_, lean_object* v_inst_332_, lean_object* v_ext_333_, lean_object* v_env_334_, lean_object* v___y_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_main___elam__0___redArg(v___x_331_, v_inst_332_, v_ext_333_, v_env_334_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0(lean_object* v___x_337_, lean_object* v_00_u03b1_338_, lean_object* v_00_u03b2_339_, lean_object* v_00_u03c3_340_, lean_object* v_inst_341_, lean_object* v_ext_342_, lean_object* v_env_343_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l_main___elam__0___redArg(v___x_337_, v_inst_341_, v_ext_342_, v_env_343_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0___boxed(lean_object* v___x_346_, lean_object* v_00_u03b1_347_, lean_object* v_00_u03b2_348_, lean_object* v_00_u03c3_349_, lean_object* v_inst_350_, lean_object* v_ext_351_, lean_object* v_env_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_main___elam__0(v___x_346_, v_00_u03b1_347_, v_00_u03b2_348_, v_00_u03c3_349_, v_inst_350_, v_ext_351_, v_env_352_);
return v_res_354_;
}
}
static lean_object* _init_l_panic___at___00main_spec__4___closed__0(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = l_instInhabitedError;
v___x_356_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_356_, 0, lean_box(0));
lean_closure_set(v___x_356_, 1, lean_box(0));
lean_closure_set(v___x_356_, 2, v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00main_spec__4(lean_object* v_msg_357_){
_start:
{
lean_object* v___x_359_; lean_object* v___x_19613__overap_360_; lean_object* v___x_361_; 
v___x_359_ = lean_obj_once(&l_panic___at___00main_spec__4___closed__0, &l_panic___at___00main_spec__4___closed__0_once, _init_l_panic___at___00main_spec__4___closed__0);
v___x_19613__overap_360_ = lean_panic_fn_borrowed(v___x_359_, v_msg_357_);
v___x_361_ = lean_apply_1(v___x_19613__overap_360_, lean_box(0));
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00main_spec__4___boxed(lean_object* v_msg_362_, lean_object* v___y_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_panic___at___00main_spec__4(v_msg_362_);
return v_res_364_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00main_spec__7(lean_object* v_opts_365_, lean_object* v_opt_366_){
_start:
{
lean_object* v_name_367_; lean_object* v_defValue_368_; lean_object* v_map_369_; lean_object* v___x_370_; 
v_name_367_ = lean_ctor_get(v_opt_366_, 0);
v_defValue_368_ = lean_ctor_get(v_opt_366_, 1);
v_map_369_ = lean_ctor_get(v_opts_365_, 0);
v___x_370_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_369_, v_name_367_);
if (lean_obj_tag(v___x_370_) == 0)
{
uint8_t v___x_371_; 
v___x_371_ = lean_unbox(v_defValue_368_);
return v___x_371_;
}
else
{
lean_object* v_val_372_; 
v_val_372_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_val_372_);
lean_dec_ref_known(v___x_370_, 1);
if (lean_obj_tag(v_val_372_) == 1)
{
uint8_t v_v_373_; 
v_v_373_ = lean_ctor_get_uint8(v_val_372_, 0);
lean_dec_ref_known(v_val_372_, 0);
return v_v_373_;
}
else
{
uint8_t v___x_374_; 
lean_dec(v_val_372_);
v___x_374_ = lean_unbox(v_defValue_368_);
return v___x_374_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__7___boxed(lean_object* v_opts_375_, lean_object* v_opt_376_){
_start:
{
uint8_t v_res_377_; lean_object* v_r_378_; 
v_res_377_ = l_Lean_Option_get___at___00main_spec__7(v_opts_375_, v_opt_376_);
lean_dec_ref(v_opt_376_);
lean_dec_ref(v_opts_375_);
v_r_378_ = lean_box(v_res_377_);
return v_r_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__8(lean_object* v_opts_379_, lean_object* v_opt_380_){
_start:
{
lean_object* v_name_381_; lean_object* v_defValue_382_; lean_object* v_map_383_; lean_object* v___x_384_; 
v_name_381_ = lean_ctor_get(v_opt_380_, 0);
v_defValue_382_ = lean_ctor_get(v_opt_380_, 1);
v_map_383_ = lean_ctor_get(v_opts_379_, 0);
v___x_384_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_383_, v_name_381_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_inc(v_defValue_382_);
return v_defValue_382_;
}
else
{
lean_object* v_val_385_; 
v_val_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_val_385_);
lean_dec_ref_known(v___x_384_, 1);
if (lean_obj_tag(v_val_385_) == 3)
{
lean_object* v_v_386_; 
v_v_386_ = lean_ctor_get(v_val_385_, 0);
lean_inc(v_v_386_);
lean_dec_ref_known(v_val_385_, 1);
return v_v_386_;
}
else
{
lean_dec(v_val_385_);
lean_inc(v_defValue_382_);
return v_defValue_382_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__8___boxed(lean_object* v_opts_387_, lean_object* v_opt_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_Option_get___at___00main_spec__8(v_opts_387_, v_opt_388_);
lean_dec_ref(v_opt_388_);
lean_dec_ref(v_opts_387_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_main___lam__0(lean_object* v___x_390_, lean_object* v___x_391_, uint8_t v___x_392_, lean_object* v_importArts_393_, uint8_t v___y_394_, uint8_t v___x_395_, uint8_t v___x_396_, lean_object* v___x_397_, uint8_t v___x_398_, lean_object* v_name_399_){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = lean_st_mk_ref(v___x_390_);
v___x_402_ = l_Lean_importModulesCore(v___x_391_, v___x_392_, v_importArts_393_, v___y_394_, v___x_395_, v___x_401_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v___x_403_; lean_object* v_moduleNameMap_404_; lean_object* v_moduleNames_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_445_; 
lean_dec_ref_known(v___x_402_, 1);
v___x_403_ = lean_st_ref_get(v___x_401_);
lean_dec(v___x_401_);
v_moduleNameMap_404_ = lean_ctor_get(v___x_403_, 0);
v_moduleNames_405_ = lean_ctor_get(v___x_403_, 1);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_445_ == 0)
{
v___x_407_ = v___x_403_;
v_isShared_408_ = v_isSharedCheck_445_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_moduleNames_405_);
lean_inc(v_moduleNameMap_404_);
lean_dec(v___x_403_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_445_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___y_410_; lean_object* v___x_418_; 
v___x_418_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(v_moduleNameMap_404_, v_name_399_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_value_419_; lean_object* v_toEffectiveImport_420_; lean_object* v_index_421_; lean_object* v_size_422_; lean_object* v_parts_423_; lean_object* v_irParts_424_; uint8_t v_needsIRTrans_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_443_; 
v_value_419_ = lean_ctor_get(v___x_418_, 2);
lean_inc(v_value_419_);
v_toEffectiveImport_420_ = lean_ctor_get(v_value_419_, 0);
lean_inc_ref(v_toEffectiveImport_420_);
v_index_421_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_index_421_);
lean_dec_ref_known(v___x_418_, 3);
v_size_422_ = lean_ctor_get(v_moduleNameMap_404_, 0);
lean_inc(v_size_422_);
v_parts_423_ = lean_ctor_get(v_value_419_, 1);
v_irParts_424_ = lean_ctor_get(v_value_419_, 2);
v_needsIRTrans_425_ = lean_ctor_get_uint8(v_value_419_, sizeof(void*)*3);
v_isSharedCheck_443_ = !lean_is_exclusive(v_value_419_);
if (v_isSharedCheck_443_ == 0)
{
lean_object* v_unused_444_; 
v_unused_444_ = lean_ctor_get(v_value_419_, 0);
lean_dec(v_unused_444_);
v___x_427_ = v_value_419_;
v_isShared_428_ = v_isSharedCheck_443_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_irParts_424_);
lean_inc(v_parts_423_);
lean_dec(v_value_419_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_443_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v_toImport_429_; uint8_t v_hasData_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_442_; 
v_toImport_429_ = lean_ctor_get(v_toEffectiveImport_420_, 0);
v_hasData_430_ = lean_ctor_get_uint8(v_toEffectiveImport_420_, sizeof(void*)*1 + 1);
v_isSharedCheck_442_ = !lean_is_exclusive(v_toEffectiveImport_420_);
if (v_isSharedCheck_442_ == 0)
{
v___x_432_ = v_toEffectiveImport_420_;
v_isShared_433_ = v_isSharedCheck_442_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_toImport_429_);
lean_dec(v_toEffectiveImport_420_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_442_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
uint8_t v___x_434_; lean_object* v___x_436_; 
v___x_434_ = 0;
if (v_isShared_433_ == 0)
{
v___x_436_ = v___x_432_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_toImport_429_);
lean_ctor_set_uint8(v_reuseFailAlloc_441_, sizeof(void*)*1 + 1, v_hasData_430_);
v___x_436_ = v_reuseFailAlloc_441_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
lean_object* v___x_438_; 
lean_ctor_set_uint8(v___x_436_, sizeof(void*)*1, v___x_434_);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 0, v___x_436_);
v___x_438_ = v___x_427_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_436_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_parts_423_);
lean_ctor_set(v_reuseFailAlloc_440_, 2, v_irParts_424_);
lean_ctor_set_uint8(v_reuseFailAlloc_440_, sizeof(void*)*3, v_needsIRTrans_425_);
v___x_438_ = v_reuseFailAlloc_440_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
lean_object* v___x_439_; 
v___x_439_ = l_Std_DHashMap_Raw_setEntry___redArg(v_moduleNameMap_404_, v_size_422_, v_index_421_, v_name_399_, v___x_438_);
lean_dec(v_index_421_);
v___y_410_ = v___x_439_;
goto v___jp_409_;
}
}
}
}
}
else
{
lean_dec(v___x_418_);
lean_dec(v_name_399_);
v___y_410_ = v_moduleNameMap_404_;
goto v___jp_409_;
}
v___jp_409_:
{
lean_object* v___x_412_; 
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 0, v___y_410_);
v___x_412_ = v___x_407_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___y_410_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_moduleNames_405_);
v___x_412_ = v_reuseFailAlloc_417_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
uint32_t v___x_413_; uint8_t v___x_414_; 
v___x_413_ = 0;
v___x_414_ = l_Lean_instDecidableEqOLeanLevel(v___x_392_, v___x_396_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_finalizeImport(v___x_412_, v___x_391_, v___x_397_, v___x_413_, v___x_395_, v___x_398_, v___x_392_, v___x_395_, v___x_395_);
lean_dec_ref(v___x_412_);
return v___x_415_;
}
else
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_finalizeImport(v___x_412_, v___x_391_, v___x_397_, v___x_413_, v___x_395_, v___x_398_, v___x_392_, v___x_398_, v___x_395_);
lean_dec_ref(v___x_412_);
return v___x_416_;
}
}
}
}
}
else
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
lean_dec(v___x_401_);
lean_dec(v_name_399_);
lean_dec_ref(v___x_397_);
lean_dec_ref(v___x_391_);
v_a_446_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_402_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_402_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__0___boxed(lean_object* v___x_454_, lean_object* v___x_455_, lean_object* v___x_456_, lean_object* v_importArts_457_, lean_object* v___y_458_, lean_object* v___x_459_, lean_object* v___x_460_, lean_object* v___x_461_, lean_object* v___x_462_, lean_object* v_name_463_, lean_object* v___y_464_){
_start:
{
uint8_t v___x_37430__boxed_465_; uint8_t v___y_37431__boxed_466_; uint8_t v___x_37432__boxed_467_; uint8_t v___x_37433__boxed_468_; uint8_t v___x_37435__boxed_469_; lean_object* v_res_470_; 
v___x_37430__boxed_465_ = lean_unbox(v___x_456_);
v___y_37431__boxed_466_ = lean_unbox(v___y_458_);
v___x_37432__boxed_467_ = lean_unbox(v___x_459_);
v___x_37433__boxed_468_ = lean_unbox(v___x_460_);
v___x_37435__boxed_469_ = lean_unbox(v___x_462_);
v_res_470_ = l_main___lam__0(v___x_454_, v___x_455_, v___x_37430__boxed_465_, v_importArts_457_, v___y_37431__boxed_466_, v___x_37432__boxed_467_, v___x_37433__boxed_468_, v___x_461_, v___x_37435__boxed_469_, v_name_463_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_main___lam__1(lean_object* v___x_474_, lean_object* v___x_475_, lean_object* v___x_476_, lean_object* v_name_477_, lean_object* v_a_478_, uint8_t v___x_479_, lean_object* v___x_480_, lean_object* v_head_481_, lean_object* v___x_482_, lean_object* v___x_483_, lean_object* v___x_484_, lean_object* v___x_485_, lean_object* v___x_486_, lean_object* v___x_487_, lean_object* v___x_488_, lean_object* v___x_489_, uint8_t v___x_490_, uint8_t v___x_491_){
_start:
{
lean_object* v_a_494_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v_env_501_; lean_object* v___x_502_; uint8_t v___x_503_; lean_object* v_fileName_505_; lean_object* v_fileMap_506_; lean_object* v_currRecDepth_507_; lean_object* v_ref_508_; lean_object* v_currNamespace_509_; lean_object* v_openDecls_510_; lean_object* v_initHeartbeats_511_; lean_object* v_maxHeartbeats_512_; lean_object* v_quotContext_513_; lean_object* v_currMacroScope_514_; lean_object* v_cancelTk_x3f_515_; uint8_t v_suppressElabErrors_516_; lean_object* v_inheritedTraceOptions_517_; lean_object* v___y_518_; uint8_t v___y_550_; uint8_t v___x_570_; 
v___x_497_ = lean_io_get_num_heartbeats();
v___x_498_ = lean_st_mk_ref(v___x_474_);
v___x_499_ = lean_st_ref_get(v___x_475_);
v___x_500_ = lean_st_ref_get(v___x_498_);
v_env_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc_ref(v_env_501_);
lean_dec(v___x_500_);
v___x_502_ = l_Lean_diagnostics;
v___x_503_ = l_Lean_Option_get___at___00main_spec__7(v___x_476_, v___x_502_);
v___x_570_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_501_);
lean_dec_ref(v_env_501_);
if (v___x_570_ == 0)
{
if (v___x_503_ == 0)
{
v___y_550_ = v___x_491_;
goto v___jp_549_;
}
else
{
v___y_550_ = v___x_570_;
goto v___jp_549_;
}
}
else
{
v___y_550_ = v___x_503_;
goto v___jp_549_;
}
v___jp_493_:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_mk_io_user_error(v_a_494_);
v___x_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
return v___x_496_;
}
v___jp_504_:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_519_ = l_Lean_maxRecDepth;
v___x_520_ = l_Lean_Option_get___at___00main_spec__8(v___x_476_, v___x_519_);
v___x_521_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_521_, 0, v_fileName_505_);
lean_ctor_set(v___x_521_, 1, v_fileMap_506_);
lean_ctor_set(v___x_521_, 2, v___x_476_);
lean_ctor_set(v___x_521_, 3, v_currRecDepth_507_);
lean_ctor_set(v___x_521_, 4, v___x_520_);
lean_ctor_set(v___x_521_, 5, v_ref_508_);
lean_ctor_set(v___x_521_, 6, v_currNamespace_509_);
lean_ctor_set(v___x_521_, 7, v_openDecls_510_);
lean_ctor_set(v___x_521_, 8, v_initHeartbeats_511_);
lean_ctor_set(v___x_521_, 9, v_maxHeartbeats_512_);
lean_ctor_set(v___x_521_, 10, v_quotContext_513_);
lean_ctor_set(v___x_521_, 11, v_currMacroScope_514_);
lean_ctor_set(v___x_521_, 12, v_cancelTk_x3f_515_);
lean_ctor_set(v___x_521_, 13, v_inheritedTraceOptions_517_);
lean_ctor_set_uint8(v___x_521_, sizeof(void*)*14, v___x_503_);
lean_ctor_set_uint8(v___x_521_, sizeof(void*)*14 + 1, v_suppressElabErrors_516_);
v___x_522_ = l_Lean_Compiler_LCNF_emitC(v_name_477_, v___x_521_, v___y_518_);
lean_dec(v___y_518_);
lean_dec_ref_known(v___x_521_, 14);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
lean_dec_ref_known(v___x_522_, 1);
v___x_524_ = lean_st_ref_get(v___x_498_);
lean_dec(v___x_498_);
lean_dec(v___x_524_);
v___x_525_ = lean_string_to_utf8(v_a_523_);
lean_dec(v_a_523_);
v___x_526_ = lean_io_prim_handle_write(v_a_478_, v___x_525_);
lean_dec_ref(v___x_525_);
return v___x_526_;
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_548_; 
lean_dec(v___x_498_);
v_a_527_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_548_ == 0)
{
v___x_529_ = v___x_522_;
v_isShared_530_ = v_isSharedCheck_548_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_522_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_548_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
if (lean_obj_tag(v_a_527_) == 0)
{
lean_object* v_msg_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_535_; 
v_msg_531_ = lean_ctor_get(v_a_527_, 1);
lean_inc_ref(v_msg_531_);
lean_dec_ref_known(v_a_527_, 2);
v___x_532_ = l_Lean_MessageData_toString(v_msg_531_);
v___x_533_ = lean_mk_io_user_error(v___x_532_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 0, v___x_533_);
v___x_535_ = v___x_529_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
else
{
lean_object* v_id_537_; lean_object* v___x_538_; 
lean_del_object(v___x_529_);
v_id_537_ = lean_ctor_get(v_a_527_, 0);
lean_inc(v_id_537_);
lean_dec_ref_known(v_a_527_, 2);
v___x_538_ = l_Lean_InternalExceptionId_getName(v_id_537_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
lean_dec(v_id_537_);
v_a_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_a_539_);
lean_dec_ref_known(v___x_538_, 1);
v___x_540_ = ((lean_object*)(l_main___lam__1___closed__0));
v___x_541_ = l_Lean_Name_toString(v_a_539_, v___x_479_);
v___x_542_ = lean_string_append(v___x_540_, v___x_541_);
lean_dec_ref(v___x_541_);
v_a_494_ = v___x_542_;
goto v___jp_493_;
}
else
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
lean_dec_ref_known(v___x_538_, 1);
v___x_543_ = ((lean_object*)(l_main___lam__1___closed__1));
v___x_544_ = l_Nat_reprFast(v_id_537_);
v___x_545_ = lean_string_append(v___x_543_, v___x_544_);
lean_dec_ref(v___x_544_);
v___x_546_ = ((lean_object*)(l_main___lam__1___closed__2));
v___x_547_ = lean_string_append(v___x_545_, v___x_546_);
v_a_494_ = v___x_547_;
goto v___jp_493_;
}
}
}
}
}
v___jp_549_:
{
if (v___y_550_ == 0)
{
lean_object* v___x_551_; lean_object* v_env_552_; lean_object* v_nextMacroScope_553_; lean_object* v_ngen_554_; lean_object* v_auxDeclNGen_555_; lean_object* v_traceState_556_; lean_object* v_messages_557_; lean_object* v_infoState_558_; lean_object* v_snapshotTasks_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_568_; 
v___x_551_ = lean_st_ref_take(v___x_498_);
v_env_552_ = lean_ctor_get(v___x_551_, 0);
v_nextMacroScope_553_ = lean_ctor_get(v___x_551_, 1);
v_ngen_554_ = lean_ctor_get(v___x_551_, 2);
v_auxDeclNGen_555_ = lean_ctor_get(v___x_551_, 3);
v_traceState_556_ = lean_ctor_get(v___x_551_, 4);
v_messages_557_ = lean_ctor_get(v___x_551_, 6);
v_infoState_558_ = lean_ctor_get(v___x_551_, 7);
v_snapshotTasks_559_ = lean_ctor_get(v___x_551_, 8);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_568_ == 0)
{
lean_object* v_unused_569_; 
v_unused_569_ = lean_ctor_get(v___x_551_, 5);
lean_dec(v_unused_569_);
v___x_561_ = v___x_551_;
v_isShared_562_ = v_isSharedCheck_568_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_snapshotTasks_559_);
lean_inc(v_infoState_558_);
lean_inc(v_messages_557_);
lean_inc(v_traceState_556_);
lean_inc(v_auxDeclNGen_555_);
lean_inc(v_ngen_554_);
lean_inc(v_nextMacroScope_553_);
lean_inc(v_env_552_);
lean_dec(v___x_551_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_568_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_563_ = l_Lean_Kernel_enableDiag(v_env_552_, v___x_503_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 5, v___x_480_);
lean_ctor_set(v___x_561_, 0, v___x_563_);
v___x_565_ = v___x_561_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_563_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v_nextMacroScope_553_);
lean_ctor_set(v_reuseFailAlloc_567_, 2, v_ngen_554_);
lean_ctor_set(v_reuseFailAlloc_567_, 3, v_auxDeclNGen_555_);
lean_ctor_set(v_reuseFailAlloc_567_, 4, v_traceState_556_);
lean_ctor_set(v_reuseFailAlloc_567_, 5, v___x_480_);
lean_ctor_set(v_reuseFailAlloc_567_, 6, v_messages_557_);
lean_ctor_set(v_reuseFailAlloc_567_, 7, v_infoState_558_);
lean_ctor_set(v_reuseFailAlloc_567_, 8, v_snapshotTasks_559_);
v___x_565_ = v_reuseFailAlloc_567_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_object* v___x_566_; 
v___x_566_ = lean_st_ref_put(v___x_498_, v___x_565_);
lean_inc(v___x_498_);
lean_inc(v___x_485_);
v_fileName_505_ = v_head_481_;
v_fileMap_506_ = v___x_482_;
v_currRecDepth_507_ = v___x_483_;
v_ref_508_ = v___x_484_;
v_currNamespace_509_ = v___x_485_;
v_openDecls_510_ = v___x_486_;
v_initHeartbeats_511_ = v___x_497_;
v_maxHeartbeats_512_ = v___x_487_;
v_quotContext_513_ = v___x_485_;
v_currMacroScope_514_ = v___x_488_;
v_cancelTk_x3f_515_ = v___x_489_;
v_suppressElabErrors_516_ = v___x_490_;
v_inheritedTraceOptions_517_ = v___x_499_;
v___y_518_ = v___x_498_;
goto v___jp_504_;
}
}
}
else
{
lean_dec_ref(v___x_480_);
lean_inc(v___x_498_);
lean_inc(v___x_485_);
v_fileName_505_ = v_head_481_;
v_fileMap_506_ = v___x_482_;
v_currRecDepth_507_ = v___x_483_;
v_ref_508_ = v___x_484_;
v_currNamespace_509_ = v___x_485_;
v_openDecls_510_ = v___x_486_;
v_initHeartbeats_511_ = v___x_497_;
v_maxHeartbeats_512_ = v___x_487_;
v_quotContext_513_ = v___x_485_;
v_currMacroScope_514_ = v___x_488_;
v_cancelTk_x3f_515_ = v___x_489_;
v_suppressElabErrors_516_ = v___x_490_;
v_inheritedTraceOptions_517_ = v___x_499_;
v___y_518_ = v___x_498_;
goto v___jp_504_;
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__1___boxed(lean_object** _args){
lean_object* v___x_571_ = _args[0];
lean_object* v___x_572_ = _args[1];
lean_object* v___x_573_ = _args[2];
lean_object* v_name_574_ = _args[3];
lean_object* v_a_575_ = _args[4];
lean_object* v___x_576_ = _args[5];
lean_object* v___x_577_ = _args[6];
lean_object* v_head_578_ = _args[7];
lean_object* v___x_579_ = _args[8];
lean_object* v___x_580_ = _args[9];
lean_object* v___x_581_ = _args[10];
lean_object* v___x_582_ = _args[11];
lean_object* v___x_583_ = _args[12];
lean_object* v___x_584_ = _args[13];
lean_object* v___x_585_ = _args[14];
lean_object* v___x_586_ = _args[15];
lean_object* v___x_587_ = _args[16];
lean_object* v___x_588_ = _args[17];
lean_object* v___y_589_ = _args[18];
_start:
{
uint8_t v___x_37554__boxed_590_; uint8_t v___x_37565__boxed_591_; uint8_t v___x_37566__boxed_592_; lean_object* v_res_593_; 
v___x_37554__boxed_590_ = lean_unbox(v___x_576_);
v___x_37565__boxed_591_ = lean_unbox(v___x_587_);
v___x_37566__boxed_592_ = lean_unbox(v___x_588_);
v_res_593_ = l_main___lam__1(v___x_571_, v___x_572_, v___x_573_, v_name_574_, v_a_575_, v___x_37554__boxed_590_, v___x_577_, v_head_578_, v___x_579_, v___x_580_, v___x_581_, v___x_582_, v___x_583_, v___x_584_, v___x_585_, v___x_586_, v___x_37565__boxed_591_, v___x_37566__boxed_592_);
lean_dec(v_a_575_);
lean_dec(v___x_572_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(lean_object* v_x2_594_, lean_object* v_as_595_, size_t v_i_596_, size_t v_stop_597_, lean_object* v_b_598_){
_start:
{
uint8_t v___x_599_; 
v___x_599_ = lean_usize_dec_eq(v_i_596_, v_stop_597_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; size_t v___x_602_; size_t v___x_603_; 
v___x_600_ = lean_array_uget_borrowed(v_as_595_, v_i_596_);
lean_inc_ref(v_x2_594_);
lean_inc(v___x_600_);
v___x_601_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_600_, v_x2_594_, v_b_598_);
v___x_602_ = ((size_t)1ULL);
v___x_603_ = lean_usize_add(v_i_596_, v___x_602_);
v_i_596_ = v___x_603_;
v_b_598_ = v___x_601_;
goto _start;
}
else
{
lean_dec_ref(v_x2_594_);
return v_b_598_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2___boxed(lean_object* v_x2_605_, lean_object* v_as_606_, lean_object* v_i_607_, lean_object* v_stop_608_, lean_object* v_b_609_){
_start:
{
size_t v_i_boxed_610_; size_t v_stop_boxed_611_; lean_object* v_res_612_; 
v_i_boxed_610_ = lean_unbox_usize(v_i_607_);
lean_dec(v_i_607_);
v_stop_boxed_611_ = lean_unbox_usize(v_stop_608_);
lean_dec(v_stop_608_);
v_res_612_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v_x2_605_, v_as_606_, v_i_boxed_610_, v_stop_boxed_611_, v_b_609_);
lean_dec_ref(v_as_606_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(lean_object* v_as_613_, size_t v_i_614_, size_t v_stop_615_, lean_object* v_b_616_){
_start:
{
lean_object* v___y_618_; uint8_t v___x_622_; 
v___x_622_ = lean_usize_dec_eq(v_i_614_, v_stop_615_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; lean_object* v_declNames_624_; lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_623_ = lean_array_uget_borrowed(v_as_613_, v_i_614_);
v_declNames_624_ = lean_ctor_get(v___x_623_, 0);
v___x_625_ = lean_unsigned_to_nat(0u);
v___x_626_ = lean_array_get_size(v_declNames_624_);
v___x_627_ = lean_nat_dec_lt(v___x_625_, v___x_626_);
if (v___x_627_ == 0)
{
v___y_618_ = v_b_616_;
goto v___jp_617_;
}
else
{
uint8_t v___x_628_; 
v___x_628_ = lean_nat_dec_le(v___x_626_, v___x_626_);
if (v___x_628_ == 0)
{
if (v___x_627_ == 0)
{
v___y_618_ = v_b_616_;
goto v___jp_617_;
}
else
{
size_t v___x_629_; size_t v___x_630_; lean_object* v___x_631_; 
v___x_629_ = ((size_t)0ULL);
v___x_630_ = lean_usize_of_nat(v___x_626_);
lean_inc(v___x_623_);
v___x_631_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_623_, v_declNames_624_, v___x_629_, v___x_630_, v_b_616_);
v___y_618_ = v___x_631_;
goto v___jp_617_;
}
}
else
{
size_t v___x_632_; size_t v___x_633_; lean_object* v___x_634_; 
v___x_632_ = ((size_t)0ULL);
v___x_633_ = lean_usize_of_nat(v___x_626_);
lean_inc(v___x_623_);
v___x_634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_623_, v_declNames_624_, v___x_632_, v___x_633_, v_b_616_);
v___y_618_ = v___x_634_;
goto v___jp_617_;
}
}
}
else
{
return v_b_616_;
}
v___jp_617_:
{
size_t v___x_619_; size_t v___x_620_; 
v___x_619_ = ((size_t)1ULL);
v___x_620_ = lean_usize_add(v_i_614_, v___x_619_);
v_i_614_ = v___x_620_;
v_b_616_ = v___y_618_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14___boxed(lean_object* v_as_635_, lean_object* v_i_636_, lean_object* v_stop_637_, lean_object* v_b_638_){
_start:
{
size_t v_i_boxed_639_; size_t v_stop_boxed_640_; lean_object* v_res_641_; 
v_i_boxed_639_ = lean_unbox_usize(v_i_636_);
lean_dec(v_i_636_);
v_stop_boxed_640_ = lean_unbox_usize(v_stop_637_);
lean_dec(v_stop_637_);
v_res_641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(v_as_635_, v_i_boxed_639_, v_stop_boxed_640_, v_b_638_);
lean_dec_ref(v_as_635_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(lean_object* v_o_645_, lean_object* v_k_646_, lean_object* v_v_647_){
_start:
{
lean_object* v_map_648_; uint8_t v_hasTrace_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_663_; 
v_map_648_ = lean_ctor_get(v_o_645_, 0);
v_hasTrace_649_ = lean_ctor_get_uint8(v_o_645_, sizeof(void*)*1);
v_isSharedCheck_663_ = !lean_is_exclusive(v_o_645_);
if (v_isSharedCheck_663_ == 0)
{
v___x_651_ = v_o_645_;
v_isShared_652_ = v_isSharedCheck_663_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_map_648_);
lean_dec(v_o_645_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_663_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_653_, 0, v_v_647_);
lean_inc(v_k_646_);
v___x_654_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_646_, v___x_653_, v_map_648_);
if (v_hasTrace_649_ == 0)
{
lean_object* v___x_655_; uint8_t v___x_656_; lean_object* v___x_658_; 
v___x_655_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_656_ = l_Lean_Name_isPrefixOf(v___x_655_, v_k_646_);
lean_dec(v_k_646_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 0, v___x_654_);
v___x_658_ = v___x_651_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_654_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
lean_ctor_set_uint8(v___x_658_, sizeof(void*)*1, v___x_656_);
return v___x_658_;
}
}
else
{
lean_object* v___x_661_; 
lean_dec(v_k_646_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 0, v___x_654_);
v___x_661_ = v___x_651_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_654_);
lean_ctor_set_uint8(v_reuseFailAlloc_662_, sizeof(void*)*1, v_hasTrace_649_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00main_spec__3(lean_object* v_opts_664_, lean_object* v_opt_665_, lean_object* v_val_666_){
_start:
{
lean_object* v_name_667_; lean_object* v___x_668_; 
v_name_667_ = lean_ctor_get(v_opt_665_, 0);
lean_inc(v_name_667_);
lean_dec_ref(v_opt_665_);
v___x_668_ = l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(v_opts_664_, v_name_667_, v_val_666_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(lean_object* v_as_669_, size_t v_i_670_, size_t v_stop_671_, lean_object* v_b_672_){
_start:
{
uint8_t v___x_673_; 
v___x_673_ = lean_usize_dec_eq(v_i_670_, v_stop_671_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; lean_object* v_name_675_; lean_object* v___x_676_; size_t v___x_677_; size_t v___x_678_; 
v___x_674_ = lean_array_uget_borrowed(v_as_669_, v_i_670_);
v_name_675_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_name_675_);
v___x_676_ = l_Lean_Compiler_LCNF_setDeclPublic(v_b_672_, v_name_675_);
v___x_677_ = ((size_t)1ULL);
v___x_678_ = lean_usize_add(v_i_670_, v___x_677_);
v_i_670_ = v___x_678_;
v_b_672_ = v___x_676_;
goto _start;
}
else
{
return v_b_672_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___boxed(lean_object* v_as_680_, lean_object* v_i_681_, lean_object* v_stop_682_, lean_object* v_b_683_){
_start:
{
size_t v_i_boxed_684_; size_t v_stop_boxed_685_; lean_object* v_res_686_; 
v_i_boxed_684_ = lean_unbox_usize(v_i_681_);
lean_dec(v_i_681_);
v_stop_boxed_685_ = lean_unbox_usize(v_stop_682_);
lean_dec(v_stop_682_);
v_res_686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v_as_680_, v_i_boxed_684_, v_stop_boxed_685_, v_b_683_);
lean_dec_ref(v_as_680_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg(lean_object* v_as_x27_688_, lean_object* v_b_689_){
_start:
{
if (lean_obj_tag(v_as_x27_688_) == 0)
{
lean_object* v___x_691_; 
v___x_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_691_, 0, v_b_689_);
return v___x_691_;
}
else
{
lean_object* v_head_692_; lean_object* v_tail_693_; lean_object* v_fst_694_; lean_object* v_snd_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_720_; 
v_head_692_ = lean_ctor_get(v_as_x27_688_, 0);
v_tail_693_ = lean_ctor_get(v_as_x27_688_, 1);
v_fst_694_ = lean_ctor_get(v_b_689_, 0);
v_snd_695_ = lean_ctor_get(v_b_689_, 1);
v_isSharedCheck_720_ = !lean_is_exclusive(v_b_689_);
if (v_isSharedCheck_720_ == 0)
{
v___x_697_ = v_b_689_;
v_isShared_698_ = v_isSharedCheck_720_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_snd_695_);
lean_inc(v_fst_694_);
lean_dec(v_b_689_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_720_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_699_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0));
v___x_700_ = lean_string_dec_eq(v_head_692_, v___x_699_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; 
lean_inc(v_head_692_);
v___x_701_ = l___private_LeanIR_0__setConfigOption(v_snd_695_, v_head_692_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; lean_object* v___x_704_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_a_702_);
lean_dec_ref_known(v___x_701_, 1);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 1, v_a_702_);
v___x_704_ = v___x_697_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_fst_694_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_a_702_);
v___x_704_ = v_reuseFailAlloc_706_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
v_as_x27_688_ = v_tail_693_;
v_b_689_ = v___x_704_;
goto _start;
}
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_del_object(v___x_697_);
lean_dec(v_fst_694_);
v_a_707_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_701_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_701_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
else
{
lean_object* v___x_715_; lean_object* v___x_717_; 
lean_dec(v_fst_694_);
v___x_715_ = lean_box(v___x_700_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v___x_715_);
v___x_717_ = v___x_697_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_snd_695_);
v___x_717_ = v_reuseFailAlloc_719_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
v_as_x27_688_ = v_tail_693_;
v_b_689_ = v___x_717_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg___boxed(lean_object* v_as_x27_721_, lean_object* v_b_722_, lean_object* v___y_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_721_, v_b_722_);
lean_dec(v_as_x27_721_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(lean_object* v_a_725_, lean_object* v_as_726_, size_t v_i_727_, size_t v_stop_728_, lean_object* v_b_729_){
_start:
{
lean_object* v___y_731_; uint8_t v___x_735_; 
v___x_735_ = lean_usize_dec_eq(v_i_727_, v_stop_728_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; lean_object* v_name_737_; uint8_t v___x_738_; 
v___x_736_ = lean_array_uget_borrowed(v_as_726_, v_i_727_);
v_name_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_name_737_);
lean_inc_ref(v_a_725_);
v___x_738_ = l_Lean_isExtern(v_a_725_, v_name_737_);
if (v___x_738_ == 0)
{
v___y_731_ = v_b_729_;
goto v___jp_730_;
}
else
{
lean_object* v___x_739_; 
lean_inc(v___x_736_);
v___x_739_ = lean_array_push(v_b_729_, v___x_736_);
v___y_731_ = v___x_739_;
goto v___jp_730_;
}
}
else
{
lean_dec_ref(v_a_725_);
return v_b_729_;
}
v___jp_730_:
{
size_t v___x_732_; size_t v___x_733_; 
v___x_732_ = ((size_t)1ULL);
v___x_733_ = lean_usize_add(v_i_727_, v___x_732_);
v_i_727_ = v___x_733_;
v_b_729_ = v___y_731_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18___boxed(lean_object* v_a_740_, lean_object* v_as_741_, lean_object* v_i_742_, lean_object* v_stop_743_, lean_object* v_b_744_){
_start:
{
size_t v_i_boxed_745_; size_t v_stop_boxed_746_; lean_object* v_res_747_; 
v_i_boxed_745_ = lean_unbox_usize(v_i_742_);
lean_dec(v_i_742_);
v_stop_boxed_746_ = lean_unbox_usize(v_stop_743_);
lean_dec(v_stop_743_);
v_res_747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_a_740_, v_as_741_, v_i_boxed_745_, v_stop_boxed_746_, v_b_744_);
lean_dec_ref(v_as_741_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__5_spec__6(lean_object* v_s_748_){
_start:
{
lean_object* v___x_750_; lean_object* v_putStr_751_; lean_object* v___x_752_; 
v___x_750_ = lean_get_stderr();
v_putStr_751_ = lean_ctor_get(v___x_750_, 4);
lean_inc_ref(v_putStr_751_);
lean_dec_ref(v___x_750_);
v___x_752_ = lean_apply_2(v_putStr_751_, v_s_748_, lean_box(0));
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__5_spec__6___boxed(lean_object* v_s_753_, lean_object* v_a_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__5_spec__6(v_s_753_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__5(lean_object* v_s_756_){
_start:
{
uint32_t v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_758_ = 10;
v___x_759_ = lean_string_push(v_s_756_, v___x_758_);
v___x_760_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__5_spec__6(v___x_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__5___boxed(lean_object* v_s_761_, lean_object* v_a_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_IO_eprintln___at___00main_spec__5(v_s_761_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(lean_object* v___y_765_, lean_object* v_as_766_, size_t v_i_767_, size_t v_stop_768_, lean_object* v_b_769_){
_start:
{
lean_object* v___y_771_; uint8_t v___x_775_; 
v___x_775_ = lean_usize_dec_eq(v_i_767_, v_stop_768_);
if (v___x_775_ == 0)
{
lean_object* v_fst_776_; lean_object* v_snd_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___y_781_; 
v_fst_776_ = lean_ctor_get(v_b_769_, 0);
v_snd_777_ = lean_ctor_get(v_b_769_, 1);
v___x_778_ = lean_array_uget_borrowed(v_as_766_, v_i_767_);
v___x_779_ = l_Lean_IR_Decl_name(v___x_778_);
if (lean_obj_tag(v___x_779_) == 1)
{
lean_object* v_pre_794_; lean_object* v_str_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
v_pre_794_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_pre_794_);
v_str_795_ = lean_ctor_get(v___x_779_, 1);
lean_inc_ref(v_str_795_);
v___x_796_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___closed__0));
v___x_797_ = lean_string_dec_eq(v_str_795_, v___x_796_);
lean_dec_ref(v_str_795_);
if (v___x_797_ == 0)
{
lean_dec(v_pre_794_);
lean_inc_ref(v___x_779_);
v___y_781_ = v___x_779_;
goto v___jp_780_;
}
else
{
v___y_781_ = v_pre_794_;
goto v___jp_780_;
}
}
else
{
lean_inc(v___x_779_);
v___y_781_ = v___x_779_;
goto v___jp_780_;
}
v___jp_780_:
{
uint8_t v___x_782_; 
lean_inc_ref(v___y_765_);
v___x_782_ = l_Lean_isExtern(v___y_765_, v___y_781_);
if (v___x_782_ == 0)
{
lean_dec(v___x_779_);
v___y_771_ = v_b_769_;
goto v___jp_770_;
}
else
{
lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_791_; 
lean_inc(v_snd_777_);
lean_inc(v_fst_776_);
v_isSharedCheck_791_ = !lean_is_exclusive(v_b_769_);
if (v_isSharedCheck_791_ == 0)
{
lean_object* v_unused_792_; lean_object* v_unused_793_; 
v_unused_792_ = lean_ctor_get(v_b_769_, 1);
lean_dec(v_unused_792_);
v_unused_793_ = lean_ctor_get(v_b_769_, 0);
lean_dec(v_unused_793_);
v___x_784_ = v_b_769_;
v_isShared_785_ = v_isSharedCheck_791_;
goto v_resetjp_783_;
}
else
{
lean_dec(v_b_769_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_791_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_789_; 
lean_inc_n(v___x_778_, 2);
v___x_786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_778_);
lean_ctor_set(v___x_786_, 1, v_fst_776_);
v___x_787_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1___redArg(v_snd_777_, v___x_779_, v___x_778_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 1, v___x_787_);
lean_ctor_set(v___x_784_, 0, v___x_786_);
v___x_789_ = v___x_784_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_786_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v___x_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
v___y_771_ = v___x_789_;
goto v___jp_770_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_765_);
return v_b_769_;
}
v___jp_770_:
{
size_t v___x_772_; size_t v___x_773_; 
v___x_772_ = ((size_t)1ULL);
v___x_773_ = lean_usize_add(v_i_767_, v___x_772_);
v_i_767_ = v___x_773_;
v_b_769_ = v___y_771_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___boxed(lean_object* v___y_798_, lean_object* v_as_799_, lean_object* v_i_800_, lean_object* v_stop_801_, lean_object* v_b_802_){
_start:
{
size_t v_i_boxed_803_; size_t v_stop_boxed_804_; lean_object* v_res_805_; 
v_i_boxed_803_ = lean_unbox_usize(v_i_800_);
lean_dec(v_i_800_);
v_stop_boxed_804_ = lean_unbox_usize(v_stop_801_);
lean_dec(v_stop_801_);
v_res_805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_798_, v_as_799_, v_i_boxed_803_, v_stop_boxed_804_, v_b_802_);
lean_dec_ref(v_as_799_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(lean_object* v_as_806_, size_t v_i_807_, size_t v_stop_808_, lean_object* v_b_809_){
_start:
{
uint8_t v___x_810_; 
v___x_810_ = lean_usize_dec_eq(v_i_807_, v_stop_808_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; lean_object* v_toEnvExtension_812_; lean_object* v_asyncMode_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; size_t v___x_817_; size_t v___x_818_; 
v___x_811_ = l_Lean_Compiler_LCNF_impureSigExt;
v_toEnvExtension_812_ = lean_ctor_get(v___x_811_, 0);
v_asyncMode_813_ = lean_ctor_get(v_toEnvExtension_812_, 2);
v___x_814_ = lean_box(0);
v___x_815_ = lean_array_uget_borrowed(v_as_806_, v_i_807_);
lean_inc(v___x_815_);
v___x_816_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_811_, v_b_809_, v___x_815_, v_asyncMode_813_, v___x_814_);
v___x_817_ = ((size_t)1ULL);
v___x_818_ = lean_usize_add(v_i_807_, v___x_817_);
v_i_807_ = v___x_818_;
v_b_809_ = v___x_816_;
goto _start;
}
else
{
return v_b_809_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___boxed(lean_object* v_as_820_, lean_object* v_i_821_, lean_object* v_stop_822_, lean_object* v_b_823_){
_start:
{
size_t v_i_boxed_824_; size_t v_stop_boxed_825_; lean_object* v_res_826_; 
v_i_boxed_824_ = lean_unbox_usize(v_i_821_);
lean_dec(v_i_821_);
v_stop_boxed_825_ = lean_unbox_usize(v_stop_822_);
lean_dec(v_stop_822_);
v_res_826_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v_as_820_, v_i_boxed_824_, v_stop_boxed_825_, v_b_823_);
lean_dec_ref(v_as_820_);
return v_res_826_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0(uint8_t v___y_834_, uint8_t v_suppressElabErrors_835_, lean_object* v_x_836_){
_start:
{
if (lean_obj_tag(v_x_836_) == 1)
{
lean_object* v_pre_837_; 
v_pre_837_ = lean_ctor_get(v_x_836_, 0);
switch(lean_obj_tag(v_pre_837_))
{
case 1:
{
lean_object* v_pre_838_; 
v_pre_838_ = lean_ctor_get(v_pre_837_, 0);
switch(lean_obj_tag(v_pre_838_))
{
case 0:
{
lean_object* v_str_839_; lean_object* v_str_840_; lean_object* v___x_841_; uint8_t v___x_842_; 
v_str_839_ = lean_ctor_get(v_x_836_, 1);
v_str_840_ = lean_ctor_get(v_pre_837_, 1);
v___x_841_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__0));
v___x_842_ = lean_string_dec_eq(v_str_840_, v___x_841_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; uint8_t v___x_844_; 
v___x_843_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__1));
v___x_844_ = lean_string_dec_eq(v_str_840_, v___x_843_);
if (v___x_844_ == 0)
{
return v___y_834_;
}
else
{
lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_845_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__2));
v___x_846_ = lean_string_dec_eq(v_str_839_, v___x_845_);
if (v___x_846_ == 0)
{
return v___y_834_;
}
else
{
return v_suppressElabErrors_835_;
}
}
}
else
{
lean_object* v___x_847_; uint8_t v___x_848_; 
v___x_847_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__3));
v___x_848_ = lean_string_dec_eq(v_str_839_, v___x_847_);
if (v___x_848_ == 0)
{
return v___y_834_;
}
else
{
return v_suppressElabErrors_835_;
}
}
}
case 1:
{
lean_object* v_pre_849_; 
v_pre_849_ = lean_ctor_get(v_pre_838_, 0);
if (lean_obj_tag(v_pre_849_) == 0)
{
lean_object* v_str_850_; lean_object* v_str_851_; lean_object* v_str_852_; lean_object* v___x_853_; uint8_t v___x_854_; 
v_str_850_ = lean_ctor_get(v_x_836_, 1);
v_str_851_ = lean_ctor_get(v_pre_837_, 1);
v_str_852_ = lean_ctor_get(v_pre_838_, 1);
v___x_853_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__4));
v___x_854_ = lean_string_dec_eq(v_str_852_, v___x_853_);
if (v___x_854_ == 0)
{
return v___y_834_;
}
else
{
lean_object* v___x_855_; uint8_t v___x_856_; 
v___x_855_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__5));
v___x_856_ = lean_string_dec_eq(v_str_851_, v___x_855_);
if (v___x_856_ == 0)
{
return v___y_834_;
}
else
{
lean_object* v___x_857_; uint8_t v___x_858_; 
v___x_857_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__6));
v___x_858_ = lean_string_dec_eq(v_str_850_, v___x_857_);
if (v___x_858_ == 0)
{
return v___y_834_;
}
else
{
return v_suppressElabErrors_835_;
}
}
}
}
else
{
return v___y_834_;
}
}
default: 
{
return v___y_834_;
}
}
}
case 0:
{
lean_object* v_str_859_; lean_object* v___x_860_; uint8_t v___x_861_; 
v_str_859_ = lean_ctor_get(v_x_836_, 1);
v___x_860_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_861_ = lean_string_dec_eq(v_str_859_, v___x_860_);
if (v___x_861_ == 0)
{
return v___y_834_;
}
else
{
return v_suppressElabErrors_835_;
}
}
default: 
{
return v___y_834_;
}
}
}
else
{
return v___y_834_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___boxed(lean_object* v___y_862_, lean_object* v_suppressElabErrors_863_, lean_object* v_x_864_){
_start:
{
uint8_t v___y_38014__boxed_865_; uint8_t v_suppressElabErrors_boxed_866_; uint8_t v_res_867_; lean_object* v_r_868_; 
v___y_38014__boxed_865_ = lean_unbox(v___y_862_);
v_suppressElabErrors_boxed_866_ = lean_unbox(v_suppressElabErrors_863_);
v_res_867_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0(v___y_38014__boxed_865_, v_suppressElabErrors_boxed_866_, v_x_864_);
lean_dec(v_x_864_);
v_r_868_ = lean_box(v_res_867_);
return v_r_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42(lean_object* v_ref_870_, lean_object* v_msgData_871_, uint8_t v_severity_872_, uint8_t v_isSilent_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v___y_878_; lean_object* v___y_879_; uint8_t v___y_880_; uint8_t v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_914_; uint8_t v___y_915_; lean_object* v___y_916_; uint8_t v___y_917_; uint8_t v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_939_; uint8_t v___y_940_; lean_object* v___y_941_; uint8_t v___y_942_; uint8_t v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_950_; uint8_t v___y_951_; uint8_t v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___y_955_; uint8_t v___y_956_; uint8_t v___x_961_; uint8_t v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; uint8_t v___y_968_; uint8_t v___y_969_; uint8_t v___y_971_; uint8_t v___x_986_; 
v___x_961_ = 2;
v___x_986_ = l_Lean_instBEqMessageSeverity_beq(v_severity_872_, v___x_961_);
if (v___x_986_ == 0)
{
v___y_971_ = v___x_986_;
goto v___jp_970_;
}
else
{
uint8_t v___x_987_; 
lean_inc_ref(v_msgData_871_);
v___x_987_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_871_);
v___y_971_ = v___x_987_;
goto v___jp_970_;
}
v___jp_877_:
{
lean_object* v___x_887_; lean_object* v_currNamespace_888_; lean_object* v_openDecls_889_; lean_object* v_env_890_; lean_object* v_nextMacroScope_891_; lean_object* v_ngen_892_; lean_object* v_auxDeclNGen_893_; lean_object* v_traceState_894_; lean_object* v_cache_895_; lean_object* v_messages_896_; lean_object* v_infoState_897_; lean_object* v_snapshotTasks_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_912_; 
v___x_887_ = lean_st_ref_take(v___y_886_);
v_currNamespace_888_ = lean_ctor_get(v___y_885_, 6);
v_openDecls_889_ = lean_ctor_get(v___y_885_, 7);
v_env_890_ = lean_ctor_get(v___x_887_, 0);
v_nextMacroScope_891_ = lean_ctor_get(v___x_887_, 1);
v_ngen_892_ = lean_ctor_get(v___x_887_, 2);
v_auxDeclNGen_893_ = lean_ctor_get(v___x_887_, 3);
v_traceState_894_ = lean_ctor_get(v___x_887_, 4);
v_cache_895_ = lean_ctor_get(v___x_887_, 5);
v_messages_896_ = lean_ctor_get(v___x_887_, 6);
v_infoState_897_ = lean_ctor_get(v___x_887_, 7);
v_snapshotTasks_898_ = lean_ctor_get(v___x_887_, 8);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_912_ == 0)
{
v___x_900_ = v___x_887_;
v_isShared_901_ = v_isSharedCheck_912_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_snapshotTasks_898_);
lean_inc(v_infoState_897_);
lean_inc(v_messages_896_);
lean_inc(v_cache_895_);
lean_inc(v_traceState_894_);
lean_inc(v_auxDeclNGen_893_);
lean_inc(v_ngen_892_);
lean_inc(v_nextMacroScope_891_);
lean_inc(v_env_890_);
lean_dec(v___x_887_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_912_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_907_; 
lean_inc(v_openDecls_889_);
lean_inc(v_currNamespace_888_);
v___x_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_902_, 0, v_currNamespace_888_);
lean_ctor_set(v___x_902_, 1, v_openDecls_889_);
v___x_903_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
lean_ctor_set(v___x_903_, 1, v___y_882_);
lean_inc_ref(v___y_878_);
lean_inc_ref(v___y_884_);
v___x_904_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_904_, 0, v___y_884_);
lean_ctor_set(v___x_904_, 1, v___y_879_);
lean_ctor_set(v___x_904_, 2, v___y_883_);
lean_ctor_set(v___x_904_, 3, v___y_878_);
lean_ctor_set(v___x_904_, 4, v___x_903_);
lean_ctor_set_uint8(v___x_904_, sizeof(void*)*5, v___y_880_);
lean_ctor_set_uint8(v___x_904_, sizeof(void*)*5 + 1, v___y_881_);
lean_ctor_set_uint8(v___x_904_, sizeof(void*)*5 + 2, v_isSilent_873_);
v___x_905_ = l_Lean_MessageLog_add(v___x_904_, v_messages_896_);
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 6, v___x_905_);
v___x_907_ = v___x_900_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_env_890_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v_nextMacroScope_891_);
lean_ctor_set(v_reuseFailAlloc_911_, 2, v_ngen_892_);
lean_ctor_set(v_reuseFailAlloc_911_, 3, v_auxDeclNGen_893_);
lean_ctor_set(v_reuseFailAlloc_911_, 4, v_traceState_894_);
lean_ctor_set(v_reuseFailAlloc_911_, 5, v_cache_895_);
lean_ctor_set(v_reuseFailAlloc_911_, 6, v___x_905_);
lean_ctor_set(v_reuseFailAlloc_911_, 7, v_infoState_897_);
lean_ctor_set(v_reuseFailAlloc_911_, 8, v_snapshotTasks_898_);
v___x_907_ = v_reuseFailAlloc_911_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_908_ = lean_st_ref_put(v___y_886_, v___x_907_);
v___x_909_ = lean_box(0);
v___x_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_910_, 0, v___x_909_);
return v___x_910_;
}
}
}
v___jp_913_:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_937_; 
v___x_922_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_871_);
v___x_923_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__5_spec__11_spec__15_spec__17(v___x_922_, v___y_874_, v___y_875_);
v_a_924_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_937_ == 0)
{
v___x_926_ = v___x_923_;
v_isShared_927_ = v_isSharedCheck_937_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_923_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_937_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
lean_inc_ref_n(v___y_919_, 2);
v___x_928_ = l_Lean_FileMap_toPosition(v___y_919_, v___y_916_);
lean_dec(v___y_916_);
v___x_929_ = l_Lean_FileMap_toPosition(v___y_919_, v___y_921_);
lean_dec(v___y_921_);
v___x_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
v___x_931_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___closed__0));
if (v___y_915_ == 0)
{
lean_del_object(v___x_926_);
lean_dec_ref(v___y_914_);
v___y_878_ = v___x_931_;
v___y_879_ = v___x_928_;
v___y_880_ = v___y_917_;
v___y_881_ = v___y_918_;
v___y_882_ = v_a_924_;
v___y_883_ = v___x_930_;
v___y_884_ = v___y_920_;
v___y_885_ = v___y_874_;
v___y_886_ = v___y_875_;
goto v___jp_877_;
}
else
{
uint8_t v___x_932_; 
lean_inc(v_a_924_);
v___x_932_ = l_Lean_MessageData_hasTag(v___y_914_, v_a_924_);
if (v___x_932_ == 0)
{
lean_object* v___x_933_; lean_object* v___x_935_; 
lean_dec_ref_known(v___x_930_, 1);
lean_dec_ref(v___x_928_);
lean_dec(v_a_924_);
v___x_933_ = lean_box(0);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 0, v___x_933_);
v___x_935_ = v___x_926_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_933_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
else
{
lean_del_object(v___x_926_);
v___y_878_ = v___x_931_;
v___y_879_ = v___x_928_;
v___y_880_ = v___y_917_;
v___y_881_ = v___y_918_;
v___y_882_ = v_a_924_;
v___y_883_ = v___x_930_;
v___y_884_ = v___y_920_;
v___y_885_ = v___y_874_;
v___y_886_ = v___y_875_;
goto v___jp_877_;
}
}
}
}
v___jp_938_:
{
lean_object* v___x_947_; 
v___x_947_ = l_Lean_Syntax_getTailPos_x3f(v___y_941_, v___y_942_);
lean_dec(v___y_941_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_inc(v___y_946_);
v___y_914_ = v___y_939_;
v___y_915_ = v___y_940_;
v___y_916_ = v___y_946_;
v___y_917_ = v___y_942_;
v___y_918_ = v___y_943_;
v___y_919_ = v___y_944_;
v___y_920_ = v___y_945_;
v___y_921_ = v___y_946_;
goto v___jp_913_;
}
else
{
lean_object* v_val_948_; 
v_val_948_ = lean_ctor_get(v___x_947_, 0);
lean_inc(v_val_948_);
lean_dec_ref_known(v___x_947_, 1);
v___y_914_ = v___y_939_;
v___y_915_ = v___y_940_;
v___y_916_ = v___y_946_;
v___y_917_ = v___y_942_;
v___y_918_ = v___y_943_;
v___y_919_ = v___y_944_;
v___y_920_ = v___y_945_;
v___y_921_ = v_val_948_;
goto v___jp_913_;
}
}
v___jp_949_:
{
lean_object* v_ref_957_; lean_object* v___x_958_; 
v_ref_957_ = l_Lean_replaceRef(v_ref_870_, v___y_954_);
v___x_958_ = l_Lean_Syntax_getPos_x3f(v_ref_957_, v___y_952_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v___x_959_; 
v___x_959_ = lean_unsigned_to_nat(0u);
v___y_939_ = v___y_950_;
v___y_940_ = v___y_951_;
v___y_941_ = v_ref_957_;
v___y_942_ = v___y_952_;
v___y_943_ = v___y_956_;
v___y_944_ = v___y_953_;
v___y_945_ = v___y_955_;
v___y_946_ = v___x_959_;
goto v___jp_938_;
}
else
{
lean_object* v_val_960_; 
v_val_960_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_val_960_);
lean_dec_ref_known(v___x_958_, 1);
v___y_939_ = v___y_950_;
v___y_940_ = v___y_951_;
v___y_941_ = v_ref_957_;
v___y_942_ = v___y_952_;
v___y_943_ = v___y_956_;
v___y_944_ = v___y_953_;
v___y_945_ = v___y_955_;
v___y_946_ = v_val_960_;
goto v___jp_938_;
}
}
v___jp_962_:
{
if (v___y_969_ == 0)
{
v___y_950_ = v___y_966_;
v___y_951_ = v___y_963_;
v___y_952_ = v___y_968_;
v___y_953_ = v___y_964_;
v___y_954_ = v___y_965_;
v___y_955_ = v___y_967_;
v___y_956_ = v_severity_872_;
goto v___jp_949_;
}
else
{
v___y_950_ = v___y_966_;
v___y_951_ = v___y_963_;
v___y_952_ = v___y_968_;
v___y_953_ = v___y_964_;
v___y_954_ = v___y_965_;
v___y_955_ = v___y_967_;
v___y_956_ = v___x_961_;
goto v___jp_949_;
}
}
v___jp_970_:
{
if (v___y_971_ == 0)
{
lean_object* v_fileName_972_; lean_object* v_fileMap_973_; lean_object* v_options_974_; lean_object* v_ref_975_; uint8_t v_suppressElabErrors_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___f_979_; uint8_t v___x_980_; uint8_t v___x_981_; 
v_fileName_972_ = lean_ctor_get(v___y_874_, 0);
v_fileMap_973_ = lean_ctor_get(v___y_874_, 1);
v_options_974_ = lean_ctor_get(v___y_874_, 2);
v_ref_975_ = lean_ctor_get(v___y_874_, 5);
v_suppressElabErrors_976_ = lean_ctor_get_uint8(v___y_874_, sizeof(void*)*14 + 1);
v___x_977_ = lean_box(v___y_971_);
v___x_978_ = lean_box(v_suppressElabErrors_976_);
v___f_979_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___boxed), 3, 2);
lean_closure_set(v___f_979_, 0, v___x_977_);
lean_closure_set(v___f_979_, 1, v___x_978_);
v___x_980_ = 1;
v___x_981_ = l_Lean_instBEqMessageSeverity_beq(v_severity_872_, v___x_980_);
if (v___x_981_ == 0)
{
v___y_963_ = v_suppressElabErrors_976_;
v___y_964_ = v_fileMap_973_;
v___y_965_ = v_ref_975_;
v___y_966_ = v___f_979_;
v___y_967_ = v_fileName_972_;
v___y_968_ = v___y_971_;
v___y_969_ = v___x_981_;
goto v___jp_962_;
}
else
{
lean_object* v___x_982_; uint8_t v___x_983_; 
v___x_982_ = l_Lean_warningAsError;
v___x_983_ = l_Lean_Option_get___at___00main_spec__7(v_options_974_, v___x_982_);
v___y_963_ = v_suppressElabErrors_976_;
v___y_964_ = v_fileMap_973_;
v___y_965_ = v_ref_975_;
v___y_966_ = v___f_979_;
v___y_967_ = v_fileName_972_;
v___y_968_ = v___y_971_;
v___y_969_ = v___x_983_;
goto v___jp_962_;
}
}
else
{
lean_object* v___x_984_; lean_object* v___x_985_; 
lean_dec_ref(v_msgData_871_);
v___x_984_ = lean_box(0);
v___x_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_985_, 0, v___x_984_);
return v___x_985_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___boxed(lean_object* v_ref_988_, lean_object* v_msgData_989_, lean_object* v_severity_990_, lean_object* v_isSilent_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
uint8_t v_severity_boxed_995_; uint8_t v_isSilent_boxed_996_; lean_object* v_res_997_; 
v_severity_boxed_995_ = lean_unbox(v_severity_990_);
v_isSilent_boxed_996_ = lean_unbox(v_isSilent_991_);
v_res_997_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42(v_ref_988_, v_msgData_989_, v_severity_boxed_995_, v_isSilent_boxed_996_, v___y_992_, v___y_993_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v_ref_988_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28(lean_object* v_msgData_998_, uint8_t v_severity_999_, uint8_t v_isSilent_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v_ref_1004_; lean_object* v___x_1005_; 
v_ref_1004_ = lean_ctor_get(v___y_1001_, 5);
v___x_1005_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42(v_ref_1004_, v_msgData_998_, v_severity_999_, v_isSilent_1000_, v___y_1001_, v___y_1002_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28___boxed(lean_object* v_msgData_1006_, lean_object* v_severity_1007_, lean_object* v_isSilent_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
uint8_t v_severity_boxed_1012_; uint8_t v_isSilent_boxed_1013_; lean_object* v_res_1014_; 
v_severity_boxed_1012_ = lean_unbox(v_severity_1007_);
v_isSilent_boxed_1013_ = lean_unbox(v_isSilent_1008_);
v_res_1014_ = l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28(v_msgData_1006_, v_severity_boxed_1012_, v_isSilent_boxed_1013_, v___y_1009_, v___y_1010_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__13(lean_object* v_msgData_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
uint8_t v___x_1019_; uint8_t v___x_1020_; lean_object* v___x_1021_; 
v___x_1019_ = 2;
v___x_1020_ = 0;
v___x_1021_ = l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28(v_msgData_1015_, v___x_1019_, v___x_1020_, v___y_1016_, v___y_1017_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__13___boxed(lean_object* v_msgData_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_logError___at___00main_spec__13(v_msgData_1022_, v___y_1023_, v___y_1024_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16_spec__21___redArg(lean_object* v_m_1027_, lean_object* v_query_1028_, lean_object* v_x_1029_, lean_object* v_x_1030_, lean_object* v_x_1031_){
_start:
{
lean_object* v_zero_1032_; uint8_t v_isZero_1033_; 
v_zero_1032_ = lean_unsigned_to_nat(0u);
v_isZero_1033_ = lean_nat_dec_eq(v_x_1030_, v_zero_1032_);
if (v_isZero_1033_ == 1)
{
lean_dec(v_x_1031_);
lean_dec(v_x_1030_);
if (lean_obj_tag(v_x_1029_) == 0)
{
lean_object* v___x_1034_; 
v___x_1034_ = lean_box(2);
return v___x_1034_;
}
else
{
lean_object* v_val_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
v_val_1035_ = lean_ctor_get(v_x_1029_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v_x_1029_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v_x_1029_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_val_1035_);
lean_dec(v_x_1029_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_val_1035_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
else
{
lean_object* v_keyArray_1043_; lean_object* v_valueArray_1044_; lean_object* v___x_1045_; uint8_t v_isSome_1046_; 
v_keyArray_1043_ = lean_ctor_get(v_m_1027_, 1);
v_valueArray_1044_ = lean_ctor_get(v_m_1027_, 2);
v___x_1045_ = lean_array_fget_borrowed(v_keyArray_1043_, v_x_1031_);
v_isSome_1046_ = lean_noption_is_some(v___x_1045_);
if (v_isSome_1046_ == 0)
{
lean_dec(v_x_1030_);
if (lean_obj_tag(v_x_1029_) == 0)
{
lean_object* v___x_1047_; 
v___x_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1047_, 0, v_x_1031_);
return v___x_1047_;
}
else
{
lean_object* v_val_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
lean_dec(v_x_1031_);
v_val_1048_ = lean_ctor_get(v_x_1029_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v_x_1029_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v_x_1029_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_val_1048_);
lean_dec(v_x_1029_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_val_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
else
{
lean_object* v_one_1056_; lean_object* v_n_1057_; lean_object* v___y_1059_; 
v_one_1056_ = lean_unsigned_to_nat(1u);
v_n_1057_ = lean_nat_sub(v_x_1030_, v_one_1056_);
lean_dec(v_x_1030_);
if (v_isSome_1046_ == 0)
{
goto v___jp_1065_;
}
else
{
lean_object* v___x_1067_; uint8_t v_isSome_1068_; 
v___x_1067_ = lean_array_fget_borrowed(v_valueArray_1044_, v_x_1031_);
v_isSome_1068_ = lean_noption_is_some(v___x_1067_);
if (v_isSome_1068_ == 0)
{
goto v___jp_1065_;
}
else
{
lean_object* v_val_1069_; lean_object* v_fst_1070_; lean_object* v_snd_1071_; lean_object* v_fst_1072_; lean_object* v_snd_1073_; lean_object* v_val_1074_; uint8_t v___y_1076_; uint8_t v___x_1083_; 
lean_inc(v___x_1045_);
v_val_1069_ = lean_noption_get(v___x_1045_);
v_fst_1070_ = lean_ctor_get(v_val_1069_, 0);
lean_inc(v_fst_1070_);
v_snd_1071_ = lean_ctor_get(v_val_1069_, 1);
lean_inc(v_snd_1071_);
v_fst_1072_ = lean_ctor_get(v_query_1028_, 0);
v_snd_1073_ = lean_ctor_get(v_query_1028_, 1);
lean_inc(v___x_1067_);
v_val_1074_ = lean_noption_get(v___x_1067_);
v___x_1083_ = lean_nat_dec_eq(v_fst_1070_, v_fst_1072_);
lean_dec(v_fst_1070_);
if (v___x_1083_ == 0)
{
lean_dec(v_snd_1071_);
v___y_1076_ = v___x_1083_;
goto v___jp_1075_;
}
else
{
uint8_t v___x_1084_; 
v___x_1084_ = lean_nat_dec_eq(v_snd_1071_, v_snd_1073_);
lean_dec(v_snd_1071_);
v___y_1076_ = v___x_1084_;
goto v___jp_1075_;
}
v___jp_1075_:
{
if (v___y_1076_ == 0)
{
lean_object* v___x_1077_; lean_object* v___x_1078_; uint8_t v___x_1079_; 
lean_dec(v_val_1074_);
lean_dec(v_val_1069_);
v___x_1077_ = lean_array_get_size(v_keyArray_1043_);
v___x_1078_ = lean_nat_add(v_x_1031_, v_one_1056_);
lean_dec(v_x_1031_);
v___x_1079_ = lean_nat_dec_lt(v___x_1078_, v___x_1077_);
if (v___x_1079_ == 0)
{
lean_dec(v___x_1078_);
v_x_1030_ = v_n_1057_;
v_x_1031_ = v_zero_1032_;
goto _start;
}
else
{
v_x_1030_ = v_n_1057_;
v_x_1031_ = v___x_1078_;
goto _start;
}
}
else
{
lean_object* v___x_1082_; 
lean_dec(v_n_1057_);
lean_dec(v_x_1029_);
v___x_1082_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1082_, 0, v_x_1031_);
lean_ctor_set(v___x_1082_, 1, v_val_1069_);
lean_ctor_set(v___x_1082_, 2, v_val_1074_);
return v___x_1082_;
}
}
}
}
v___jp_1058_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; 
v___x_1060_ = lean_array_get_size(v_keyArray_1043_);
v___x_1061_ = lean_nat_add(v_x_1031_, v_one_1056_);
lean_dec(v_x_1031_);
v___x_1062_ = lean_nat_dec_lt(v___x_1061_, v___x_1060_);
if (v___x_1062_ == 0)
{
lean_dec(v___x_1061_);
v_x_1029_ = v___y_1059_;
v_x_1030_ = v_n_1057_;
v_x_1031_ = v_zero_1032_;
goto _start;
}
else
{
v_x_1029_ = v___y_1059_;
v_x_1030_ = v_n_1057_;
v_x_1031_ = v___x_1061_;
goto _start;
}
}
v___jp_1065_:
{
if (lean_obj_tag(v_x_1029_) == 0)
{
lean_object* v___x_1066_; 
lean_inc(v_x_1031_);
v___x_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1066_, 0, v_x_1031_);
v___y_1059_ = v___x_1066_;
goto v___jp_1058_;
}
else
{
v___y_1059_ = v_x_1029_;
goto v___jp_1058_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16_spec__21___redArg___boxed(lean_object* v_m_1085_, lean_object* v_query_1086_, lean_object* v_x_1087_, lean_object* v_x_1088_, lean_object* v_x_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16_spec__21___redArg(v_m_1085_, v_query_1086_, v_x_1087_, v_x_1088_, v_x_1089_);
lean_dec_ref(v_query_1086_);
lean_dec_ref(v_m_1085_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(lean_object* v_m_1091_, lean_object* v_query_1092_){
_start:
{
lean_object* v_keyArray_1093_; lean_object* v_fst_1094_; lean_object* v_snd_1095_; lean_object* v___x_1096_; uint64_t v___x_1097_; uint64_t v___x_1098_; uint64_t v___x_1099_; uint64_t v___x_1100_; uint64_t v___x_1101_; uint64_t v_fold_1102_; uint64_t v___x_1103_; uint64_t v___x_1104_; uint64_t v___x_1105_; size_t v___x_1106_; size_t v___x_1107_; size_t v___x_1108_; size_t v___x_1109_; size_t v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v_keyArray_1093_ = lean_ctor_get(v_m_1091_, 1);
v_fst_1094_ = lean_ctor_get(v_query_1092_, 0);
v_snd_1095_ = lean_ctor_get(v_query_1092_, 1);
v___x_1096_ = lean_array_get_size(v_keyArray_1093_);
v___x_1097_ = l_String_instHashableRaw_hash(v_fst_1094_);
v___x_1098_ = l_String_instHashableRaw_hash(v_snd_1095_);
v___x_1099_ = lean_uint64_mix_hash(v___x_1097_, v___x_1098_);
v___x_1100_ = 32ULL;
v___x_1101_ = lean_uint64_shift_right(v___x_1099_, v___x_1100_);
v_fold_1102_ = lean_uint64_xor(v___x_1099_, v___x_1101_);
v___x_1103_ = 16ULL;
v___x_1104_ = lean_uint64_shift_right(v_fold_1102_, v___x_1103_);
v___x_1105_ = lean_uint64_xor(v_fold_1102_, v___x_1104_);
v___x_1106_ = lean_uint64_to_usize(v___x_1105_);
v___x_1107_ = lean_usize_of_nat(v___x_1096_);
v___x_1108_ = ((size_t)1ULL);
v___x_1109_ = lean_usize_sub(v___x_1107_, v___x_1108_);
v___x_1110_ = lean_usize_land(v___x_1106_, v___x_1109_);
v___x_1111_ = lean_usize_to_nat(v___x_1110_);
v___x_1112_ = lean_box(0);
v___x_1113_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16_spec__21___redArg(v_m_1091_, v_query_1092_, v___x_1112_, v___x_1096_, v___x_1111_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___boxed(lean_object* v_m_1114_, lean_object* v_query_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v_m_1114_, v_query_1115_);
lean_dec_ref(v_query_1115_);
lean_dec_ref(v_m_1114_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23_spec__35___redArg(lean_object* v_b_1117_, lean_object* v_acc_1118_, lean_object* v_i_1119_){
_start:
{
lean_object* v___y_1121_; lean_object* v_keyArray_1129_; lean_object* v_valueArray_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
v_keyArray_1129_ = lean_ctor_get(v_b_1117_, 1);
v_valueArray_1130_ = lean_ctor_get(v_b_1117_, 2);
v___x_1131_ = lean_array_get_size(v_keyArray_1129_);
v___x_1132_ = lean_nat_dec_lt(v_i_1119_, v___x_1131_);
if (v___x_1132_ == 0)
{
lean_dec(v_i_1119_);
return v_acc_1118_;
}
else
{
lean_object* v___x_1133_; uint8_t v_isSome_1134_; 
v___x_1133_ = lean_array_fget_borrowed(v_keyArray_1129_, v_i_1119_);
v_isSome_1134_ = lean_noption_is_some(v___x_1133_);
if (v_isSome_1134_ == 0)
{
goto v___jp_1125_;
}
else
{
lean_object* v___x_1135_; uint8_t v_isSome_1136_; 
v___x_1135_ = lean_array_fget_borrowed(v_valueArray_1130_, v_i_1119_);
v_isSome_1136_ = lean_noption_is_some(v___x_1135_);
if (v_isSome_1136_ == 0)
{
goto v___jp_1125_;
}
else
{
lean_object* v_val_1137_; lean_object* v_val_1138_; lean_object* v_i_1140_; lean_object* v___x_1145_; 
lean_inc(v___x_1133_);
v_val_1137_ = lean_noption_get(v___x_1133_);
lean_inc(v___x_1135_);
v_val_1138_ = lean_noption_get(v___x_1135_);
v___x_1145_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v_acc_1118_, v_val_1137_);
switch(lean_obj_tag(v___x_1145_))
{
case 0:
{
lean_object* v_index_1146_; lean_object* v_size_1147_; lean_object* v___x_1148_; 
v_index_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_index_1146_);
lean_dec_ref_known(v___x_1145_, 3);
v_size_1147_ = lean_ctor_get(v_acc_1118_, 0);
lean_inc(v_size_1147_);
v___x_1148_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1118_, v_size_1147_, v_index_1146_, v_val_1137_, v_val_1138_);
lean_dec(v_index_1146_);
v___y_1121_ = v___x_1148_;
goto v___jp_1120_;
}
case 1:
{
lean_object* v_index_1149_; 
v_index_1149_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_index_1149_);
lean_dec_ref_known(v___x_1145_, 1);
v_i_1140_ = v_index_1149_;
goto v___jp_1139_;
}
default: 
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = lean_unsigned_to_nat(0u);
v___x_1151_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_1118_, v___x_1150_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v_index_1152_; 
v_index_1152_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_index_1152_);
lean_dec_ref_known(v___x_1151_, 1);
v_i_1140_ = v_index_1152_;
goto v___jp_1139_;
}
else
{
lean_dec(v_val_1138_);
lean_dec(v_val_1137_);
v___y_1121_ = v_acc_1118_;
goto v___jp_1120_;
}
}
}
v___jp_1139_:
{
lean_object* v_size_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v_size_1141_ = lean_ctor_get(v_acc_1118_, 0);
v___x_1142_ = lean_unsigned_to_nat(1u);
v___x_1143_ = lean_nat_add(v_size_1141_, v___x_1142_);
v___x_1144_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1118_, v___x_1143_, v_i_1140_, v_val_1137_, v_val_1138_);
lean_dec(v_i_1140_);
v___y_1121_ = v___x_1144_;
goto v___jp_1120_;
}
}
}
}
v___jp_1120_:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = lean_unsigned_to_nat(1u);
v___x_1123_ = lean_nat_add(v_i_1119_, v___x_1122_);
lean_dec(v_i_1119_);
v_acc_1118_ = v___y_1121_;
v_i_1119_ = v___x_1123_;
goto _start;
}
v___jp_1125_:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1126_ = lean_unsigned_to_nat(1u);
v___x_1127_ = lean_nat_add(v_i_1119_, v___x_1126_);
lean_dec(v_i_1119_);
v_i_1119_ = v___x_1127_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23_spec__35___redArg___boxed(lean_object* v_b_1153_, lean_object* v_acc_1154_, lean_object* v_i_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23_spec__35___redArg(v_b_1153_, v_acc_1154_, v_i_1155_);
lean_dec_ref(v_b_1153_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23___redArg(lean_object* v_init_1157_, lean_object* v_b_1158_){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = lean_unsigned_to_nat(0u);
v___x_1160_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23_spec__35___redArg(v_b_1158_, v_init_1157_, v___x_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23___redArg___boxed(lean_object* v_init_1161_, lean_object* v_b_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23___redArg(v_init_1161_, v_b_1162_);
lean_dec_ref(v_b_1162_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(lean_object* v_m_1164_){
_start:
{
lean_object* v_keyArray_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v_cellCount_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v_target_1172_; lean_object* v___x_1173_; 
v_keyArray_1165_ = lean_ctor_get(v_m_1164_, 1);
v___x_1166_ = lean_array_get_size(v_keyArray_1165_);
v___x_1167_ = lean_unsigned_to_nat(2u);
v_cellCount_1168_ = lean_nat_mul(v___x_1166_, v___x_1167_);
v___x_1169_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_1168_);
v___x_1170_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1168_);
v___x_1171_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1168_);
v_target_1172_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_1172_, 0, v___x_1169_);
lean_ctor_set(v_target_1172_, 1, v___x_1170_);
lean_ctor_set(v_target_1172_, 2, v___x_1171_);
v___x_1173_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23___redArg(v_target_1172_, v_m_1164_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg___boxed(lean_object* v_m_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_m_1174_);
lean_dec_ref(v_m_1174_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15_spec__19_spec__30___redArg(lean_object* v_m_1176_, lean_object* v_query_1177_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v_m_1176_, v_query_1177_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v_index_1179_; lean_object* v_key_1180_; lean_object* v_value_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
v_index_1179_ = lean_ctor_get(v___x_1178_, 0);
v_key_1180_ = lean_ctor_get(v___x_1178_, 1);
v_value_1181_ = lean_ctor_get(v___x_1178_, 2);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_1178_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_value_1181_);
lean_inc(v_key_1180_);
lean_inc(v_index_1179_);
lean_dec(v___x_1178_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_index_1179_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v_key_1180_);
lean_ctor_set(v_reuseFailAlloc_1187_, 2, v_value_1181_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
else
{
lean_object* v___x_1189_; 
lean_dec(v___x_1178_);
v___x_1189_ = lean_box(1);
return v___x_1189_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15_spec__19_spec__30___redArg___boxed(lean_object* v_m_1190_, lean_object* v_query_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15_spec__19_spec__30___redArg(v_m_1190_, v_query_1191_);
lean_dec_ref(v_query_1191_);
lean_dec_ref(v_m_1190_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15_spec__19___redArg(lean_object* v_m_1193_, lean_object* v_a_1194_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15_spec__19_spec__30___redArg(v_m_1193_, v_a_1194_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v_value_1196_; lean_object* v___x_1197_; 
v_value_1196_ = lean_ctor_get(v___x_1195_, 2);
lean_inc(v_value_1196_);
lean_dec_ref_known(v___x_1195_, 3);
v___x_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1197_, 0, v_value_1196_);
return v___x_1197_;
}
else
{
lean_object* v___x_1198_; 
v___x_1198_ = lean_box(0);
return v___x_1198_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15_spec__19___redArg___boxed(lean_object* v_m_1199_, lean_object* v_a_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15_spec__19___redArg(v_m_1199_, v_a_1200_);
lean_dec_ref(v_a_1200_);
lean_dec_ref(v_m_1199_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg(lean_object* v_m_1202_, lean_object* v_a_1203_, lean_object* v_fallback_1204_){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15_spec__19___redArg(v_m_1202_, v_a_1203_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_inc(v_fallback_1204_);
return v_fallback_1204_;
}
else
{
lean_object* v_val_1206_; 
v_val_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_val_1206_);
lean_dec_ref_known(v___x_1205_, 1);
return v_val_1206_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg___boxed(lean_object* v_m_1207_, lean_object* v_a_1208_, lean_object* v_fallback_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg(v_m_1207_, v_a_1208_, v_fallback_1209_);
lean_dec(v_fallback_1209_);
lean_dec_ref(v_a_1208_);
lean_dec_ref(v_m_1207_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25_spec__39_spec__46___redArg(uint8_t v___x_1213_, lean_object* v_as_1214_, size_t v_sz_1215_, size_t v_i_1216_, lean_object* v_b_1217_, lean_object* v___y_1218_){
_start:
{
uint8_t v___x_1220_; 
v___x_1220_ = lean_usize_dec_lt(v_i_1216_, v_sz_1215_);
if (v___x_1220_ == 0)
{
lean_object* v___x_1221_; 
v___x_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1221_, 0, v_b_1217_);
return v___x_1221_;
}
else
{
lean_object* v_snd_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1333_; 
v_snd_1222_ = lean_ctor_get(v_b_1217_, 1);
v_isSharedCheck_1333_ = !lean_is_exclusive(v_b_1217_);
if (v_isSharedCheck_1333_ == 0)
{
lean_object* v_unused_1334_; 
v_unused_1334_ = lean_ctor_get(v_b_1217_, 0);
lean_dec(v_unused_1334_);
v___x_1224_ = v_b_1217_;
v_isShared_1225_ = v_isSharedCheck_1333_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_snd_1222_);
lean_dec(v_b_1217_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1333_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v_ref_1226_; lean_object* v_a_1227_; lean_object* v_ref_1228_; lean_object* v_msg_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1332_; 
v_ref_1226_ = lean_ctor_get(v___y_1218_, 5);
v_a_1227_ = lean_array_uget(v_as_1214_, v_i_1216_);
v_ref_1228_ = lean_ctor_get(v_a_1227_, 0);
v_msg_1229_ = lean_ctor_get(v_a_1227_, 1);
v_isSharedCheck_1332_ = !lean_is_exclusive(v_a_1227_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1231_ = v_a_1227_;
v_isShared_1232_ = v_isSharedCheck_1332_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_msg_1229_);
lean_inc(v_ref_1228_);
lean_dec(v_a_1227_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1332_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1233_; lean_object* v___y_1235_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v_i_1246_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1264_; lean_object* v___y_1265_; lean_object* v___y_1266_; lean_object* v_i_1267_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1285_; lean_object* v___y_1286_; lean_object* v_ref_1324_; lean_object* v___y_1326_; lean_object* v___x_1329_; 
v___x_1233_ = lean_box(0);
v_ref_1324_ = l_Lean_replaceRef(v_ref_1228_, v_ref_1226_);
lean_dec(v_ref_1228_);
v___x_1329_ = l_Lean_Syntax_getPos_x3f(v_ref_1324_, v___x_1213_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v___x_1330_; 
v___x_1330_ = lean_unsigned_to_nat(0u);
v___y_1326_ = v___x_1330_;
goto v___jp_1325_;
}
else
{
lean_object* v_val_1331_; 
v_val_1331_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_val_1331_);
lean_dec_ref_known(v___x_1329_, 1);
v___y_1326_ = v_val_1331_;
goto v___jp_1325_;
}
v___jp_1234_:
{
lean_object* v___x_1237_; 
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 1, v___y_1235_);
lean_ctor_set(v___x_1224_, 0, v___x_1233_);
v___x_1237_ = v___x_1224_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1233_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v___y_1235_);
v___x_1237_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
size_t v___x_1238_; size_t v___x_1239_; 
v___x_1238_ = ((size_t)1ULL);
v___x_1239_ = lean_usize_add(v_i_1216_, v___x_1238_);
v_i_1216_ = v___x_1239_;
v_b_1217_ = v___x_1237_;
goto _start;
}
}
v___jp_1242_:
{
lean_object* v_size_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v_size_1247_ = lean_ctor_get(v___y_1244_, 0);
v___x_1248_ = lean_unsigned_to_nat(1u);
v___x_1249_ = lean_nat_add(v_size_1247_, v___x_1248_);
v___x_1250_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1244_, v___x_1249_, v_i_1246_, v___y_1243_, v___y_1245_);
lean_dec(v_i_1246_);
v___y_1235_ = v___x_1250_;
goto v___jp_1234_;
}
v___jp_1251_:
{
lean_object* v___x_1256_; 
v___x_1256_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v___y_1255_, v___y_1252_);
switch(lean_obj_tag(v___x_1256_))
{
case 0:
{
lean_object* v_index_1257_; lean_object* v_size_1258_; lean_object* v___x_1259_; 
lean_dec(v___y_1254_);
v_index_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_index_1257_);
lean_dec_ref_known(v___x_1256_, 3);
v_size_1258_ = lean_ctor_get(v___y_1255_, 0);
lean_inc(v_size_1258_);
v___x_1259_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1255_, v_size_1258_, v_index_1257_, v___y_1252_, v___y_1253_);
lean_dec(v_index_1257_);
v___y_1235_ = v___x_1259_;
goto v___jp_1234_;
}
case 1:
{
lean_object* v_index_1260_; 
lean_dec(v___y_1254_);
v_index_1260_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_index_1260_);
lean_dec_ref_known(v___x_1256_, 1);
v___y_1243_ = v___y_1252_;
v___y_1244_ = v___y_1255_;
v___y_1245_ = v___y_1253_;
v_i_1246_ = v_index_1260_;
goto v___jp_1242_;
}
default: 
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1255_, v___y_1254_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_index_1262_; 
v_index_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_index_1262_);
lean_dec_ref_known(v___x_1261_, 1);
v___y_1243_ = v___y_1252_;
v___y_1244_ = v___y_1255_;
v___y_1245_ = v___y_1253_;
v_i_1246_ = v_index_1262_;
goto v___jp_1242_;
}
else
{
lean_dec_ref(v___y_1253_);
lean_dec_ref(v___y_1252_);
v___y_1235_ = v___y_1255_;
goto v___jp_1234_;
}
}
}
}
v___jp_1263_:
{
lean_object* v_size_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v_size_1268_ = lean_ctor_get(v___y_1266_, 0);
v___x_1269_ = lean_unsigned_to_nat(1u);
v___x_1270_ = lean_nat_add(v_size_1268_, v___x_1269_);
v___x_1271_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1266_, v___x_1270_, v_i_1267_, v___y_1264_, v___y_1265_);
lean_dec(v_i_1267_);
v___y_1235_ = v___x_1271_;
goto v___jp_1234_;
}
v___jp_1272_:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_1222_);
lean_dec(v_snd_1222_);
v___x_1277_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v___x_1276_, v___y_1273_);
switch(lean_obj_tag(v___x_1277_))
{
case 0:
{
lean_object* v_index_1278_; lean_object* v_size_1279_; lean_object* v___x_1280_; 
lean_dec(v___y_1275_);
v_index_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_index_1278_);
lean_dec_ref_known(v___x_1277_, 3);
v_size_1279_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_size_1279_);
v___x_1280_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1276_, v_size_1279_, v_index_1278_, v___y_1273_, v___y_1274_);
lean_dec(v_index_1278_);
v___y_1235_ = v___x_1280_;
goto v___jp_1234_;
}
case 1:
{
lean_object* v_index_1281_; 
lean_dec(v___y_1275_);
v_index_1281_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_index_1281_);
lean_dec_ref_known(v___x_1277_, 1);
v___y_1264_ = v___y_1273_;
v___y_1265_ = v___y_1274_;
v___y_1266_ = v___x_1276_;
v_i_1267_ = v_index_1281_;
goto v___jp_1263_;
}
default: 
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1276_, v___y_1275_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_index_1283_; 
v_index_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_index_1283_);
lean_dec_ref_known(v___x_1282_, 1);
v___y_1264_ = v___y_1273_;
v___y_1265_ = v___y_1274_;
v___y_1266_ = v___x_1276_;
v_i_1267_ = v_index_1283_;
goto v___jp_1263_;
}
else
{
lean_dec_ref(v___y_1274_);
lean_dec_ref(v___y_1273_);
v___y_1235_ = v___x_1276_;
goto v___jp_1234_;
}
}
}
}
v___jp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 1, v___y_1286_);
lean_ctor_set(v___x_1231_, 0, v___y_1285_);
v___x_1288_ = v___x_1231_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___y_1285_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v___y_1286_);
v___x_1288_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1289_ = lean_unsigned_to_nat(0u);
v___x_1290_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25_spec__39_spec__46___redArg___closed__0));
v___x_1291_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg(v_snd_1222_, v___x_1288_, v___x_1290_);
v___x_1292_ = lean_array_push(v___x_1291_, v_msg_1229_);
v___x_1293_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v_snd_1222_, v___x_1288_);
switch(lean_obj_tag(v___x_1293_))
{
case 0:
{
lean_object* v_index_1294_; lean_object* v_size_1295_; lean_object* v___x_1296_; 
v_index_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_index_1294_);
lean_dec_ref_known(v___x_1293_, 3);
v_size_1295_ = lean_ctor_get(v_snd_1222_, 0);
lean_inc(v_size_1295_);
v___x_1296_ = l_Std_DHashMap_Raw_setEntry___redArg(v_snd_1222_, v_size_1295_, v_index_1294_, v___x_1288_, v___x_1292_);
lean_dec(v_index_1294_);
v___y_1235_ = v___x_1296_;
goto v___jp_1234_;
}
case 1:
{
lean_object* v_index_1297_; lean_object* v_size_1298_; lean_object* v_keyArray_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; uint8_t v___x_1303_; 
v_index_1297_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_index_1297_);
lean_dec_ref_known(v___x_1293_, 1);
v_size_1298_ = lean_ctor_get(v_snd_1222_, 0);
v_keyArray_1299_ = lean_ctor_get(v_snd_1222_, 1);
v___x_1300_ = lean_unsigned_to_nat(1u);
v___x_1301_ = lean_nat_add(v_size_1298_, v___x_1300_);
v___x_1302_ = lean_array_get_size(v_keyArray_1299_);
v___x_1303_ = lean_nat_dec_lt(v___x_1301_, v___x_1302_);
if (v___x_1303_ == 0)
{
lean_dec(v___x_1301_);
lean_dec(v_index_1297_);
v___y_1273_ = v___x_1288_;
v___y_1274_ = v___x_1292_;
v___y_1275_ = v___x_1289_;
goto v___jp_1272_;
}
else
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1304_ = lean_unsigned_to_nat(4u);
v___x_1305_ = lean_nat_mul(v___x_1301_, v___x_1304_);
v___x_1306_ = lean_unsigned_to_nat(3u);
v___x_1307_ = lean_nat_mul(v___x_1302_, v___x_1306_);
v___x_1308_ = lean_nat_dec_le(v___x_1305_, v___x_1307_);
lean_dec(v___x_1307_);
lean_dec(v___x_1305_);
if (v___x_1308_ == 0)
{
lean_dec(v___x_1301_);
lean_dec(v_index_1297_);
v___y_1273_ = v___x_1288_;
v___y_1274_ = v___x_1292_;
v___y_1275_ = v___x_1289_;
goto v___jp_1272_;
}
else
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Std_DHashMap_Raw_setEntry___redArg(v_snd_1222_, v___x_1301_, v_index_1297_, v___x_1288_, v___x_1292_);
lean_dec(v_index_1297_);
v___y_1235_ = v___x_1309_;
goto v___jp_1234_;
}
}
}
default: 
{
lean_object* v_size_1310_; lean_object* v_keyArray_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; uint8_t v___x_1315_; 
v_size_1310_ = lean_ctor_get(v_snd_1222_, 0);
v_keyArray_1311_ = lean_ctor_get(v_snd_1222_, 1);
v___x_1312_ = lean_unsigned_to_nat(1u);
v___x_1313_ = lean_nat_add(v_size_1310_, v___x_1312_);
v___x_1314_ = lean_array_get_size(v_keyArray_1311_);
v___x_1315_ = lean_nat_dec_lt(v___x_1313_, v___x_1314_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1316_; 
lean_dec(v___x_1313_);
v___x_1316_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_1222_);
lean_dec(v_snd_1222_);
v___y_1252_ = v___x_1288_;
v___y_1253_ = v___x_1292_;
v___y_1254_ = v___x_1289_;
v___y_1255_ = v___x_1316_;
goto v___jp_1251_;
}
else
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; 
v___x_1317_ = lean_unsigned_to_nat(4u);
v___x_1318_ = lean_nat_mul(v___x_1313_, v___x_1317_);
lean_dec(v___x_1313_);
v___x_1319_ = lean_unsigned_to_nat(3u);
v___x_1320_ = lean_nat_mul(v___x_1314_, v___x_1319_);
v___x_1321_ = lean_nat_dec_le(v___x_1318_, v___x_1320_);
lean_dec(v___x_1320_);
lean_dec(v___x_1318_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1322_; 
v___x_1322_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_1222_);
lean_dec(v_snd_1222_);
v___y_1252_ = v___x_1288_;
v___y_1253_ = v___x_1292_;
v___y_1254_ = v___x_1289_;
v___y_1255_ = v___x_1322_;
goto v___jp_1251_;
}
else
{
v___y_1252_ = v___x_1288_;
v___y_1253_ = v___x_1292_;
v___y_1254_ = v___x_1289_;
v___y_1255_ = v_snd_1222_;
goto v___jp_1251_;
}
}
}
}
}
}
v___jp_1325_:
{
lean_object* v___x_1327_; 
v___x_1327_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1324_, v___x_1213_);
lean_dec(v_ref_1324_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_inc(v___y_1326_);
v___y_1285_ = v___y_1326_;
v___y_1286_ = v___y_1326_;
goto v___jp_1284_;
}
else
{
lean_object* v_val_1328_; 
v_val_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_val_1328_);
lean_dec_ref_known(v___x_1327_, 1);
v___y_1285_ = v___y_1326_;
v___y_1286_ = v_val_1328_;
goto v___jp_1284_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25_spec__39_spec__46___redArg___boxed(lean_object* v___x_1335_, lean_object* v_as_1336_, lean_object* v_sz_1337_, lean_object* v_i_1338_, lean_object* v_b_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
uint8_t v___x_38562__boxed_1342_; size_t v_sz_boxed_1343_; size_t v_i_boxed_1344_; lean_object* v_res_1345_; 
v___x_38562__boxed_1342_ = lean_unbox(v___x_1335_);
v_sz_boxed_1343_ = lean_unbox_usize(v_sz_1337_);
lean_dec(v_sz_1337_);
v_i_boxed_1344_ = lean_unbox_usize(v_i_1338_);
lean_dec(v_i_1338_);
v_res_1345_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25_spec__39_spec__46___redArg(v___x_38562__boxed_1342_, v_as_1336_, v_sz_boxed_1343_, v_i_boxed_1344_, v_b_1339_, v___y_1340_);
lean_dec_ref(v___y_1340_);
lean_dec_ref(v_as_1336_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25_spec__39(uint8_t v___x_1346_, lean_object* v_as_1347_, size_t v_sz_1348_, size_t v_i_1349_, lean_object* v_b_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
uint8_t v___x_1354_; 
v___x_1354_ = lean_usize_dec_lt(v_i_1349_, v_sz_1348_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; 
v___x_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1355_, 0, v_b_1350_);
return v___x_1355_;
}
else
{
lean_object* v_snd_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1467_; 
v_snd_1356_ = lean_ctor_get(v_b_1350_, 1);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_b_1350_);
if (v_isSharedCheck_1467_ == 0)
{
lean_object* v_unused_1468_; 
v_unused_1468_ = lean_ctor_get(v_b_1350_, 0);
lean_dec(v_unused_1468_);
v___x_1358_ = v_b_1350_;
v_isShared_1359_ = v_isSharedCheck_1467_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_snd_1356_);
lean_dec(v_b_1350_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1467_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v_ref_1360_; lean_object* v_a_1361_; lean_object* v_ref_1362_; lean_object* v_msg_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1466_; 
v_ref_1360_ = lean_ctor_get(v___y_1351_, 5);
v_a_1361_ = lean_array_uget(v_as_1347_, v_i_1349_);
v_ref_1362_ = lean_ctor_get(v_a_1361_, 0);
v_msg_1363_ = lean_ctor_get(v_a_1361_, 1);
v_isSharedCheck_1466_ = !lean_is_exclusive(v_a_1361_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1365_ = v_a_1361_;
v_isShared_1366_ = v_isSharedCheck_1466_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_msg_1363_);
lean_inc(v_ref_1362_);
lean_dec(v_a_1361_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1466_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1367_; lean_object* v___y_1369_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v_i_1380_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v_i_1401_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v_ref_1458_; lean_object* v___y_1460_; lean_object* v___x_1463_; 
v___x_1367_ = lean_box(0);
v_ref_1458_ = l_Lean_replaceRef(v_ref_1362_, v_ref_1360_);
lean_dec(v_ref_1362_);
v___x_1463_ = l_Lean_Syntax_getPos_x3f(v_ref_1458_, v___x_1346_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v___x_1464_; 
v___x_1464_ = lean_unsigned_to_nat(0u);
v___y_1460_ = v___x_1464_;
goto v___jp_1459_;
}
else
{
lean_object* v_val_1465_; 
v_val_1465_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_val_1465_);
lean_dec_ref_known(v___x_1463_, 1);
v___y_1460_ = v_val_1465_;
goto v___jp_1459_;
}
v___jp_1368_:
{
lean_object* v___x_1371_; 
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 1, v___y_1369_);
lean_ctor_set(v___x_1358_, 0, v___x_1367_);
v___x_1371_ = v___x_1358_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1367_);
lean_ctor_set(v_reuseFailAlloc_1375_, 1, v___y_1369_);
v___x_1371_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
size_t v___x_1372_; size_t v___x_1373_; lean_object* v___x_1374_; 
v___x_1372_ = ((size_t)1ULL);
v___x_1373_ = lean_usize_add(v_i_1349_, v___x_1372_);
v___x_1374_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25_spec__39_spec__46___redArg(v___x_1346_, v_as_1347_, v_sz_1348_, v___x_1373_, v___x_1371_, v___y_1351_);
return v___x_1374_;
}
}
v___jp_1376_:
{
lean_object* v_size_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v_size_1381_ = lean_ctor_get(v___y_1377_, 0);
v___x_1382_ = lean_unsigned_to_nat(1u);
v___x_1383_ = lean_nat_add(v_size_1381_, v___x_1382_);
v___x_1384_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1377_, v___x_1383_, v_i_1380_, v___y_1378_, v___y_1379_);
lean_dec(v_i_1380_);
v___y_1369_ = v___x_1384_;
goto v___jp_1368_;
}
v___jp_1385_:
{
lean_object* v___x_1390_; 
v___x_1390_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v___y_1389_, v___y_1387_);
switch(lean_obj_tag(v___x_1390_))
{
case 0:
{
lean_object* v_index_1391_; lean_object* v_size_1392_; lean_object* v___x_1393_; 
lean_dec(v___y_1386_);
v_index_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_index_1391_);
lean_dec_ref_known(v___x_1390_, 3);
v_size_1392_ = lean_ctor_get(v___y_1389_, 0);
lean_inc(v_size_1392_);
v___x_1393_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1389_, v_size_1392_, v_index_1391_, v___y_1387_, v___y_1388_);
lean_dec(v_index_1391_);
v___y_1369_ = v___x_1393_;
goto v___jp_1368_;
}
case 1:
{
lean_object* v_index_1394_; 
lean_dec(v___y_1386_);
v_index_1394_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_index_1394_);
lean_dec_ref_known(v___x_1390_, 1);
v___y_1377_ = v___y_1389_;
v___y_1378_ = v___y_1387_;
v___y_1379_ = v___y_1388_;
v_i_1380_ = v_index_1394_;
goto v___jp_1376_;
}
default: 
{
lean_object* v___x_1395_; 
v___x_1395_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1389_, v___y_1386_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_index_1396_; 
v_index_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_index_1396_);
lean_dec_ref_known(v___x_1395_, 1);
v___y_1377_ = v___y_1389_;
v___y_1378_ = v___y_1387_;
v___y_1379_ = v___y_1388_;
v_i_1380_ = v_index_1396_;
goto v___jp_1376_;
}
else
{
lean_dec_ref(v___y_1388_);
lean_dec_ref(v___y_1387_);
v___y_1369_ = v___y_1389_;
goto v___jp_1368_;
}
}
}
}
v___jp_1397_:
{
lean_object* v_size_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v_size_1402_ = lean_ctor_get(v___y_1398_, 0);
v___x_1403_ = lean_unsigned_to_nat(1u);
v___x_1404_ = lean_nat_add(v_size_1402_, v___x_1403_);
v___x_1405_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1398_, v___x_1404_, v_i_1401_, v___y_1399_, v___y_1400_);
lean_dec(v_i_1401_);
v___y_1369_ = v___x_1405_;
goto v___jp_1368_;
}
v___jp_1406_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1410_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_1356_);
lean_dec(v_snd_1356_);
v___x_1411_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v___x_1410_, v___y_1408_);
switch(lean_obj_tag(v___x_1411_))
{
case 0:
{
lean_object* v_index_1412_; lean_object* v_size_1413_; lean_object* v___x_1414_; 
lean_dec(v___y_1407_);
v_index_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_index_1412_);
lean_dec_ref_known(v___x_1411_, 3);
v_size_1413_ = lean_ctor_get(v___x_1410_, 0);
lean_inc(v_size_1413_);
v___x_1414_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1410_, v_size_1413_, v_index_1412_, v___y_1408_, v___y_1409_);
lean_dec(v_index_1412_);
v___y_1369_ = v___x_1414_;
goto v___jp_1368_;
}
case 1:
{
lean_object* v_index_1415_; 
lean_dec(v___y_1407_);
v_index_1415_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_index_1415_);
lean_dec_ref_known(v___x_1411_, 1);
v___y_1398_ = v___x_1410_;
v___y_1399_ = v___y_1408_;
v___y_1400_ = v___y_1409_;
v_i_1401_ = v_index_1415_;
goto v___jp_1397_;
}
default: 
{
lean_object* v___x_1416_; 
v___x_1416_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1410_, v___y_1407_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_index_1417_; 
v_index_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_index_1417_);
lean_dec_ref_known(v___x_1416_, 1);
v___y_1398_ = v___x_1410_;
v___y_1399_ = v___y_1408_;
v___y_1400_ = v___y_1409_;
v_i_1401_ = v_index_1417_;
goto v___jp_1397_;
}
else
{
lean_dec_ref(v___y_1409_);
lean_dec_ref(v___y_1408_);
v___y_1369_ = v___x_1410_;
goto v___jp_1368_;
}
}
}
}
v___jp_1418_:
{
lean_object* v___x_1422_; 
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 1, v___y_1420_);
lean_ctor_set(v___x_1365_, 0, v___y_1419_);
v___x_1422_ = v___x_1365_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___y_1419_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v___y_1420_);
v___x_1422_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1423_ = lean_unsigned_to_nat(0u);
v___x_1424_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25_spec__39_spec__46___redArg___closed__0));
v___x_1425_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg(v_snd_1356_, v___x_1422_, v___x_1424_);
v___x_1426_ = lean_array_push(v___x_1425_, v_msg_1363_);
v___x_1427_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v_snd_1356_, v___x_1422_);
switch(lean_obj_tag(v___x_1427_))
{
case 0:
{
lean_object* v_index_1428_; lean_object* v_size_1429_; lean_object* v___x_1430_; 
v_index_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_index_1428_);
lean_dec_ref_known(v___x_1427_, 3);
v_size_1429_ = lean_ctor_get(v_snd_1356_, 0);
lean_inc(v_size_1429_);
v___x_1430_ = l_Std_DHashMap_Raw_setEntry___redArg(v_snd_1356_, v_size_1429_, v_index_1428_, v___x_1422_, v___x_1426_);
lean_dec(v_index_1428_);
v___y_1369_ = v___x_1430_;
goto v___jp_1368_;
}
case 1:
{
lean_object* v_index_1431_; lean_object* v_size_1432_; lean_object* v_keyArray_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; uint8_t v___x_1437_; 
v_index_1431_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_index_1431_);
lean_dec_ref_known(v___x_1427_, 1);
v_size_1432_ = lean_ctor_get(v_snd_1356_, 0);
v_keyArray_1433_ = lean_ctor_get(v_snd_1356_, 1);
v___x_1434_ = lean_unsigned_to_nat(1u);
v___x_1435_ = lean_nat_add(v_size_1432_, v___x_1434_);
v___x_1436_ = lean_array_get_size(v_keyArray_1433_);
v___x_1437_ = lean_nat_dec_lt(v___x_1435_, v___x_1436_);
if (v___x_1437_ == 0)
{
lean_dec(v___x_1435_);
lean_dec(v_index_1431_);
v___y_1407_ = v___x_1423_;
v___y_1408_ = v___x_1422_;
v___y_1409_ = v___x_1426_;
goto v___jp_1406_;
}
else
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; 
v___x_1438_ = lean_unsigned_to_nat(4u);
v___x_1439_ = lean_nat_mul(v___x_1435_, v___x_1438_);
v___x_1440_ = lean_unsigned_to_nat(3u);
v___x_1441_ = lean_nat_mul(v___x_1436_, v___x_1440_);
v___x_1442_ = lean_nat_dec_le(v___x_1439_, v___x_1441_);
lean_dec(v___x_1441_);
lean_dec(v___x_1439_);
if (v___x_1442_ == 0)
{
lean_dec(v___x_1435_);
lean_dec(v_index_1431_);
v___y_1407_ = v___x_1423_;
v___y_1408_ = v___x_1422_;
v___y_1409_ = v___x_1426_;
goto v___jp_1406_;
}
else
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Std_DHashMap_Raw_setEntry___redArg(v_snd_1356_, v___x_1435_, v_index_1431_, v___x_1422_, v___x_1426_);
lean_dec(v_index_1431_);
v___y_1369_ = v___x_1443_;
goto v___jp_1368_;
}
}
}
default: 
{
lean_object* v_size_1444_; lean_object* v_keyArray_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; uint8_t v___x_1449_; 
v_size_1444_ = lean_ctor_get(v_snd_1356_, 0);
v_keyArray_1445_ = lean_ctor_get(v_snd_1356_, 1);
v___x_1446_ = lean_unsigned_to_nat(1u);
v___x_1447_ = lean_nat_add(v_size_1444_, v___x_1446_);
v___x_1448_ = lean_array_get_size(v_keyArray_1445_);
v___x_1449_ = lean_nat_dec_lt(v___x_1447_, v___x_1448_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; 
lean_dec(v___x_1447_);
v___x_1450_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_1356_);
lean_dec(v_snd_1356_);
v___y_1386_ = v___x_1423_;
v___y_1387_ = v___x_1422_;
v___y_1388_ = v___x_1426_;
v___y_1389_ = v___x_1450_;
goto v___jp_1385_;
}
else
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; uint8_t v___x_1455_; 
v___x_1451_ = lean_unsigned_to_nat(4u);
v___x_1452_ = lean_nat_mul(v___x_1447_, v___x_1451_);
lean_dec(v___x_1447_);
v___x_1453_ = lean_unsigned_to_nat(3u);
v___x_1454_ = lean_nat_mul(v___x_1448_, v___x_1453_);
v___x_1455_ = lean_nat_dec_le(v___x_1452_, v___x_1454_);
lean_dec(v___x_1454_);
lean_dec(v___x_1452_);
if (v___x_1455_ == 0)
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_1356_);
lean_dec(v_snd_1356_);
v___y_1386_ = v___x_1423_;
v___y_1387_ = v___x_1422_;
v___y_1388_ = v___x_1426_;
v___y_1389_ = v___x_1456_;
goto v___jp_1385_;
}
else
{
v___y_1386_ = v___x_1423_;
v___y_1387_ = v___x_1422_;
v___y_1388_ = v___x_1426_;
v___y_1389_ = v_snd_1356_;
goto v___jp_1385_;
}
}
}
}
}
}
v___jp_1459_:
{
lean_object* v___x_1461_; 
v___x_1461_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1458_, v___x_1346_);
lean_dec(v_ref_1458_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_inc(v___y_1460_);
v___y_1419_ = v___y_1460_;
v___y_1420_ = v___y_1460_;
goto v___jp_1418_;
}
else
{
lean_object* v_val_1462_; 
v_val_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_val_1462_);
lean_dec_ref_known(v___x_1461_, 1);
v___y_1419_ = v___y_1460_;
v___y_1420_ = v_val_1462_;
goto v___jp_1418_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25_spec__39___boxed(lean_object* v___x_1469_, lean_object* v_as_1470_, lean_object* v_sz_1471_, lean_object* v_i_1472_, lean_object* v_b_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
uint8_t v___x_38771__boxed_1477_; size_t v_sz_boxed_1478_; size_t v_i_boxed_1479_; lean_object* v_res_1480_; 
v___x_38771__boxed_1477_ = lean_unbox(v___x_1469_);
v_sz_boxed_1478_ = lean_unbox_usize(v_sz_1471_);
lean_dec(v_sz_1471_);
v_i_boxed_1479_ = lean_unbox_usize(v_i_1472_);
lean_dec(v_i_1472_);
v_res_1480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25_spec__39(v___x_38771__boxed_1477_, v_as_1470_, v_sz_boxed_1478_, v_i_boxed_1479_, v_b_1473_, v___y_1474_, v___y_1475_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec_ref(v_as_1470_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25(lean_object* v_init_1481_, uint8_t v___x_1482_, lean_object* v_n_1483_, lean_object* v_b_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
if (lean_obj_tag(v_n_1483_) == 0)
{
lean_object* v_cs_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; size_t v_sz_1491_; size_t v___x_1492_; lean_object* v___x_1493_; 
v_cs_1488_ = lean_ctor_get(v_n_1483_, 0);
v___x_1489_ = lean_box(0);
v___x_1490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1489_);
lean_ctor_set(v___x_1490_, 1, v_b_1484_);
v_sz_1491_ = lean_array_size(v_cs_1488_);
v___x_1492_ = ((size_t)0ULL);
v___x_1493_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25_spec__38(v_init_1481_, v___x_1482_, v_cs_1488_, v_sz_1491_, v___x_1492_, v___x_1490_, v___y_1485_, v___y_1486_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1508_; 
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1496_ = v___x_1493_;
v_isShared_1497_ = v_isSharedCheck_1508_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1493_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1508_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v_fst_1498_; 
v_fst_1498_ = lean_ctor_get(v_a_1494_, 0);
if (lean_obj_tag(v_fst_1498_) == 0)
{
lean_object* v_snd_1499_; lean_object* v___x_1500_; lean_object* v___x_1502_; 
v_snd_1499_ = lean_ctor_get(v_a_1494_, 1);
lean_inc(v_snd_1499_);
lean_dec(v_a_1494_);
v___x_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1500_, 0, v_snd_1499_);
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 0, v___x_1500_);
v___x_1502_ = v___x_1496_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1500_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
else
{
lean_object* v_val_1504_; lean_object* v___x_1506_; 
lean_inc_ref(v_fst_1498_);
lean_dec(v_a_1494_);
v_val_1504_ = lean_ctor_get(v_fst_1498_, 0);
lean_inc(v_val_1504_);
lean_dec_ref_known(v_fst_1498_, 1);
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 0, v_val_1504_);
v___x_1506_ = v___x_1496_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_val_1504_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
else
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1516_; 
v_a_1509_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1511_ = v___x_1493_;
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1493_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1509_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
}
else
{
lean_object* v_vs_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; size_t v_sz_1520_; size_t v___x_1521_; lean_object* v___x_1522_; 
v_vs_1517_ = lean_ctor_get(v_n_1483_, 0);
v___x_1518_ = lean_box(0);
v___x_1519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1518_);
lean_ctor_set(v___x_1519_, 1, v_b_1484_);
v_sz_1520_ = lean_array_size(v_vs_1517_);
v___x_1521_ = ((size_t)0ULL);
v___x_1522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25_spec__39(v___x_1482_, v_vs_1517_, v_sz_1520_, v___x_1521_, v___x_1519_, v___y_1485_, v___y_1486_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1537_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1525_ = v___x_1522_;
v_isShared_1526_ = v_isSharedCheck_1537_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1522_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1537_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v_fst_1527_; 
v_fst_1527_ = lean_ctor_get(v_a_1523_, 0);
if (lean_obj_tag(v_fst_1527_) == 0)
{
lean_object* v_snd_1528_; lean_object* v___x_1529_; lean_object* v___x_1531_; 
v_snd_1528_ = lean_ctor_get(v_a_1523_, 1);
lean_inc(v_snd_1528_);
lean_dec(v_a_1523_);
v___x_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1529_, 0, v_snd_1528_);
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 0, v___x_1529_);
v___x_1531_ = v___x_1525_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1529_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
else
{
lean_object* v_val_1533_; lean_object* v___x_1535_; 
lean_inc_ref(v_fst_1527_);
lean_dec(v_a_1523_);
v_val_1533_ = lean_ctor_get(v_fst_1527_, 0);
lean_inc(v_val_1533_);
lean_dec_ref_known(v_fst_1527_, 1);
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 0, v_val_1533_);
v___x_1535_ = v___x_1525_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_val_1533_);
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
else
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
v_a_1538_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1540_ = v___x_1522_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1522_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1538_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25_spec__38(lean_object* v_init_1546_, uint8_t v___x_1547_, lean_object* v_as_1548_, size_t v_sz_1549_, size_t v_i_1550_, lean_object* v_b_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
uint8_t v___x_1555_; 
v___x_1555_ = lean_usize_dec_lt(v_i_1550_, v_sz_1549_);
if (v___x_1555_ == 0)
{
lean_object* v___x_1556_; 
v___x_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1556_, 0, v_b_1551_);
return v___x_1556_;
}
else
{
lean_object* v_snd_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1591_; 
v_snd_1557_ = lean_ctor_get(v_b_1551_, 1);
v_isSharedCheck_1591_ = !lean_is_exclusive(v_b_1551_);
if (v_isSharedCheck_1591_ == 0)
{
lean_object* v_unused_1592_; 
v_unused_1592_ = lean_ctor_get(v_b_1551_, 0);
lean_dec(v_unused_1592_);
v___x_1559_ = v_b_1551_;
v_isShared_1560_ = v_isSharedCheck_1591_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_snd_1557_);
lean_dec(v_b_1551_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1591_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v_a_1561_; lean_object* v___x_1562_; 
v_a_1561_ = lean_array_uget_borrowed(v_as_1548_, v_i_1550_);
lean_inc(v_snd_1557_);
v___x_1562_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25(v_init_1546_, v___x_1547_, v_a_1561_, v_snd_1557_, v___y_1552_, v___y_1553_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1582_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1565_ = v___x_1562_;
v_isShared_1566_ = v_isSharedCheck_1582_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1562_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1582_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
if (lean_obj_tag(v_a_1563_) == 0)
{
lean_object* v___x_1567_; lean_object* v___x_1569_; 
v___x_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1567_, 0, v_a_1563_);
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 0, v___x_1567_);
v___x_1569_ = v___x_1559_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1567_);
lean_ctor_set(v_reuseFailAlloc_1573_, 1, v_snd_1557_);
v___x_1569_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
lean_object* v___x_1571_; 
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 0, v___x_1569_);
v___x_1571_ = v___x_1565_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1569_);
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
lean_object* v_a_1574_; lean_object* v___x_1575_; lean_object* v___x_1577_; 
lean_del_object(v___x_1565_);
lean_dec(v_snd_1557_);
v_a_1574_ = lean_ctor_get(v_a_1563_, 0);
lean_inc(v_a_1574_);
lean_dec_ref_known(v_a_1563_, 1);
v___x_1575_ = lean_box(0);
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 1, v_a_1574_);
lean_ctor_set(v___x_1559_, 0, v___x_1575_);
v___x_1577_ = v___x_1559_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1575_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v_a_1574_);
v___x_1577_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
size_t v___x_1578_; size_t v___x_1579_; 
v___x_1578_ = ((size_t)1ULL);
v___x_1579_ = lean_usize_add(v_i_1550_, v___x_1578_);
v_i_1550_ = v___x_1579_;
v_b_1551_ = v___x_1577_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
lean_del_object(v___x_1559_);
lean_dec(v_snd_1557_);
v_a_1583_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1585_ = v___x_1562_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1562_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1583_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25_spec__38___boxed(lean_object* v_init_1593_, lean_object* v___x_1594_, lean_object* v_as_1595_, lean_object* v_sz_1596_, lean_object* v_i_1597_, lean_object* v_b_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
uint8_t v___x_38979__boxed_1602_; size_t v_sz_boxed_1603_; size_t v_i_boxed_1604_; lean_object* v_res_1605_; 
v___x_38979__boxed_1602_ = lean_unbox(v___x_1594_);
v_sz_boxed_1603_ = lean_unbox_usize(v_sz_1596_);
lean_dec(v_sz_1596_);
v_i_boxed_1604_ = lean_unbox_usize(v_i_1597_);
lean_dec(v_i_1597_);
v_res_1605_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25_spec__38(v_init_1593_, v___x_38979__boxed_1602_, v_as_1595_, v_sz_boxed_1603_, v_i_boxed_1604_, v_b_1598_, v___y_1599_, v___y_1600_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec_ref(v_as_1595_);
lean_dec_ref(v_init_1593_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25___boxed(lean_object* v_init_1606_, lean_object* v___x_1607_, lean_object* v_n_1608_, lean_object* v_b_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
uint8_t v___x_38999__boxed_1613_; lean_object* v_res_1614_; 
v___x_38999__boxed_1613_ = lean_unbox(v___x_1607_);
v_res_1614_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25(v_init_1606_, v___x_38999__boxed_1613_, v_n_1608_, v_b_1609_, v___y_1610_, v___y_1611_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec_ref(v_n_1608_);
lean_dec_ref(v_init_1606_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__41___redArg(uint8_t v___x_1615_, lean_object* v_as_1616_, size_t v_sz_1617_, size_t v_i_1618_, lean_object* v_b_1619_, lean_object* v___y_1620_){
_start:
{
uint8_t v___x_1622_; 
v___x_1622_ = lean_usize_dec_lt(v_i_1618_, v_sz_1617_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1623_; 
v___x_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1623_, 0, v_b_1619_);
return v___x_1623_;
}
else
{
lean_object* v_snd_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1735_; 
v_snd_1624_ = lean_ctor_get(v_b_1619_, 1);
v_isSharedCheck_1735_ = !lean_is_exclusive(v_b_1619_);
if (v_isSharedCheck_1735_ == 0)
{
lean_object* v_unused_1736_; 
v_unused_1736_ = lean_ctor_get(v_b_1619_, 0);
lean_dec(v_unused_1736_);
v___x_1626_ = v_b_1619_;
v_isShared_1627_ = v_isSharedCheck_1735_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_snd_1624_);
lean_dec(v_b_1619_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1735_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v_ref_1628_; lean_object* v_a_1629_; lean_object* v_ref_1630_; lean_object* v_msg_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1734_; 
v_ref_1628_ = lean_ctor_get(v___y_1620_, 5);
v_a_1629_ = lean_array_uget(v_as_1616_, v_i_1618_);
v_ref_1630_ = lean_ctor_get(v_a_1629_, 0);
v_msg_1631_ = lean_ctor_get(v_a_1629_, 1);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_a_1629_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1633_ = v_a_1629_;
v_isShared_1634_ = v_isSharedCheck_1734_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_msg_1631_);
lean_inc(v_ref_1630_);
lean_dec(v_a_1629_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1734_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1635_; lean_object* v___y_1637_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v_i_1648_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v_i_1669_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v_ref_1726_; lean_object* v___y_1728_; lean_object* v___x_1731_; 
v___x_1635_ = lean_box(0);
v_ref_1726_ = l_Lean_replaceRef(v_ref_1630_, v_ref_1628_);
lean_dec(v_ref_1630_);
v___x_1731_ = l_Lean_Syntax_getPos_x3f(v_ref_1726_, v___x_1615_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_object* v___x_1732_; 
v___x_1732_ = lean_unsigned_to_nat(0u);
v___y_1728_ = v___x_1732_;
goto v___jp_1727_;
}
else
{
lean_object* v_val_1733_; 
v_val_1733_ = lean_ctor_get(v___x_1731_, 0);
lean_inc(v_val_1733_);
lean_dec_ref_known(v___x_1731_, 1);
v___y_1728_ = v_val_1733_;
goto v___jp_1727_;
}
v___jp_1636_:
{
lean_object* v___x_1639_; 
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 1, v___y_1637_);
lean_ctor_set(v___x_1626_, 0, v___x_1635_);
v___x_1639_ = v___x_1626_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1635_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v___y_1637_);
v___x_1639_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
size_t v___x_1640_; size_t v___x_1641_; 
v___x_1640_ = ((size_t)1ULL);
v___x_1641_ = lean_usize_add(v_i_1618_, v___x_1640_);
v_i_1618_ = v___x_1641_;
v_b_1619_ = v___x_1639_;
goto _start;
}
}
v___jp_1644_:
{
lean_object* v_size_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v_size_1649_ = lean_ctor_get(v___y_1646_, 0);
v___x_1650_ = lean_unsigned_to_nat(1u);
v___x_1651_ = lean_nat_add(v_size_1649_, v___x_1650_);
v___x_1652_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1646_, v___x_1651_, v_i_1648_, v___y_1647_, v___y_1645_);
lean_dec(v_i_1648_);
v___y_1637_ = v___x_1652_;
goto v___jp_1636_;
}
v___jp_1653_:
{
lean_object* v___x_1658_; 
v___x_1658_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v___y_1657_, v___y_1655_);
switch(lean_obj_tag(v___x_1658_))
{
case 0:
{
lean_object* v_index_1659_; lean_object* v_size_1660_; lean_object* v___x_1661_; 
lean_dec(v___y_1656_);
v_index_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_index_1659_);
lean_dec_ref_known(v___x_1658_, 3);
v_size_1660_ = lean_ctor_get(v___y_1657_, 0);
lean_inc(v_size_1660_);
v___x_1661_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1657_, v_size_1660_, v_index_1659_, v___y_1655_, v___y_1654_);
lean_dec(v_index_1659_);
v___y_1637_ = v___x_1661_;
goto v___jp_1636_;
}
case 1:
{
lean_object* v_index_1662_; 
lean_dec(v___y_1656_);
v_index_1662_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_index_1662_);
lean_dec_ref_known(v___x_1658_, 1);
v___y_1645_ = v___y_1654_;
v___y_1646_ = v___y_1657_;
v___y_1647_ = v___y_1655_;
v_i_1648_ = v_index_1662_;
goto v___jp_1644_;
}
default: 
{
lean_object* v___x_1663_; 
v___x_1663_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1657_, v___y_1656_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_index_1664_; 
v_index_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_index_1664_);
lean_dec_ref_known(v___x_1663_, 1);
v___y_1645_ = v___y_1654_;
v___y_1646_ = v___y_1657_;
v___y_1647_ = v___y_1655_;
v_i_1648_ = v_index_1664_;
goto v___jp_1644_;
}
else
{
lean_dec_ref(v___y_1655_);
lean_dec_ref(v___y_1654_);
v___y_1637_ = v___y_1657_;
goto v___jp_1636_;
}
}
}
}
v___jp_1665_:
{
lean_object* v_size_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v_size_1670_ = lean_ctor_get(v___y_1666_, 0);
v___x_1671_ = lean_unsigned_to_nat(1u);
v___x_1672_ = lean_nat_add(v_size_1670_, v___x_1671_);
v___x_1673_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1666_, v___x_1672_, v_i_1669_, v___y_1668_, v___y_1667_);
lean_dec(v_i_1669_);
v___y_1637_ = v___x_1673_;
goto v___jp_1636_;
}
v___jp_1674_:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_1624_);
lean_dec(v_snd_1624_);
v___x_1679_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v___x_1678_, v___y_1676_);
switch(lean_obj_tag(v___x_1679_))
{
case 0:
{
lean_object* v_index_1680_; lean_object* v_size_1681_; lean_object* v___x_1682_; 
lean_dec(v___y_1677_);
v_index_1680_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_index_1680_);
lean_dec_ref_known(v___x_1679_, 3);
v_size_1681_ = lean_ctor_get(v___x_1678_, 0);
lean_inc(v_size_1681_);
v___x_1682_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1678_, v_size_1681_, v_index_1680_, v___y_1676_, v___y_1675_);
lean_dec(v_index_1680_);
v___y_1637_ = v___x_1682_;
goto v___jp_1636_;
}
case 1:
{
lean_object* v_index_1683_; 
lean_dec(v___y_1677_);
v_index_1683_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_index_1683_);
lean_dec_ref_known(v___x_1679_, 1);
v___y_1666_ = v___x_1678_;
v___y_1667_ = v___y_1675_;
v___y_1668_ = v___y_1676_;
v_i_1669_ = v_index_1683_;
goto v___jp_1665_;
}
default: 
{
lean_object* v___x_1684_; 
v___x_1684_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1678_, v___y_1677_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v_index_1685_; 
v_index_1685_ = lean_ctor_get(v___x_1684_, 0);
lean_inc(v_index_1685_);
lean_dec_ref_known(v___x_1684_, 1);
v___y_1666_ = v___x_1678_;
v___y_1667_ = v___y_1675_;
v___y_1668_ = v___y_1676_;
v_i_1669_ = v_index_1685_;
goto v___jp_1665_;
}
else
{
lean_dec_ref(v___y_1676_);
lean_dec_ref(v___y_1675_);
v___y_1637_ = v___x_1678_;
goto v___jp_1636_;
}
}
}
}
v___jp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 1, v___y_1688_);
lean_ctor_set(v___x_1633_, 0, v___y_1687_);
v___x_1690_ = v___x_1633_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___y_1687_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v___y_1688_);
v___x_1690_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1691_ = lean_unsigned_to_nat(0u);
v___x_1692_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25_spec__39_spec__46___redArg___closed__0));
v___x_1693_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg(v_snd_1624_, v___x_1690_, v___x_1692_);
v___x_1694_ = lean_array_push(v___x_1693_, v_msg_1631_);
v___x_1695_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v_snd_1624_, v___x_1690_);
switch(lean_obj_tag(v___x_1695_))
{
case 0:
{
lean_object* v_index_1696_; lean_object* v_size_1697_; lean_object* v___x_1698_; 
v_index_1696_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_index_1696_);
lean_dec_ref_known(v___x_1695_, 3);
v_size_1697_ = lean_ctor_get(v_snd_1624_, 0);
lean_inc(v_size_1697_);
v___x_1698_ = l_Std_DHashMap_Raw_setEntry___redArg(v_snd_1624_, v_size_1697_, v_index_1696_, v___x_1690_, v___x_1694_);
lean_dec(v_index_1696_);
v___y_1637_ = v___x_1698_;
goto v___jp_1636_;
}
case 1:
{
lean_object* v_index_1699_; lean_object* v_size_1700_; lean_object* v_keyArray_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; uint8_t v___x_1705_; 
v_index_1699_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_index_1699_);
lean_dec_ref_known(v___x_1695_, 1);
v_size_1700_ = lean_ctor_get(v_snd_1624_, 0);
v_keyArray_1701_ = lean_ctor_get(v_snd_1624_, 1);
v___x_1702_ = lean_unsigned_to_nat(1u);
v___x_1703_ = lean_nat_add(v_size_1700_, v___x_1702_);
v___x_1704_ = lean_array_get_size(v_keyArray_1701_);
v___x_1705_ = lean_nat_dec_lt(v___x_1703_, v___x_1704_);
if (v___x_1705_ == 0)
{
lean_dec(v___x_1703_);
lean_dec(v_index_1699_);
v___y_1675_ = v___x_1694_;
v___y_1676_ = v___x_1690_;
v___y_1677_ = v___x_1691_;
goto v___jp_1674_;
}
else
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; uint8_t v___x_1710_; 
v___x_1706_ = lean_unsigned_to_nat(4u);
v___x_1707_ = lean_nat_mul(v___x_1703_, v___x_1706_);
v___x_1708_ = lean_unsigned_to_nat(3u);
v___x_1709_ = lean_nat_mul(v___x_1704_, v___x_1708_);
v___x_1710_ = lean_nat_dec_le(v___x_1707_, v___x_1709_);
lean_dec(v___x_1709_);
lean_dec(v___x_1707_);
if (v___x_1710_ == 0)
{
lean_dec(v___x_1703_);
lean_dec(v_index_1699_);
v___y_1675_ = v___x_1694_;
v___y_1676_ = v___x_1690_;
v___y_1677_ = v___x_1691_;
goto v___jp_1674_;
}
else
{
lean_object* v___x_1711_; 
v___x_1711_ = l_Std_DHashMap_Raw_setEntry___redArg(v_snd_1624_, v___x_1703_, v_index_1699_, v___x_1690_, v___x_1694_);
lean_dec(v_index_1699_);
v___y_1637_ = v___x_1711_;
goto v___jp_1636_;
}
}
}
default: 
{
lean_object* v_size_1712_; lean_object* v_keyArray_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; uint8_t v___x_1717_; 
v_size_1712_ = lean_ctor_get(v_snd_1624_, 0);
v_keyArray_1713_ = lean_ctor_get(v_snd_1624_, 1);
v___x_1714_ = lean_unsigned_to_nat(1u);
v___x_1715_ = lean_nat_add(v_size_1712_, v___x_1714_);
v___x_1716_ = lean_array_get_size(v_keyArray_1713_);
v___x_1717_ = lean_nat_dec_lt(v___x_1715_, v___x_1716_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; 
lean_dec(v___x_1715_);
v___x_1718_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_1624_);
lean_dec(v_snd_1624_);
v___y_1654_ = v___x_1694_;
v___y_1655_ = v___x_1690_;
v___y_1656_ = v___x_1691_;
v___y_1657_ = v___x_1718_;
goto v___jp_1653_;
}
else
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; uint8_t v___x_1723_; 
v___x_1719_ = lean_unsigned_to_nat(4u);
v___x_1720_ = lean_nat_mul(v___x_1715_, v___x_1719_);
lean_dec(v___x_1715_);
v___x_1721_ = lean_unsigned_to_nat(3u);
v___x_1722_ = lean_nat_mul(v___x_1716_, v___x_1721_);
v___x_1723_ = lean_nat_dec_le(v___x_1720_, v___x_1722_);
lean_dec(v___x_1722_);
lean_dec(v___x_1720_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; 
v___x_1724_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_1624_);
lean_dec(v_snd_1624_);
v___y_1654_ = v___x_1694_;
v___y_1655_ = v___x_1690_;
v___y_1656_ = v___x_1691_;
v___y_1657_ = v___x_1724_;
goto v___jp_1653_;
}
else
{
v___y_1654_ = v___x_1694_;
v___y_1655_ = v___x_1690_;
v___y_1656_ = v___x_1691_;
v___y_1657_ = v_snd_1624_;
goto v___jp_1653_;
}
}
}
}
}
}
v___jp_1727_:
{
lean_object* v___x_1729_; 
v___x_1729_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1726_, v___x_1615_);
lean_dec(v_ref_1726_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_inc(v___y_1728_);
v___y_1687_ = v___y_1728_;
v___y_1688_ = v___y_1728_;
goto v___jp_1686_;
}
else
{
lean_object* v_val_1730_; 
v_val_1730_ = lean_ctor_get(v___x_1729_, 0);
lean_inc(v_val_1730_);
lean_dec_ref_known(v___x_1729_, 1);
v___y_1687_ = v___y_1728_;
v___y_1688_ = v_val_1730_;
goto v___jp_1686_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__41___redArg___boxed(lean_object* v___x_1737_, lean_object* v_as_1738_, lean_object* v_sz_1739_, lean_object* v_i_1740_, lean_object* v_b_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
uint8_t v___x_39182__boxed_1744_; size_t v_sz_boxed_1745_; size_t v_i_boxed_1746_; lean_object* v_res_1747_; 
v___x_39182__boxed_1744_ = lean_unbox(v___x_1737_);
v_sz_boxed_1745_ = lean_unbox_usize(v_sz_1739_);
lean_dec(v_sz_1739_);
v_i_boxed_1746_ = lean_unbox_usize(v_i_1740_);
lean_dec(v_i_1740_);
v_res_1747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__41___redArg(v___x_39182__boxed_1744_, v_as_1738_, v_sz_boxed_1745_, v_i_boxed_1746_, v_b_1741_, v___y_1742_);
lean_dec_ref(v___y_1742_);
lean_dec_ref(v_as_1738_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26(uint8_t v___x_1748_, lean_object* v_as_1749_, size_t v_sz_1750_, size_t v_i_1751_, lean_object* v_b_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
uint8_t v___x_1756_; 
v___x_1756_ = lean_usize_dec_lt(v_i_1751_, v_sz_1750_);
if (v___x_1756_ == 0)
{
lean_object* v___x_1757_; 
v___x_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1757_, 0, v_b_1752_);
return v___x_1757_;
}
else
{
lean_object* v_snd_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1869_; 
v_snd_1758_ = lean_ctor_get(v_b_1752_, 1);
v_isSharedCheck_1869_ = !lean_is_exclusive(v_b_1752_);
if (v_isSharedCheck_1869_ == 0)
{
lean_object* v_unused_1870_; 
v_unused_1870_ = lean_ctor_get(v_b_1752_, 0);
lean_dec(v_unused_1870_);
v___x_1760_ = v_b_1752_;
v_isShared_1761_ = v_isSharedCheck_1869_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_snd_1758_);
lean_dec(v_b_1752_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1869_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v_ref_1762_; lean_object* v_a_1763_; lean_object* v_ref_1764_; lean_object* v_msg_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1868_; 
v_ref_1762_ = lean_ctor_get(v___y_1753_, 5);
v_a_1763_ = lean_array_uget(v_as_1749_, v_i_1751_);
v_ref_1764_ = lean_ctor_get(v_a_1763_, 0);
v_msg_1765_ = lean_ctor_get(v_a_1763_, 1);
v_isSharedCheck_1868_ = !lean_is_exclusive(v_a_1763_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1767_ = v_a_1763_;
v_isShared_1768_ = v_isSharedCheck_1868_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_msg_1765_);
lean_inc(v_ref_1764_);
lean_dec(v_a_1763_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1868_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1769_; lean_object* v___y_1771_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v_i_1782_; lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v_i_1803_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v_ref_1860_; lean_object* v___y_1862_; lean_object* v___x_1865_; 
v___x_1769_ = lean_box(0);
v_ref_1860_ = l_Lean_replaceRef(v_ref_1764_, v_ref_1762_);
lean_dec(v_ref_1764_);
v___x_1865_ = l_Lean_Syntax_getPos_x3f(v_ref_1860_, v___x_1748_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v___x_1866_; 
v___x_1866_ = lean_unsigned_to_nat(0u);
v___y_1862_ = v___x_1866_;
goto v___jp_1861_;
}
else
{
lean_object* v_val_1867_; 
v_val_1867_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_val_1867_);
lean_dec_ref_known(v___x_1865_, 1);
v___y_1862_ = v_val_1867_;
goto v___jp_1861_;
}
v___jp_1770_:
{
lean_object* v___x_1773_; 
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 1, v___y_1771_);
lean_ctor_set(v___x_1760_, 0, v___x_1769_);
v___x_1773_ = v___x_1760_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v___x_1769_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v___y_1771_);
v___x_1773_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
size_t v___x_1774_; size_t v___x_1775_; lean_object* v___x_1776_; 
v___x_1774_ = ((size_t)1ULL);
v___x_1775_ = lean_usize_add(v_i_1751_, v___x_1774_);
v___x_1776_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__41___redArg(v___x_1748_, v_as_1749_, v_sz_1750_, v___x_1775_, v___x_1773_, v___y_1753_);
return v___x_1776_;
}
}
v___jp_1778_:
{
lean_object* v_size_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v_size_1783_ = lean_ctor_get(v___y_1779_, 0);
v___x_1784_ = lean_unsigned_to_nat(1u);
v___x_1785_ = lean_nat_add(v_size_1783_, v___x_1784_);
v___x_1786_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1779_, v___x_1785_, v_i_1782_, v___y_1781_, v___y_1780_);
lean_dec(v_i_1782_);
v___y_1771_ = v___x_1786_;
goto v___jp_1770_;
}
v___jp_1787_:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v___y_1791_, v___y_1790_);
switch(lean_obj_tag(v___x_1792_))
{
case 0:
{
lean_object* v_index_1793_; lean_object* v_size_1794_; lean_object* v___x_1795_; 
lean_dec(v___y_1788_);
v_index_1793_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_index_1793_);
lean_dec_ref_known(v___x_1792_, 3);
v_size_1794_ = lean_ctor_get(v___y_1791_, 0);
lean_inc(v_size_1794_);
v___x_1795_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1791_, v_size_1794_, v_index_1793_, v___y_1790_, v___y_1789_);
lean_dec(v_index_1793_);
v___y_1771_ = v___x_1795_;
goto v___jp_1770_;
}
case 1:
{
lean_object* v_index_1796_; 
lean_dec(v___y_1788_);
v_index_1796_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_index_1796_);
lean_dec_ref_known(v___x_1792_, 1);
v___y_1779_ = v___y_1791_;
v___y_1780_ = v___y_1789_;
v___y_1781_ = v___y_1790_;
v_i_1782_ = v_index_1796_;
goto v___jp_1778_;
}
default: 
{
lean_object* v___x_1797_; 
v___x_1797_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1791_, v___y_1788_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_index_1798_; 
v_index_1798_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_index_1798_);
lean_dec_ref_known(v___x_1797_, 1);
v___y_1779_ = v___y_1791_;
v___y_1780_ = v___y_1789_;
v___y_1781_ = v___y_1790_;
v_i_1782_ = v_index_1798_;
goto v___jp_1778_;
}
else
{
lean_dec_ref(v___y_1790_);
lean_dec_ref(v___y_1789_);
v___y_1771_ = v___y_1791_;
goto v___jp_1770_;
}
}
}
}
v___jp_1799_:
{
lean_object* v_size_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v_size_1804_ = lean_ctor_get(v___y_1800_, 0);
v___x_1805_ = lean_unsigned_to_nat(1u);
v___x_1806_ = lean_nat_add(v_size_1804_, v___x_1805_);
v___x_1807_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1800_, v___x_1806_, v_i_1803_, v___y_1802_, v___y_1801_);
lean_dec(v_i_1803_);
v___y_1771_ = v___x_1807_;
goto v___jp_1770_;
}
v___jp_1808_:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_1758_);
lean_dec(v_snd_1758_);
v___x_1813_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v___x_1812_, v___y_1811_);
switch(lean_obj_tag(v___x_1813_))
{
case 0:
{
lean_object* v_index_1814_; lean_object* v_size_1815_; lean_object* v___x_1816_; 
lean_dec(v___y_1809_);
v_index_1814_ = lean_ctor_get(v___x_1813_, 0);
lean_inc(v_index_1814_);
lean_dec_ref_known(v___x_1813_, 3);
v_size_1815_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_size_1815_);
v___x_1816_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1812_, v_size_1815_, v_index_1814_, v___y_1811_, v___y_1810_);
lean_dec(v_index_1814_);
v___y_1771_ = v___x_1816_;
goto v___jp_1770_;
}
case 1:
{
lean_object* v_index_1817_; 
lean_dec(v___y_1809_);
v_index_1817_ = lean_ctor_get(v___x_1813_, 0);
lean_inc(v_index_1817_);
lean_dec_ref_known(v___x_1813_, 1);
v___y_1800_ = v___x_1812_;
v___y_1801_ = v___y_1810_;
v___y_1802_ = v___y_1811_;
v_i_1803_ = v_index_1817_;
goto v___jp_1799_;
}
default: 
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1812_, v___y_1809_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_index_1819_; 
v_index_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_index_1819_);
lean_dec_ref_known(v___x_1818_, 1);
v___y_1800_ = v___x_1812_;
v___y_1801_ = v___y_1810_;
v___y_1802_ = v___y_1811_;
v_i_1803_ = v_index_1819_;
goto v___jp_1799_;
}
else
{
lean_dec_ref(v___y_1811_);
lean_dec_ref(v___y_1810_);
v___y_1771_ = v___x_1812_;
goto v___jp_1770_;
}
}
}
}
v___jp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 1, v___y_1822_);
lean_ctor_set(v___x_1767_, 0, v___y_1821_);
v___x_1824_ = v___x_1767_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___y_1821_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v___y_1822_);
v___x_1824_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1825_ = lean_unsigned_to_nat(0u);
v___x_1826_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25_spec__39_spec__46___redArg___closed__0));
v___x_1827_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg(v_snd_1758_, v___x_1824_, v___x_1826_);
v___x_1828_ = lean_array_push(v___x_1827_, v_msg_1765_);
v___x_1829_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v_snd_1758_, v___x_1824_);
switch(lean_obj_tag(v___x_1829_))
{
case 0:
{
lean_object* v_index_1830_; lean_object* v_size_1831_; lean_object* v___x_1832_; 
v_index_1830_ = lean_ctor_get(v___x_1829_, 0);
lean_inc(v_index_1830_);
lean_dec_ref_known(v___x_1829_, 3);
v_size_1831_ = lean_ctor_get(v_snd_1758_, 0);
lean_inc(v_size_1831_);
v___x_1832_ = l_Std_DHashMap_Raw_setEntry___redArg(v_snd_1758_, v_size_1831_, v_index_1830_, v___x_1824_, v___x_1828_);
lean_dec(v_index_1830_);
v___y_1771_ = v___x_1832_;
goto v___jp_1770_;
}
case 1:
{
lean_object* v_index_1833_; lean_object* v_size_1834_; lean_object* v_keyArray_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; uint8_t v___x_1839_; 
v_index_1833_ = lean_ctor_get(v___x_1829_, 0);
lean_inc(v_index_1833_);
lean_dec_ref_known(v___x_1829_, 1);
v_size_1834_ = lean_ctor_get(v_snd_1758_, 0);
v_keyArray_1835_ = lean_ctor_get(v_snd_1758_, 1);
v___x_1836_ = lean_unsigned_to_nat(1u);
v___x_1837_ = lean_nat_add(v_size_1834_, v___x_1836_);
v___x_1838_ = lean_array_get_size(v_keyArray_1835_);
v___x_1839_ = lean_nat_dec_lt(v___x_1837_, v___x_1838_);
if (v___x_1839_ == 0)
{
lean_dec(v___x_1837_);
lean_dec(v_index_1833_);
v___y_1809_ = v___x_1825_;
v___y_1810_ = v___x_1828_;
v___y_1811_ = v___x_1824_;
goto v___jp_1808_;
}
else
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; uint8_t v___x_1844_; 
v___x_1840_ = lean_unsigned_to_nat(4u);
v___x_1841_ = lean_nat_mul(v___x_1837_, v___x_1840_);
v___x_1842_ = lean_unsigned_to_nat(3u);
v___x_1843_ = lean_nat_mul(v___x_1838_, v___x_1842_);
v___x_1844_ = lean_nat_dec_le(v___x_1841_, v___x_1843_);
lean_dec(v___x_1843_);
lean_dec(v___x_1841_);
if (v___x_1844_ == 0)
{
lean_dec(v___x_1837_);
lean_dec(v_index_1833_);
v___y_1809_ = v___x_1825_;
v___y_1810_ = v___x_1828_;
v___y_1811_ = v___x_1824_;
goto v___jp_1808_;
}
else
{
lean_object* v___x_1845_; 
v___x_1845_ = l_Std_DHashMap_Raw_setEntry___redArg(v_snd_1758_, v___x_1837_, v_index_1833_, v___x_1824_, v___x_1828_);
lean_dec(v_index_1833_);
v___y_1771_ = v___x_1845_;
goto v___jp_1770_;
}
}
}
default: 
{
lean_object* v_size_1846_; lean_object* v_keyArray_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; uint8_t v___x_1851_; 
v_size_1846_ = lean_ctor_get(v_snd_1758_, 0);
v_keyArray_1847_ = lean_ctor_get(v_snd_1758_, 1);
v___x_1848_ = lean_unsigned_to_nat(1u);
v___x_1849_ = lean_nat_add(v_size_1846_, v___x_1848_);
v___x_1850_ = lean_array_get_size(v_keyArray_1847_);
v___x_1851_ = lean_nat_dec_lt(v___x_1849_, v___x_1850_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1852_; 
lean_dec(v___x_1849_);
v___x_1852_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_1758_);
lean_dec(v_snd_1758_);
v___y_1788_ = v___x_1825_;
v___y_1789_ = v___x_1828_;
v___y_1790_ = v___x_1824_;
v___y_1791_ = v___x_1852_;
goto v___jp_1787_;
}
else
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; uint8_t v___x_1857_; 
v___x_1853_ = lean_unsigned_to_nat(4u);
v___x_1854_ = lean_nat_mul(v___x_1849_, v___x_1853_);
lean_dec(v___x_1849_);
v___x_1855_ = lean_unsigned_to_nat(3u);
v___x_1856_ = lean_nat_mul(v___x_1850_, v___x_1855_);
v___x_1857_ = lean_nat_dec_le(v___x_1854_, v___x_1856_);
lean_dec(v___x_1856_);
lean_dec(v___x_1854_);
if (v___x_1857_ == 0)
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_1758_);
lean_dec(v_snd_1758_);
v___y_1788_ = v___x_1825_;
v___y_1789_ = v___x_1828_;
v___y_1790_ = v___x_1824_;
v___y_1791_ = v___x_1858_;
goto v___jp_1787_;
}
else
{
v___y_1788_ = v___x_1825_;
v___y_1789_ = v___x_1828_;
v___y_1790_ = v___x_1824_;
v___y_1791_ = v_snd_1758_;
goto v___jp_1787_;
}
}
}
}
}
}
v___jp_1861_:
{
lean_object* v___x_1863_; 
v___x_1863_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1860_, v___x_1748_);
lean_dec(v_ref_1860_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_inc(v___y_1862_);
v___y_1821_ = v___y_1862_;
v___y_1822_ = v___y_1862_;
goto v___jp_1820_;
}
else
{
lean_object* v_val_1864_; 
v_val_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc(v_val_1864_);
lean_dec_ref_known(v___x_1863_, 1);
v___y_1821_ = v___y_1862_;
v___y_1822_ = v_val_1864_;
goto v___jp_1820_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26___boxed(lean_object* v___x_1871_, lean_object* v_as_1872_, lean_object* v_sz_1873_, lean_object* v_i_1874_, lean_object* v_b_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
uint8_t v___x_39389__boxed_1879_; size_t v_sz_boxed_1880_; size_t v_i_boxed_1881_; lean_object* v_res_1882_; 
v___x_39389__boxed_1879_ = lean_unbox(v___x_1871_);
v_sz_boxed_1880_ = lean_unbox_usize(v_sz_1873_);
lean_dec(v_sz_1873_);
v_i_boxed_1881_ = lean_unbox_usize(v_i_1874_);
lean_dec(v_i_1874_);
v_res_1882_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26(v___x_39389__boxed_1879_, v_as_1872_, v_sz_boxed_1880_, v_i_boxed_1881_, v_b_1875_, v___y_1876_, v___y_1877_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec_ref(v_as_1872_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18(uint8_t v___x_1883_, lean_object* v_t_1884_, lean_object* v_init_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v_root_1889_; lean_object* v_tail_1890_; lean_object* v___x_1891_; 
v_root_1889_ = lean_ctor_get(v_t_1884_, 0);
v_tail_1890_ = lean_ctor_get(v_t_1884_, 1);
lean_inc_ref(v_init_1885_);
v___x_1891_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25(v_init_1885_, v___x_1883_, v_root_1889_, v_init_1885_, v___y_1886_, v___y_1887_);
lean_dec_ref(v_init_1885_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1928_; 
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1894_ = v___x_1891_;
v_isShared_1895_ = v_isSharedCheck_1928_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_a_1892_);
lean_dec(v___x_1891_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1928_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
if (lean_obj_tag(v_a_1892_) == 0)
{
lean_object* v_a_1896_; lean_object* v___x_1898_; 
v_a_1896_ = lean_ctor_get(v_a_1892_, 0);
lean_inc(v_a_1896_);
lean_dec_ref_known(v_a_1892_, 1);
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 0, v_a_1896_);
v___x_1898_ = v___x_1894_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1896_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
else
{
lean_object* v_a_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; size_t v_sz_1903_; size_t v___x_1904_; lean_object* v___x_1905_; 
lean_del_object(v___x_1894_);
v_a_1900_ = lean_ctor_get(v_a_1892_, 0);
lean_inc(v_a_1900_);
lean_dec_ref_known(v_a_1892_, 1);
v___x_1901_ = lean_box(0);
v___x_1902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
lean_ctor_set(v___x_1902_, 1, v_a_1900_);
v_sz_1903_ = lean_array_size(v_tail_1890_);
v___x_1904_ = ((size_t)0ULL);
v___x_1905_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26(v___x_1883_, v_tail_1890_, v_sz_1903_, v___x_1904_, v___x_1902_, v___y_1886_, v___y_1887_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1919_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1908_ = v___x_1905_;
v_isShared_1909_ = v_isSharedCheck_1919_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1905_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1919_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v_fst_1910_; 
v_fst_1910_ = lean_ctor_get(v_a_1906_, 0);
if (lean_obj_tag(v_fst_1910_) == 0)
{
lean_object* v_snd_1911_; lean_object* v___x_1913_; 
v_snd_1911_ = lean_ctor_get(v_a_1906_, 1);
lean_inc(v_snd_1911_);
lean_dec(v_a_1906_);
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 0, v_snd_1911_);
v___x_1913_ = v___x_1908_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_snd_1911_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
else
{
lean_object* v_val_1915_; lean_object* v___x_1917_; 
lean_inc_ref(v_fst_1910_);
lean_dec(v_a_1906_);
v_val_1915_ = lean_ctor_get(v_fst_1910_, 0);
lean_inc(v_val_1915_);
lean_dec_ref_known(v_fst_1910_, 1);
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 0, v_val_1915_);
v___x_1917_ = v___x_1908_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_val_1915_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
v_a_1920_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1905_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1905_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
}
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
v_a_1929_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1891_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1891_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___boxed(lean_object* v___x_1937_, lean_object* v_t_1938_, lean_object* v_init_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
uint8_t v___x_39597__boxed_1943_; lean_object* v_res_1944_; 
v___x_39597__boxed_1943_ = lean_unbox(v___x_1937_);
v_res_1944_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18(v___x_39597__boxed_1943_, v_t_1938_, v_init_1939_, v___y_1940_, v___y_1941_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec_ref(v_t_1938_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__13(lean_object* v_opts_1945_, lean_object* v_opt_1946_){
_start:
{
lean_object* v_name_1947_; lean_object* v_map_1948_; lean_object* v___x_1949_; 
v_name_1947_ = lean_ctor_get(v_opt_1946_, 0);
v_map_1948_ = lean_ctor_get(v_opts_1945_, 0);
v___x_1949_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1948_, v_name_1947_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v___x_1950_; 
v___x_1950_ = lean_box(0);
return v___x_1950_;
}
else
{
lean_object* v_val_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1960_; 
v_val_1951_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1953_ = v___x_1949_;
v_isShared_1954_ = v_isSharedCheck_1960_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_val_1951_);
lean_dec(v___x_1949_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1960_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
if (lean_obj_tag(v_val_1951_) == 0)
{
lean_object* v_v_1955_; lean_object* v___x_1957_; 
v_v_1955_ = lean_ctor_get(v_val_1951_, 0);
lean_inc_ref(v_v_1955_);
lean_dec_ref_known(v_val_1951_, 1);
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 0, v_v_1955_);
v___x_1957_ = v___x_1953_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_v_1955_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
else
{
lean_object* v___x_1959_; 
lean_del_object(v___x_1953_);
lean_dec(v_val_1951_);
v___x_1959_ = lean_box(0);
return v___x_1959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__13___boxed(lean_object* v_opts_1961_, lean_object* v_opt_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__13(v_opts_1961_, v_opt_1962_);
lean_dec_ref(v_opt_1962_);
lean_dec_ref(v_opts_1961_);
return v_res_1963_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1964_ = lean_unsigned_to_nat(32u);
v___x_1965_ = lean_mk_empty_array_with_capacity(v___x_1964_);
v___x_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1965_);
return v___x_1966_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___redArg___closed__1(void){
_start:
{
size_t v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1967_ = ((size_t)5ULL);
v___x_1968_ = lean_unsigned_to_nat(0u);
v___x_1969_ = lean_unsigned_to_nat(32u);
v___x_1970_ = lean_mk_empty_array_with_capacity(v___x_1969_);
v___x_1971_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___redArg___closed__0);
v___x_1972_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1972_, 0, v___x_1971_);
lean_ctor_set(v___x_1972_, 1, v___x_1970_);
lean_ctor_set(v___x_1972_, 2, v___x_1968_);
lean_ctor_set(v___x_1972_, 3, v___x_1968_);
lean_ctor_set_usize(v___x_1972_, 4, v___x_1967_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___redArg(lean_object* v___y_1973_){
_start:
{
lean_object* v___x_1975_; lean_object* v_traceState_1976_; lean_object* v_traces_1977_; lean_object* v___x_1978_; lean_object* v_traceState_1979_; lean_object* v_env_1980_; lean_object* v_nextMacroScope_1981_; lean_object* v_ngen_1982_; lean_object* v_auxDeclNGen_1983_; lean_object* v_cache_1984_; lean_object* v_messages_1985_; lean_object* v_infoState_1986_; lean_object* v_snapshotTasks_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_2006_; 
v___x_1975_ = lean_st_ref_get(v___y_1973_);
v_traceState_1976_ = lean_ctor_get(v___x_1975_, 4);
lean_inc_ref(v_traceState_1976_);
lean_dec(v___x_1975_);
v_traces_1977_ = lean_ctor_get(v_traceState_1976_, 0);
lean_inc_ref(v_traces_1977_);
lean_dec_ref(v_traceState_1976_);
v___x_1978_ = lean_st_ref_take(v___y_1973_);
v_traceState_1979_ = lean_ctor_get(v___x_1978_, 4);
v_env_1980_ = lean_ctor_get(v___x_1978_, 0);
v_nextMacroScope_1981_ = lean_ctor_get(v___x_1978_, 1);
v_ngen_1982_ = lean_ctor_get(v___x_1978_, 2);
v_auxDeclNGen_1983_ = lean_ctor_get(v___x_1978_, 3);
v_cache_1984_ = lean_ctor_get(v___x_1978_, 5);
v_messages_1985_ = lean_ctor_get(v___x_1978_, 6);
v_infoState_1986_ = lean_ctor_get(v___x_1978_, 7);
v_snapshotTasks_1987_ = lean_ctor_get(v___x_1978_, 8);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_1989_ = v___x_1978_;
v_isShared_1990_ = v_isSharedCheck_2006_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_snapshotTasks_1987_);
lean_inc(v_infoState_1986_);
lean_inc(v_messages_1985_);
lean_inc(v_cache_1984_);
lean_inc(v_traceState_1979_);
lean_inc(v_auxDeclNGen_1983_);
lean_inc(v_ngen_1982_);
lean_inc(v_nextMacroScope_1981_);
lean_inc(v_env_1980_);
lean_dec(v___x_1978_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_2006_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
uint64_t v_tid_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2004_; 
v_tid_1991_ = lean_ctor_get_uint64(v_traceState_1979_, sizeof(void*)*1);
v_isSharedCheck_2004_ = !lean_is_exclusive(v_traceState_1979_);
if (v_isSharedCheck_2004_ == 0)
{
lean_object* v_unused_2005_; 
v_unused_2005_ = lean_ctor_get(v_traceState_1979_, 0);
lean_dec(v_unused_2005_);
v___x_1993_ = v_traceState_1979_;
v_isShared_1994_ = v_isSharedCheck_2004_;
goto v_resetjp_1992_;
}
else
{
lean_dec(v_traceState_1979_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2004_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1995_; lean_object* v___x_1997_; 
v___x_1995_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___redArg___closed__1);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 0, v___x_1995_);
v___x_1997_ = v___x_1993_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1995_);
lean_ctor_set_uint64(v_reuseFailAlloc_2003_, sizeof(void*)*1, v_tid_1991_);
v___x_1997_ = v_reuseFailAlloc_2003_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
lean_object* v___x_1999_; 
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 4, v___x_1997_);
v___x_1999_ = v___x_1989_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_env_1980_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v_nextMacroScope_1981_);
lean_ctor_set(v_reuseFailAlloc_2002_, 2, v_ngen_1982_);
lean_ctor_set(v_reuseFailAlloc_2002_, 3, v_auxDeclNGen_1983_);
lean_ctor_set(v_reuseFailAlloc_2002_, 4, v___x_1997_);
lean_ctor_set(v_reuseFailAlloc_2002_, 5, v_cache_1984_);
lean_ctor_set(v_reuseFailAlloc_2002_, 6, v_messages_1985_);
lean_ctor_set(v_reuseFailAlloc_2002_, 7, v_infoState_1986_);
lean_ctor_set(v_reuseFailAlloc_2002_, 8, v_snapshotTasks_1987_);
v___x_1999_ = v_reuseFailAlloc_2002_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = lean_st_ref_put(v___y_1973_, v___x_1999_);
v___x_2001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2001_, 0, v_traces_1977_);
return v___x_2001_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___redArg___boxed(lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___redArg(v___y_2007_);
lean_dec(v___y_2007_);
return v_res_2009_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0(uint8_t v___x_2010_, uint8_t v_suppressElabErrors_2011_, lean_object* v___x_2012_, lean_object* v_x_2013_){
_start:
{
if (lean_obj_tag(v_x_2013_) == 1)
{
lean_object* v_pre_2014_; 
v_pre_2014_ = lean_ctor_get(v_x_2013_, 0);
switch(lean_obj_tag(v_pre_2014_))
{
case 1:
{
lean_object* v_pre_2015_; 
v_pre_2015_ = lean_ctor_get(v_pre_2014_, 0);
switch(lean_obj_tag(v_pre_2015_))
{
case 0:
{
lean_object* v_str_2016_; lean_object* v_str_2017_; lean_object* v___x_2018_; uint8_t v___x_2019_; 
v_str_2016_ = lean_ctor_get(v_x_2013_, 1);
v_str_2017_ = lean_ctor_get(v_pre_2014_, 1);
v___x_2018_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__0));
v___x_2019_ = lean_string_dec_eq(v_str_2017_, v___x_2018_);
if (v___x_2019_ == 0)
{
lean_object* v___x_2020_; uint8_t v___x_2021_; 
v___x_2020_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__1));
v___x_2021_ = lean_string_dec_eq(v_str_2017_, v___x_2020_);
if (v___x_2021_ == 0)
{
return v___x_2010_;
}
else
{
lean_object* v___x_2022_; uint8_t v___x_2023_; 
v___x_2022_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__2));
v___x_2023_ = lean_string_dec_eq(v_str_2016_, v___x_2022_);
if (v___x_2023_ == 0)
{
return v___x_2010_;
}
else
{
return v_suppressElabErrors_2011_;
}
}
}
else
{
lean_object* v___x_2024_; uint8_t v___x_2025_; 
v___x_2024_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__3));
v___x_2025_ = lean_string_dec_eq(v_str_2016_, v___x_2024_);
if (v___x_2025_ == 0)
{
return v___x_2010_;
}
else
{
return v_suppressElabErrors_2011_;
}
}
}
case 1:
{
lean_object* v_pre_2026_; 
v_pre_2026_ = lean_ctor_get(v_pre_2015_, 0);
if (lean_obj_tag(v_pre_2026_) == 0)
{
lean_object* v_str_2027_; lean_object* v_str_2028_; lean_object* v_str_2029_; lean_object* v___x_2030_; uint8_t v___x_2031_; 
v_str_2027_ = lean_ctor_get(v_x_2013_, 1);
v_str_2028_ = lean_ctor_get(v_pre_2014_, 1);
v_str_2029_ = lean_ctor_get(v_pre_2015_, 1);
v___x_2030_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__4));
v___x_2031_ = lean_string_dec_eq(v_str_2029_, v___x_2030_);
if (v___x_2031_ == 0)
{
return v___x_2010_;
}
else
{
lean_object* v___x_2032_; uint8_t v___x_2033_; 
v___x_2032_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__5));
v___x_2033_ = lean_string_dec_eq(v_str_2028_, v___x_2032_);
if (v___x_2033_ == 0)
{
return v___x_2010_;
}
else
{
lean_object* v___x_2034_; uint8_t v___x_2035_; 
v___x_2034_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___lam__0___closed__6));
v___x_2035_ = lean_string_dec_eq(v_str_2027_, v___x_2034_);
if (v___x_2035_ == 0)
{
return v___x_2010_;
}
else
{
return v_suppressElabErrors_2011_;
}
}
}
}
else
{
return v___x_2010_;
}
}
default: 
{
return v___x_2010_;
}
}
}
case 0:
{
lean_object* v_str_2036_; uint8_t v___x_2037_; 
v_str_2036_ = lean_ctor_get(v_x_2013_, 1);
v___x_2037_ = lean_string_dec_eq(v_str_2036_, v___x_2012_);
if (v___x_2037_ == 0)
{
return v___x_2010_;
}
else
{
return v_suppressElabErrors_2011_;
}
}
default: 
{
return v___x_2010_;
}
}
}
else
{
return v___x_2010_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0___boxed(lean_object* v___x_2038_, lean_object* v_suppressElabErrors_2039_, lean_object* v___x_2040_, lean_object* v_x_2041_){
_start:
{
uint8_t v___x_39801__boxed_2042_; uint8_t v_suppressElabErrors_boxed_2043_; uint8_t v_res_2044_; lean_object* v_r_2045_; 
v___x_39801__boxed_2042_ = lean_unbox(v___x_2038_);
v_suppressElabErrors_boxed_2043_ = lean_unbox(v_suppressElabErrors_2039_);
v_res_2044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0(v___x_39801__boxed_2042_, v_suppressElabErrors_boxed_2043_, v___x_2040_, v_x_2041_);
lean_dec(v_x_2041_);
lean_dec_ref(v___x_2040_);
v_r_2045_ = lean_box(v_res_2044_);
return v_r_2045_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0(void){
_start:
{
lean_object* v___x_2046_; double v___x_2047_; 
v___x_2046_ = lean_unsigned_to_nat(0u);
v___x_2047_ = lean_float_of_nat(v___x_2046_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20(uint8_t v___x_2048_, lean_object* v_as_2049_, size_t v_sz_2050_, size_t v_i_2051_, lean_object* v_b_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v_a_2057_; uint8_t v___x_2061_; 
v___x_2061_ = lean_usize_dec_lt(v_i_2051_, v_sz_2050_);
if (v___x_2061_ == 0)
{
lean_object* v___x_2062_; 
v___x_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2062_, 0, v_b_2052_);
return v___x_2062_;
}
else
{
lean_object* v_a_2063_; lean_object* v_fst_2064_; lean_object* v_snd_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2141_; 
v_a_2063_ = lean_array_uget(v_as_2049_, v_i_2051_);
v_fst_2064_ = lean_ctor_get(v_a_2063_, 0);
v_snd_2065_ = lean_ctor_get(v_a_2063_, 1);
v_isSharedCheck_2141_ = !lean_is_exclusive(v_a_2063_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2067_ = v_a_2063_;
v_isShared_2068_ = v_isSharedCheck_2141_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_snd_2065_);
lean_inc(v_fst_2064_);
lean_dec(v_a_2063_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2141_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v_fst_2069_; lean_object* v_snd_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2140_; 
v_fst_2069_ = lean_ctor_get(v_fst_2064_, 0);
v_snd_2070_ = lean_ctor_get(v_fst_2064_, 1);
v_isSharedCheck_2140_ = !lean_is_exclusive(v_fst_2064_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2072_ = v_fst_2064_;
v_isShared_2073_ = v_isSharedCheck_2140_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_snd_2070_);
lean_inc(v_fst_2069_);
lean_dec(v_fst_2064_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2140_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; double v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v_fileName_2079_; lean_object* v_fileMap_2080_; uint8_t v_suppressElabErrors_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2088_; 
v___x_2074_ = lean_box(0);
v___x_2075_ = lean_box(0);
v___x_2076_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0);
v___x_2077_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__28_spec__42___closed__0));
v___x_2078_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2078_, 0, v___x_2074_);
lean_ctor_set(v___x_2078_, 1, v___x_2075_);
lean_ctor_set(v___x_2078_, 2, v___x_2077_);
lean_ctor_set_float(v___x_2078_, sizeof(void*)*3, v___x_2076_);
lean_ctor_set_float(v___x_2078_, sizeof(void*)*3 + 8, v___x_2076_);
lean_ctor_set_uint8(v___x_2078_, sizeof(void*)*3 + 16, v___x_2061_);
v_fileName_2079_ = lean_ctor_get(v___y_2053_, 0);
v_fileMap_2080_ = lean_ctor_get(v___y_2053_, 1);
v_suppressElabErrors_2081_ = lean_ctor_get_uint8(v___y_2053_, sizeof(void*)*14 + 1);
v___x_2082_ = lean_box(0);
v___x_2083_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_2084_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_2085_ = l_Lean_MessageData_nil;
v___x_2086_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2078_);
lean_ctor_set(v___x_2086_, 1, v___x_2085_);
lean_ctor_set(v___x_2086_, 2, v_snd_2065_);
if (v_isShared_2073_ == 0)
{
lean_ctor_set_tag(v___x_2072_, 8);
lean_ctor_set(v___x_2072_, 1, v___x_2086_);
lean_ctor_set(v___x_2072_, 0, v___x_2084_);
v___x_2088_ = v___x_2072_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2084_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v___x_2086_);
v___x_2088_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
uint8_t v___x_2089_; lean_object* v___x_2090_; lean_object* v___y_2092_; lean_object* v___y_2093_; 
v___x_2089_ = 0;
lean_inc_ref(v_fileMap_2080_);
lean_inc_ref(v_fileName_2079_);
v___x_2090_ = l_Lean_Elab_mkMessageCore(v_fileName_2079_, v_fileMap_2080_, v___x_2088_, v___x_2089_, v_fst_2069_, v_snd_2070_);
lean_dec(v_snd_2070_);
lean_dec(v_fst_2069_);
if (v_suppressElabErrors_2081_ == 0)
{
v___y_2092_ = v___y_2053_;
v___y_2093_ = v___y_2054_;
goto v___jp_2091_;
}
else
{
lean_object* v_data_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___f_2137_; uint8_t v___x_2138_; 
v_data_2134_ = lean_ctor_get(v___x_2090_, 4);
lean_inc(v_data_2134_);
v___x_2135_ = lean_box(v___x_2048_);
v___x_2136_ = lean_box(v_suppressElabErrors_2081_);
v___f_2137_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2137_, 0, v___x_2135_);
lean_closure_set(v___f_2137_, 1, v___x_2136_);
lean_closure_set(v___f_2137_, 2, v___x_2083_);
v___x_2138_ = l_Lean_MessageData_hasTag(v___f_2137_, v_data_2134_);
if (v___x_2138_ == 0)
{
lean_dec_ref(v___x_2090_);
lean_del_object(v___x_2067_);
v_a_2057_ = v___x_2082_;
goto v___jp_2056_;
}
else
{
v___y_2092_ = v___y_2053_;
v___y_2093_ = v___y_2054_;
goto v___jp_2091_;
}
}
v___jp_2091_:
{
lean_object* v___x_2094_; lean_object* v_fileName_2095_; lean_object* v_pos_2096_; lean_object* v_endPos_2097_; uint8_t v_keepFullRange_2098_; uint8_t v_severity_2099_; uint8_t v_isSilent_2100_; lean_object* v_caption_2101_; lean_object* v_data_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2133_; 
v___x_2094_ = lean_st_ref_take(v___y_2093_);
v_fileName_2095_ = lean_ctor_get(v___x_2090_, 0);
v_pos_2096_ = lean_ctor_get(v___x_2090_, 1);
v_endPos_2097_ = lean_ctor_get(v___x_2090_, 2);
v_keepFullRange_2098_ = lean_ctor_get_uint8(v___x_2090_, sizeof(void*)*5);
v_severity_2099_ = lean_ctor_get_uint8(v___x_2090_, sizeof(void*)*5 + 1);
v_isSilent_2100_ = lean_ctor_get_uint8(v___x_2090_, sizeof(void*)*5 + 2);
v_caption_2101_ = lean_ctor_get(v___x_2090_, 3);
v_data_2102_ = lean_ctor_get(v___x_2090_, 4);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2104_ = v___x_2090_;
v_isShared_2105_ = v_isSharedCheck_2133_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_data_2102_);
lean_inc(v_caption_2101_);
lean_inc(v_endPos_2097_);
lean_inc(v_pos_2096_);
lean_inc(v_fileName_2095_);
lean_dec(v___x_2090_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2133_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v_currNamespace_2106_; lean_object* v_openDecls_2107_; lean_object* v_env_2108_; lean_object* v_nextMacroScope_2109_; lean_object* v_ngen_2110_; lean_object* v_auxDeclNGen_2111_; lean_object* v_traceState_2112_; lean_object* v_cache_2113_; lean_object* v_messages_2114_; lean_object* v_infoState_2115_; lean_object* v_snapshotTasks_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2132_; 
v_currNamespace_2106_ = lean_ctor_get(v___y_2092_, 6);
v_openDecls_2107_ = lean_ctor_get(v___y_2092_, 7);
v_env_2108_ = lean_ctor_get(v___x_2094_, 0);
v_nextMacroScope_2109_ = lean_ctor_get(v___x_2094_, 1);
v_ngen_2110_ = lean_ctor_get(v___x_2094_, 2);
v_auxDeclNGen_2111_ = lean_ctor_get(v___x_2094_, 3);
v_traceState_2112_ = lean_ctor_get(v___x_2094_, 4);
v_cache_2113_ = lean_ctor_get(v___x_2094_, 5);
v_messages_2114_ = lean_ctor_get(v___x_2094_, 6);
v_infoState_2115_ = lean_ctor_get(v___x_2094_, 7);
v_snapshotTasks_2116_ = lean_ctor_get(v___x_2094_, 8);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2118_ = v___x_2094_;
v_isShared_2119_ = v_isSharedCheck_2132_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_snapshotTasks_2116_);
lean_inc(v_infoState_2115_);
lean_inc(v_messages_2114_);
lean_inc(v_cache_2113_);
lean_inc(v_traceState_2112_);
lean_inc(v_auxDeclNGen_2111_);
lean_inc(v_ngen_2110_);
lean_inc(v_nextMacroScope_2109_);
lean_inc(v_env_2108_);
lean_dec(v___x_2094_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2132_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
lean_inc(v_openDecls_2107_);
lean_inc(v_currNamespace_2106_);
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 1, v_openDecls_2107_);
lean_ctor_set(v___x_2067_, 0, v_currNamespace_2106_);
v___x_2121_ = v___x_2067_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_currNamespace_2106_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_openDecls_2107_);
v___x_2121_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
lean_object* v___x_2122_; lean_object* v___x_2124_; 
v___x_2122_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
lean_ctor_set(v___x_2122_, 1, v_data_2102_);
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 4, v___x_2122_);
v___x_2124_ = v___x_2104_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_fileName_2095_);
lean_ctor_set(v_reuseFailAlloc_2130_, 1, v_pos_2096_);
lean_ctor_set(v_reuseFailAlloc_2130_, 2, v_endPos_2097_);
lean_ctor_set(v_reuseFailAlloc_2130_, 3, v_caption_2101_);
lean_ctor_set(v_reuseFailAlloc_2130_, 4, v___x_2122_);
lean_ctor_set_uint8(v_reuseFailAlloc_2130_, sizeof(void*)*5, v_keepFullRange_2098_);
lean_ctor_set_uint8(v_reuseFailAlloc_2130_, sizeof(void*)*5 + 1, v_severity_2099_);
lean_ctor_set_uint8(v_reuseFailAlloc_2130_, sizeof(void*)*5 + 2, v_isSilent_2100_);
v___x_2124_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
lean_object* v___x_2125_; lean_object* v___x_2127_; 
v___x_2125_ = l_Lean_MessageLog_add(v___x_2124_, v_messages_2114_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 6, v___x_2125_);
v___x_2127_ = v___x_2118_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_env_2108_);
lean_ctor_set(v_reuseFailAlloc_2129_, 1, v_nextMacroScope_2109_);
lean_ctor_set(v_reuseFailAlloc_2129_, 2, v_ngen_2110_);
lean_ctor_set(v_reuseFailAlloc_2129_, 3, v_auxDeclNGen_2111_);
lean_ctor_set(v_reuseFailAlloc_2129_, 4, v_traceState_2112_);
lean_ctor_set(v_reuseFailAlloc_2129_, 5, v_cache_2113_);
lean_ctor_set(v_reuseFailAlloc_2129_, 6, v___x_2125_);
lean_ctor_set(v_reuseFailAlloc_2129_, 7, v_infoState_2115_);
lean_ctor_set(v_reuseFailAlloc_2129_, 8, v_snapshotTasks_2116_);
v___x_2127_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
lean_object* v___x_2128_; 
v___x_2128_ = lean_st_ref_put(v___y_2093_, v___x_2127_);
v_a_2057_ = v___x_2082_;
goto v___jp_2056_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___boxed(lean_object* v___x_2142_, lean_object* v_as_2143_, lean_object* v_sz_2144_, lean_object* v_i_2145_, lean_object* v_b_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
uint8_t v___x_39866__boxed_2150_; size_t v_sz_boxed_2151_; size_t v_i_boxed_2152_; lean_object* v_res_2153_; 
v___x_39866__boxed_2150_ = lean_unbox(v___x_2142_);
v_sz_boxed_2151_ = lean_unbox_usize(v_sz_2144_);
lean_dec(v_sz_2144_);
v_i_boxed_2152_ = lean_unbox_usize(v_i_2145_);
lean_dec(v_i_2145_);
v_res_2153_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20(v___x_39866__boxed_2150_, v_as_2143_, v_sz_boxed_2151_, v_i_boxed_2152_, v_b_2146_, v___y_2147_, v___y_2148_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec_ref(v_as_2143_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28(lean_object* v_b_2154_, lean_object* v_acc_2155_, lean_object* v_i_2156_){
_start:
{
lean_object* v_keyArray_2161_; lean_object* v_valueArray_2162_; lean_object* v___x_2163_; uint8_t v___x_2164_; 
v_keyArray_2161_ = lean_ctor_get(v_b_2154_, 1);
v_valueArray_2162_ = lean_ctor_get(v_b_2154_, 2);
v___x_2163_ = lean_array_get_size(v_keyArray_2161_);
v___x_2164_ = lean_nat_dec_lt(v_i_2156_, v___x_2163_);
if (v___x_2164_ == 0)
{
lean_dec(v_i_2156_);
return v_acc_2155_;
}
else
{
lean_object* v___x_2165_; uint8_t v_isSome_2166_; 
v___x_2165_ = lean_array_fget_borrowed(v_keyArray_2161_, v_i_2156_);
v_isSome_2166_ = lean_noption_is_some(v___x_2165_);
if (v_isSome_2166_ == 0)
{
goto v___jp_2157_;
}
else
{
lean_object* v___x_2167_; uint8_t v_isSome_2168_; 
v___x_2167_ = lean_array_fget_borrowed(v_valueArray_2162_, v_i_2156_);
v_isSome_2168_ = lean_noption_is_some(v___x_2167_);
if (v_isSome_2168_ == 0)
{
goto v___jp_2157_;
}
else
{
lean_object* v_val_2169_; lean_object* v_val_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
lean_inc(v___x_2165_);
v_val_2169_ = lean_noption_get(v___x_2165_);
lean_inc(v___x_2167_);
v_val_2170_ = lean_noption_get(v___x_2167_);
v___x_2171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2171_, 0, v_val_2169_);
lean_ctor_set(v___x_2171_, 1, v_val_2170_);
v___x_2172_ = lean_array_push(v_acc_2155_, v___x_2171_);
v___x_2173_ = lean_unsigned_to_nat(1u);
v___x_2174_ = lean_nat_add(v_i_2156_, v___x_2173_);
lean_dec(v_i_2156_);
v_acc_2155_ = v___x_2172_;
v_i_2156_ = v___x_2174_;
goto _start;
}
}
}
v___jp_2157_:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2158_ = lean_unsigned_to_nat(1u);
v___x_2159_ = lean_nat_add(v_i_2156_, v___x_2158_);
lean_dec(v_i_2156_);
v_i_2156_ = v___x_2159_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28___boxed(lean_object* v_b_2176_, lean_object* v_acc_2177_, lean_object* v_i_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28(v_b_2176_, v_acc_2177_, v_i_2178_);
lean_dec_ref(v_b_2176_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19(lean_object* v_init_2180_, lean_object* v_b_2181_){
_start:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2182_ = lean_unsigned_to_nat(0u);
v___x_2183_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28(v_b_2181_, v_init_2180_, v___x_2182_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___boxed(lean_object* v_init_2184_, lean_object* v_b_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_Std_DHashMap_Raw_foldM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19(v_init_2184_, v_b_2185_);
lean_dec_ref(v_b_2185_);
return v_res_2186_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(lean_object* v_x_2187_, lean_object* v_x_2188_){
_start:
{
lean_object* v_fst_2189_; lean_object* v_fst_2190_; lean_object* v_fst_2191_; lean_object* v_fst_2192_; uint8_t v___x_2193_; 
v_fst_2189_ = lean_ctor_get(v_x_2187_, 0);
v_fst_2190_ = lean_ctor_get(v_x_2188_, 0);
v_fst_2191_ = lean_ctor_get(v_fst_2189_, 0);
v_fst_2192_ = lean_ctor_get(v_fst_2190_, 0);
v___x_2193_ = lean_nat_dec_lt(v_fst_2191_, v_fst_2192_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0___boxed(lean_object* v_x_2194_, lean_object* v_x_2195_){
_start:
{
uint8_t v_res_2196_; lean_object* v_r_2197_; 
v_res_2196_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(v_x_2194_, v_x_2195_);
lean_dec_ref(v_x_2195_);
lean_dec_ref(v_x_2194_);
v_r_2197_ = lean_box(v_res_2196_);
return v_r_2197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg(lean_object* v_hi_2198_, lean_object* v_pivot_2199_, lean_object* v_as_2200_, lean_object* v_i_2201_, lean_object* v_k_2202_){
_start:
{
uint8_t v___x_2203_; 
v___x_2203_ = lean_nat_dec_lt(v_k_2202_, v_hi_2198_);
if (v___x_2203_ == 0)
{
lean_object* v___x_2204_; lean_object* v___x_2205_; 
lean_dec(v_k_2202_);
v___x_2204_ = lean_array_fswap(v_as_2200_, v_i_2201_, v_hi_2198_);
v___x_2205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2205_, 0, v_i_2201_);
lean_ctor_set(v___x_2205_, 1, v___x_2204_);
return v___x_2205_;
}
else
{
lean_object* v___x_2206_; lean_object* v_fst_2207_; lean_object* v_fst_2208_; lean_object* v_fst_2209_; lean_object* v_fst_2210_; uint8_t v___x_2211_; 
v___x_2206_ = lean_array_fget_borrowed(v_as_2200_, v_k_2202_);
v_fst_2207_ = lean_ctor_get(v___x_2206_, 0);
v_fst_2208_ = lean_ctor_get(v_pivot_2199_, 0);
v_fst_2209_ = lean_ctor_get(v_fst_2207_, 0);
v_fst_2210_ = lean_ctor_get(v_fst_2208_, 0);
v___x_2211_ = lean_nat_dec_lt(v_fst_2209_, v_fst_2210_);
if (v___x_2211_ == 0)
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2212_ = lean_unsigned_to_nat(1u);
v___x_2213_ = lean_nat_add(v_k_2202_, v___x_2212_);
lean_dec(v_k_2202_);
v_k_2202_ = v___x_2213_;
goto _start;
}
else
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2215_ = lean_array_fswap(v_as_2200_, v_i_2201_, v_k_2202_);
v___x_2216_ = lean_unsigned_to_nat(1u);
v___x_2217_ = lean_nat_add(v_i_2201_, v___x_2216_);
lean_dec(v_i_2201_);
v___x_2218_ = lean_nat_add(v_k_2202_, v___x_2216_);
lean_dec(v_k_2202_);
v_as_2200_ = v___x_2215_;
v_i_2201_ = v___x_2217_;
v_k_2202_ = v___x_2218_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg___boxed(lean_object* v_hi_2220_, lean_object* v_pivot_2221_, lean_object* v_as_2222_, lean_object* v_i_2223_, lean_object* v_k_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg(v_hi_2220_, v_pivot_2221_, v_as_2222_, v_i_2223_, v_k_2224_);
lean_dec_ref(v_pivot_2221_);
lean_dec(v_hi_2220_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(lean_object* v_n_2226_, lean_object* v_as_2227_, lean_object* v_lo_2228_, lean_object* v_hi_2229_){
_start:
{
lean_object* v___y_2231_; uint8_t v___x_2241_; 
v___x_2241_ = lean_nat_dec_lt(v_lo_2228_, v_hi_2229_);
if (v___x_2241_ == 0)
{
lean_dec(v_lo_2228_);
return v_as_2227_;
}
else
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v_mid_2244_; lean_object* v___y_2246_; lean_object* v___y_2252_; lean_object* v___x_2257_; lean_object* v___x_2258_; uint8_t v___x_2259_; 
v___x_2242_ = lean_nat_add(v_lo_2228_, v_hi_2229_);
v___x_2243_ = lean_unsigned_to_nat(1u);
v_mid_2244_ = lean_nat_shiftr(v___x_2242_, v___x_2243_);
lean_dec(v___x_2242_);
v___x_2257_ = lean_array_fget_borrowed(v_as_2227_, v_mid_2244_);
v___x_2258_ = lean_array_fget_borrowed(v_as_2227_, v_lo_2228_);
v___x_2259_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(v___x_2257_, v___x_2258_);
if (v___x_2259_ == 0)
{
v___y_2252_ = v_as_2227_;
goto v___jp_2251_;
}
else
{
lean_object* v___x_2260_; 
v___x_2260_ = lean_array_fswap(v_as_2227_, v_lo_2228_, v_mid_2244_);
v___y_2252_ = v___x_2260_;
goto v___jp_2251_;
}
v___jp_2245_:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; uint8_t v___x_2249_; 
v___x_2247_ = lean_array_fget_borrowed(v___y_2246_, v_mid_2244_);
v___x_2248_ = lean_array_fget_borrowed(v___y_2246_, v_hi_2229_);
v___x_2249_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(v___x_2247_, v___x_2248_);
if (v___x_2249_ == 0)
{
lean_dec(v_mid_2244_);
v___y_2231_ = v___y_2246_;
goto v___jp_2230_;
}
else
{
lean_object* v___x_2250_; 
v___x_2250_ = lean_array_fswap(v___y_2246_, v_mid_2244_, v_hi_2229_);
lean_dec(v_mid_2244_);
v___y_2231_ = v___x_2250_;
goto v___jp_2230_;
}
}
v___jp_2251_:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; uint8_t v___x_2255_; 
v___x_2253_ = lean_array_fget_borrowed(v___y_2252_, v_hi_2229_);
v___x_2254_ = lean_array_fget_borrowed(v___y_2252_, v_lo_2228_);
v___x_2255_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(v___x_2253_, v___x_2254_);
if (v___x_2255_ == 0)
{
v___y_2246_ = v___y_2252_;
goto v___jp_2245_;
}
else
{
lean_object* v___x_2256_; 
v___x_2256_ = lean_array_fswap(v___y_2252_, v_lo_2228_, v_hi_2229_);
v___y_2246_ = v___x_2256_;
goto v___jp_2245_;
}
}
}
v___jp_2230_:
{
lean_object* v_pivot_2232_; lean_object* v___x_2233_; lean_object* v_fst_2234_; lean_object* v_snd_2235_; uint8_t v___x_2236_; 
v_pivot_2232_ = lean_array_fget(v___y_2231_, v_hi_2229_);
lean_inc_n(v_lo_2228_, 2);
v___x_2233_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg(v_hi_2229_, v_pivot_2232_, v___y_2231_, v_lo_2228_, v_lo_2228_);
lean_dec(v_pivot_2232_);
v_fst_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc(v_fst_2234_);
v_snd_2235_ = lean_ctor_get(v___x_2233_, 1);
lean_inc(v_snd_2235_);
lean_dec_ref(v___x_2233_);
v___x_2236_ = lean_nat_dec_le(v_hi_2229_, v_fst_2234_);
if (v___x_2236_ == 0)
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2237_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(v_n_2226_, v_snd_2235_, v_lo_2228_, v_fst_2234_);
v___x_2238_ = lean_unsigned_to_nat(1u);
v___x_2239_ = lean_nat_add(v_fst_2234_, v___x_2238_);
lean_dec(v_fst_2234_);
v_as_2227_ = v___x_2237_;
v_lo_2228_ = v___x_2239_;
goto _start;
}
else
{
lean_dec(v_fst_2234_);
lean_dec(v_lo_2228_);
return v_snd_2235_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___boxed(lean_object* v_n_2261_, lean_object* v_as_2262_, lean_object* v_lo_2263_, lean_object* v_hi_2264_){
_start:
{
lean_object* v_res_2265_; 
v_res_2265_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(v_n_2261_, v_as_2262_, v_lo_2263_, v_hi_2264_);
lean_dec(v_hi_2264_);
lean_dec(v_n_2261_);
return v_res_2265_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0(void){
_start:
{
lean_object* v_cellCount_2266_; lean_object* v___x_2267_; 
v_cellCount_2266_ = lean_unsigned_to_nat(16u);
v___x_2267_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_2266_);
return v___x_2267_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1(void){
_start:
{
lean_object* v_cellCount_2268_; lean_object* v___x_2269_; 
v_cellCount_2268_ = lean_unsigned_to_nat(16u);
v___x_2269_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2268_);
return v___x_2269_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__2(void){
_start:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v_pos2traces_2273_; 
v___x_2270_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1, &l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1);
v___x_2271_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0, &l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0);
v___x_2272_ = lean_unsigned_to_nat(0u);
v_pos2traces_2273_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_pos2traces_2273_, 0, v___x_2272_);
lean_ctor_set(v_pos2traces_2273_, 1, v___x_2271_);
lean_ctor_set(v_pos2traces_2273_, 2, v___x_2270_);
return v_pos2traces_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__9(lean_object* v___y_2274_, lean_object* v___y_2275_){
_start:
{
lean_object* v_options_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v_options_2280_ = lean_ctor_get(v___y_2274_, 2);
v___x_2281_ = l_Lean_trace_profiler_output;
v___x_2282_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__13(v_options_2280_, v___x_2281_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v___x_2283_; uint8_t v___x_2284_; 
v___x_2283_ = l_Lean_trace_profiler_serve;
v___x_2284_ = l_Lean_Option_get___at___00main_spec__7(v_options_2280_, v___x_2283_);
if (v___x_2284_ == 0)
{
lean_object* v___x_2285_; lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2336_; 
v___x_2285_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___redArg(v___y_2275_);
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2288_ = v___x_2285_;
v_isShared_2289_ = v_isSharedCheck_2336_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2285_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2336_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
uint8_t v___x_2290_; 
v___x_2290_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_2286_);
if (v___x_2290_ == 0)
{
lean_object* v___x_2291_; lean_object* v_pos2traces_2292_; lean_object* v___x_2293_; 
lean_del_object(v___x_2288_);
v___x_2291_ = lean_unsigned_to_nat(0u);
v_pos2traces_2292_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__9___closed__2, &l_Lean_addTraceAsMessages___at___00main_spec__9___closed__2_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__2);
v___x_2293_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18(v___x_2290_, v_a_2286_, v_pos2traces_2292_, v___y_2274_, v___y_2275_);
lean_dec(v_a_2286_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; lean_object* v___y_2296_; lean_object* v_size_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___y_2314_; lean_object* v___y_2315_; uint8_t v___x_2317_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
lean_inc(v_a_2294_);
lean_dec_ref_known(v___x_2293_, 1);
v_size_2309_ = lean_ctor_get(v_a_2294_, 0);
v___x_2310_ = lean_mk_empty_array_with_capacity(v_size_2309_);
v___x_2311_ = l_Std_DHashMap_Raw_foldM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19(v___x_2310_, v_a_2294_);
lean_dec(v_a_2294_);
v___x_2312_ = lean_array_get_size(v___x_2311_);
v___x_2317_ = lean_nat_dec_eq(v___x_2312_, v___x_2291_);
if (v___x_2317_ == 0)
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___y_2321_; uint8_t v___x_2323_; 
v___x_2318_ = lean_unsigned_to_nat(1u);
v___x_2319_ = lean_nat_sub(v___x_2312_, v___x_2318_);
v___x_2323_ = lean_nat_dec_le(v___x_2291_, v___x_2319_);
if (v___x_2323_ == 0)
{
lean_inc(v___x_2319_);
v___y_2321_ = v___x_2319_;
goto v___jp_2320_;
}
else
{
v___y_2321_ = v___x_2291_;
goto v___jp_2320_;
}
v___jp_2320_:
{
uint8_t v___x_2322_; 
v___x_2322_ = lean_nat_dec_le(v___y_2321_, v___x_2319_);
if (v___x_2322_ == 0)
{
lean_dec(v___x_2319_);
lean_inc(v___y_2321_);
v___y_2314_ = v___y_2321_;
v___y_2315_ = v___y_2321_;
goto v___jp_2313_;
}
else
{
v___y_2314_ = v___y_2321_;
v___y_2315_ = v___x_2319_;
goto v___jp_2313_;
}
}
}
else
{
v___y_2296_ = v___x_2311_;
goto v___jp_2295_;
}
v___jp_2295_:
{
lean_object* v___x_2297_; size_t v_sz_2298_; size_t v___x_2299_; lean_object* v___x_2300_; 
v___x_2297_ = lean_box(0);
v_sz_2298_ = lean_array_size(v___y_2296_);
v___x_2299_ = ((size_t)0ULL);
v___x_2300_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20(v___x_2284_, v___y_2296_, v_sz_2298_, v___x_2299_, v___x_2297_, v___y_2274_, v___y_2275_);
lean_dec_ref(v___y_2296_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2307_; 
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2307_ == 0)
{
lean_object* v_unused_2308_; 
v_unused_2308_ = lean_ctor_get(v___x_2300_, 0);
lean_dec(v_unused_2308_);
v___x_2302_ = v___x_2300_;
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
else
{
lean_dec(v___x_2300_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2305_; 
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 0, v___x_2297_);
v___x_2305_ = v___x_2302_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2297_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
else
{
return v___x_2300_;
}
}
v___jp_2313_:
{
lean_object* v___x_2316_; 
v___x_2316_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(v___x_2312_, v___x_2311_, v___y_2314_, v___y_2315_);
lean_dec(v___y_2315_);
v___y_2296_ = v___x_2316_;
goto v___jp_2295_;
}
}
else
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
v_a_2324_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2326_ = v___x_2293_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2293_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2324_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
else
{
lean_object* v___x_2332_; lean_object* v___x_2334_; 
lean_dec(v_a_2286_);
v___x_2332_ = lean_box(0);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 0, v___x_2332_);
v___x_2334_ = v___x_2288_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2332_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
}
}
else
{
goto v___jp_2277_;
}
}
else
{
lean_dec_ref_known(v___x_2282_, 1);
goto v___jp_2277_;
}
v___jp_2277_:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2278_ = lean_box(0);
v___x_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2278_);
return v___x_2279_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__9___boxed(lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l_Lean_addTraceAsMessages___at___00main_spec__9(v___y_2337_, v___y_2338_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10(lean_object* v_as_2341_, size_t v_sz_2342_, size_t v_i_2343_, lean_object* v_b_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
uint8_t v___x_2348_; 
v___x_2348_ = lean_usize_dec_lt(v_i_2343_, v_sz_2342_);
if (v___x_2348_ == 0)
{
lean_object* v___x_2349_; 
v___x_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2349_, 0, v_b_2344_);
return v___x_2349_;
}
else
{
lean_object* v_options_2350_; lean_object* v_a_2351_; lean_object* v___x_2352_; 
v_options_2350_ = lean_ctor_get(v___y_2345_, 2);
v_a_2351_ = lean_array_uget_borrowed(v_as_2341_, v_i_2343_);
lean_inc_ref(v_options_2350_);
lean_inc(v_a_2351_);
v___x_2352_ = l_Lean_Compiler_LCNF_resumeCompilation(v_a_2351_, v_options_2350_, v___y_2345_, v___y_2346_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v___x_2353_; 
lean_dec_ref_known(v___x_2352_, 1);
v___x_2353_ = l_Lean_addTraceAsMessages___at___00main_spec__9(v___y_2345_, v___y_2346_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v___x_2354_; size_t v___x_2355_; size_t v___x_2356_; 
lean_dec_ref_known(v___x_2353_, 1);
v___x_2354_ = lean_box(0);
v___x_2355_ = ((size_t)1ULL);
v___x_2356_ = lean_usize_add(v_i_2343_, v___x_2355_);
v_i_2343_ = v___x_2356_;
v_b_2344_ = v___x_2354_;
goto _start;
}
else
{
return v___x_2353_;
}
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2359_; 
v_a_2358_ = lean_ctor_get(v___x_2352_, 0);
lean_inc(v_a_2358_);
lean_dec_ref_known(v___x_2352_, 1);
v___x_2359_ = l_Lean_addTraceAsMessages___at___00main_spec__9(v___y_2345_, v___y_2346_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2366_; 
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2366_ == 0)
{
lean_object* v_unused_2367_; 
v_unused_2367_ = lean_ctor_get(v___x_2359_, 0);
lean_dec(v_unused_2367_);
v___x_2361_ = v___x_2359_;
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
else
{
lean_dec(v___x_2359_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2364_; 
if (v_isShared_2362_ == 0)
{
lean_ctor_set_tag(v___x_2361_, 1);
lean_ctor_set(v___x_2361_, 0, v_a_2358_);
v___x_2364_ = v___x_2361_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_a_2358_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
else
{
lean_dec(v_a_2358_);
return v___x_2359_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10___boxed(lean_object* v_as_2368_, lean_object* v_sz_2369_, lean_object* v_i_2370_, lean_object* v_b_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
size_t v_sz_boxed_2375_; size_t v_i_boxed_2376_; lean_object* v_res_2377_; 
v_sz_boxed_2375_ = lean_unbox_usize(v_sz_2369_);
lean_dec(v_sz_2369_);
v_i_boxed_2376_ = lean_unbox_usize(v_i_2370_);
lean_dec(v_i_2370_);
v_res_2377_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10(v_as_2368_, v_sz_boxed_2375_, v_i_boxed_2376_, v_b_2371_, v___y_2372_, v___y_2373_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec_ref(v_as_2368_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__38___redArg(lean_object* v_as_2381_, size_t v_sz_2382_, size_t v_i_2383_, lean_object* v_b_2384_, lean_object* v___y_2385_){
_start:
{
uint8_t v___x_2387_; 
v___x_2387_ = lean_usize_dec_lt(v_i_2383_, v_sz_2382_);
if (v___x_2387_ == 0)
{
lean_object* v___x_2388_; 
v___x_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2388_, 0, v_b_2384_);
return v___x_2388_;
}
else
{
uint8_t v___x_2389_; lean_object* v_a_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
lean_dec_ref(v_b_2384_);
v___x_2389_ = 0;
v_a_2390_ = lean_array_uget_borrowed(v_as_2381_, v_i_2383_);
lean_inc(v_a_2390_);
v___x_2391_ = l_Lean_Message_toString(v_a_2390_, v___x_2389_);
v___x_2392_ = l_IO_eprintln___at___00main_spec__5(v___x_2391_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v___x_2393_; size_t v___x_2394_; size_t v___x_2395_; 
lean_dec_ref_known(v___x_2392_, 1);
v___x_2393_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__38___redArg___closed__0));
v___x_2394_ = ((size_t)1ULL);
v___x_2395_ = lean_usize_add(v_i_2383_, v___x_2394_);
v_i_2383_ = v___x_2395_;
v_b_2384_ = v___x_2393_;
goto _start;
}
else
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2409_; 
v_a_2397_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2399_ = v___x_2392_;
v_isShared_2400_ = v_isSharedCheck_2409_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2392_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2409_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v_ref_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2407_; 
v_ref_2401_ = lean_ctor_get(v___y_2385_, 5);
v___x_2402_ = lean_io_error_to_string(v_a_2397_);
v___x_2403_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2402_);
v___x_2404_ = l_Lean_MessageData_ofFormat(v___x_2403_);
lean_inc(v_ref_2401_);
v___x_2405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2405_, 0, v_ref_2401_);
lean_ctor_set(v___x_2405_, 1, v___x_2404_);
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 0, v___x_2405_);
v___x_2407_ = v___x_2399_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v___x_2405_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__38___redArg___boxed(lean_object* v_as_2410_, lean_object* v_sz_2411_, lean_object* v_i_2412_, lean_object* v_b_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
size_t v_sz_boxed_2416_; size_t v_i_boxed_2417_; lean_object* v_res_2418_; 
v_sz_boxed_2416_ = lean_unbox_usize(v_sz_2411_);
lean_dec(v_sz_2411_);
v_i_boxed_2417_ = lean_unbox_usize(v_i_2412_);
lean_dec(v_i_2412_);
v_res_2418_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__38___redArg(v_as_2410_, v_sz_boxed_2416_, v_i_boxed_2417_, v_b_2413_, v___y_2414_);
lean_dec_ref(v___y_2414_);
lean_dec_ref(v_as_2410_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25(lean_object* v_as_2419_, size_t v_sz_2420_, size_t v_i_2421_, lean_object* v_b_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_){
_start:
{
uint8_t v___x_2426_; 
v___x_2426_ = lean_usize_dec_lt(v_i_2421_, v_sz_2420_);
if (v___x_2426_ == 0)
{
lean_object* v___x_2427_; 
v___x_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2427_, 0, v_b_2422_);
return v___x_2427_;
}
else
{
uint8_t v___x_2428_; lean_object* v_a_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
lean_dec_ref(v_b_2422_);
v___x_2428_ = 0;
v_a_2429_ = lean_array_uget_borrowed(v_as_2419_, v_i_2421_);
lean_inc(v_a_2429_);
v___x_2430_ = l_Lean_Message_toString(v_a_2429_, v___x_2428_);
v___x_2431_ = l_IO_eprintln___at___00main_spec__5(v___x_2430_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_object* v___x_2432_; size_t v___x_2433_; size_t v___x_2434_; lean_object* v___x_2435_; 
lean_dec_ref_known(v___x_2431_, 1);
v___x_2432_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__38___redArg___closed__0));
v___x_2433_ = ((size_t)1ULL);
v___x_2434_ = lean_usize_add(v_i_2421_, v___x_2433_);
v___x_2435_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__38___redArg(v_as_2419_, v_sz_2420_, v___x_2434_, v___x_2432_, v___y_2423_);
return v___x_2435_;
}
else
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2448_; 
v_a_2436_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2438_ = v___x_2431_;
v_isShared_2439_ = v_isSharedCheck_2448_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2431_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2448_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v_ref_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2446_; 
v_ref_2440_ = lean_ctor_get(v___y_2423_, 5);
v___x_2441_ = lean_io_error_to_string(v_a_2436_);
v___x_2442_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2441_);
v___x_2443_ = l_Lean_MessageData_ofFormat(v___x_2442_);
lean_inc(v_ref_2440_);
v___x_2444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2444_, 0, v_ref_2440_);
lean_ctor_set(v___x_2444_, 1, v___x_2443_);
if (v_isShared_2439_ == 0)
{
lean_ctor_set(v___x_2438_, 0, v___x_2444_);
v___x_2446_ = v___x_2438_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v___x_2444_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25___boxed(lean_object* v_as_2449_, lean_object* v_sz_2450_, lean_object* v_i_2451_, lean_object* v_b_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_){
_start:
{
size_t v_sz_boxed_2456_; size_t v_i_boxed_2457_; lean_object* v_res_2458_; 
v_sz_boxed_2456_ = lean_unbox_usize(v_sz_2450_);
lean_dec(v_sz_2450_);
v_i_boxed_2457_ = lean_unbox_usize(v_i_2451_);
lean_dec(v_i_2451_);
v_res_2458_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25(v_as_2449_, v_sz_boxed_2456_, v_i_boxed_2457_, v_b_2452_, v___y_2453_, v___y_2454_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
lean_dec_ref(v_as_2449_);
return v_res_2458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24_spec__36_spec__50___redArg(lean_object* v_as_2462_, size_t v_sz_2463_, size_t v_i_2464_, lean_object* v_b_2465_, lean_object* v___y_2466_){
_start:
{
uint8_t v___x_2468_; 
v___x_2468_ = lean_usize_dec_lt(v_i_2464_, v_sz_2463_);
if (v___x_2468_ == 0)
{
lean_object* v___x_2469_; 
v___x_2469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2469_, 0, v_b_2465_);
return v___x_2469_;
}
else
{
uint8_t v___x_2470_; lean_object* v_a_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
lean_dec_ref(v_b_2465_);
v___x_2470_ = 0;
v_a_2471_ = lean_array_uget_borrowed(v_as_2462_, v_i_2464_);
lean_inc(v_a_2471_);
v___x_2472_ = l_Lean_Message_toString(v_a_2471_, v___x_2470_);
v___x_2473_ = l_IO_eprintln___at___00main_spec__5(v___x_2472_);
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_object* v___x_2474_; size_t v___x_2475_; size_t v___x_2476_; 
lean_dec_ref_known(v___x_2473_, 1);
v___x_2474_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24_spec__36_spec__50___redArg___closed__0));
v___x_2475_ = ((size_t)1ULL);
v___x_2476_ = lean_usize_add(v_i_2464_, v___x_2475_);
v_i_2464_ = v___x_2476_;
v_b_2465_ = v___x_2474_;
goto _start;
}
else
{
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2490_; 
v_a_2478_ = lean_ctor_get(v___x_2473_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2480_ = v___x_2473_;
v_isShared_2481_ = v_isSharedCheck_2490_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2473_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2490_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v_ref_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2488_; 
v_ref_2482_ = lean_ctor_get(v___y_2466_, 5);
v___x_2483_ = lean_io_error_to_string(v_a_2478_);
v___x_2484_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2483_);
v___x_2485_ = l_Lean_MessageData_ofFormat(v___x_2484_);
lean_inc(v_ref_2482_);
v___x_2486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2486_, 0, v_ref_2482_);
lean_ctor_set(v___x_2486_, 1, v___x_2485_);
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 0, v___x_2486_);
v___x_2488_ = v___x_2480_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v___x_2486_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24_spec__36_spec__50___redArg___boxed(lean_object* v_as_2491_, lean_object* v_sz_2492_, lean_object* v_i_2493_, lean_object* v_b_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
size_t v_sz_boxed_2497_; size_t v_i_boxed_2498_; lean_object* v_res_2499_; 
v_sz_boxed_2497_ = lean_unbox_usize(v_sz_2492_);
lean_dec(v_sz_2492_);
v_i_boxed_2498_ = lean_unbox_usize(v_i_2493_);
lean_dec(v_i_2493_);
v_res_2499_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24_spec__36_spec__50___redArg(v_as_2491_, v_sz_boxed_2497_, v_i_boxed_2498_, v_b_2494_, v___y_2495_);
lean_dec_ref(v___y_2495_);
lean_dec_ref(v_as_2491_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24_spec__36(lean_object* v_as_2500_, size_t v_sz_2501_, size_t v_i_2502_, lean_object* v_b_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
uint8_t v___x_2507_; 
v___x_2507_ = lean_usize_dec_lt(v_i_2502_, v_sz_2501_);
if (v___x_2507_ == 0)
{
lean_object* v___x_2508_; 
v___x_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2508_, 0, v_b_2503_);
return v___x_2508_;
}
else
{
uint8_t v___x_2509_; lean_object* v_a_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
lean_dec_ref(v_b_2503_);
v___x_2509_ = 0;
v_a_2510_ = lean_array_uget_borrowed(v_as_2500_, v_i_2502_);
lean_inc(v_a_2510_);
v___x_2511_ = l_Lean_Message_toString(v_a_2510_, v___x_2509_);
v___x_2512_ = l_IO_eprintln___at___00main_spec__5(v___x_2511_);
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_object* v___x_2513_; size_t v___x_2514_; size_t v___x_2515_; lean_object* v___x_2516_; 
lean_dec_ref_known(v___x_2512_, 1);
v___x_2513_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24_spec__36_spec__50___redArg___closed__0));
v___x_2514_ = ((size_t)1ULL);
v___x_2515_ = lean_usize_add(v_i_2502_, v___x_2514_);
v___x_2516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24_spec__36_spec__50___redArg(v_as_2500_, v_sz_2501_, v___x_2515_, v___x_2513_, v___y_2504_);
return v___x_2516_;
}
else
{
lean_object* v_a_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2529_; 
v_a_2517_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2519_ = v___x_2512_;
v_isShared_2520_ = v_isSharedCheck_2529_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_dec(v___x_2512_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2529_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v_ref_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2527_; 
v_ref_2521_ = lean_ctor_get(v___y_2504_, 5);
v___x_2522_ = lean_io_error_to_string(v_a_2517_);
v___x_2523_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2522_);
v___x_2524_ = l_Lean_MessageData_ofFormat(v___x_2523_);
lean_inc(v_ref_2521_);
v___x_2525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2525_, 0, v_ref_2521_);
lean_ctor_set(v___x_2525_, 1, v___x_2524_);
if (v_isShared_2520_ == 0)
{
lean_ctor_set(v___x_2519_, 0, v___x_2525_);
v___x_2527_ = v___x_2519_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v___x_2525_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24_spec__36___boxed(lean_object* v_as_2530_, lean_object* v_sz_2531_, lean_object* v_i_2532_, lean_object* v_b_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
size_t v_sz_boxed_2537_; size_t v_i_boxed_2538_; lean_object* v_res_2539_; 
v_sz_boxed_2537_ = lean_unbox_usize(v_sz_2531_);
lean_dec(v_sz_2531_);
v_i_boxed_2538_ = lean_unbox_usize(v_i_2532_);
lean_dec(v_i_2532_);
v_res_2539_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24_spec__36(v_as_2530_, v_sz_boxed_2537_, v_i_boxed_2538_, v_b_2533_, v___y_2534_, v___y_2535_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
lean_dec_ref(v_as_2530_);
return v_res_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24(lean_object* v_init_2540_, lean_object* v_n_2541_, lean_object* v_b_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
if (lean_obj_tag(v_n_2541_) == 0)
{
lean_object* v_cs_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; size_t v_sz_2549_; size_t v___x_2550_; lean_object* v___x_2551_; 
v_cs_2546_ = lean_ctor_get(v_n_2541_, 0);
v___x_2547_ = lean_box(0);
v___x_2548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2547_);
lean_ctor_set(v___x_2548_, 1, v_b_2542_);
v_sz_2549_ = lean_array_size(v_cs_2546_);
v___x_2550_ = ((size_t)0ULL);
v___x_2551_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24_spec__35(v_init_2540_, v_cs_2546_, v_sz_2549_, v___x_2550_, v___x_2548_, v___y_2543_, v___y_2544_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2566_; 
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2554_ = v___x_2551_;
v_isShared_2555_ = v_isSharedCheck_2566_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2551_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2566_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v_fst_2556_; 
v_fst_2556_ = lean_ctor_get(v_a_2552_, 0);
if (lean_obj_tag(v_fst_2556_) == 0)
{
lean_object* v_snd_2557_; lean_object* v___x_2558_; lean_object* v___x_2560_; 
v_snd_2557_ = lean_ctor_get(v_a_2552_, 1);
lean_inc(v_snd_2557_);
lean_dec(v_a_2552_);
v___x_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2558_, 0, v_snd_2557_);
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 0, v___x_2558_);
v___x_2560_ = v___x_2554_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2558_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
else
{
lean_object* v_val_2562_; lean_object* v___x_2564_; 
lean_inc_ref(v_fst_2556_);
lean_dec(v_a_2552_);
v_val_2562_ = lean_ctor_get(v_fst_2556_, 0);
lean_inc(v_val_2562_);
lean_dec_ref_known(v_fst_2556_, 1);
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 0, v_val_2562_);
v___x_2564_ = v___x_2554_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_val_2562_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
}
else
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2574_; 
v_a_2567_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2569_ = v___x_2551_;
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2551_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2572_; 
if (v_isShared_2570_ == 0)
{
v___x_2572_ = v___x_2569_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_a_2567_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
}
else
{
lean_object* v_vs_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; size_t v_sz_2578_; size_t v___x_2579_; lean_object* v___x_2580_; 
v_vs_2575_ = lean_ctor_get(v_n_2541_, 0);
v___x_2576_ = lean_box(0);
v___x_2577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2576_);
lean_ctor_set(v___x_2577_, 1, v_b_2542_);
v_sz_2578_ = lean_array_size(v_vs_2575_);
v___x_2579_ = ((size_t)0ULL);
v___x_2580_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24_spec__36(v_vs_2575_, v_sz_2578_, v___x_2579_, v___x_2577_, v___y_2543_, v___y_2544_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2595_; 
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2583_ = v___x_2580_;
v_isShared_2584_ = v_isSharedCheck_2595_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2580_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2595_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v_fst_2585_; 
v_fst_2585_ = lean_ctor_get(v_a_2581_, 0);
if (lean_obj_tag(v_fst_2585_) == 0)
{
lean_object* v_snd_2586_; lean_object* v___x_2587_; lean_object* v___x_2589_; 
v_snd_2586_ = lean_ctor_get(v_a_2581_, 1);
lean_inc(v_snd_2586_);
lean_dec(v_a_2581_);
v___x_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2587_, 0, v_snd_2586_);
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 0, v___x_2587_);
v___x_2589_ = v___x_2583_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2587_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
else
{
lean_object* v_val_2591_; lean_object* v___x_2593_; 
lean_inc_ref(v_fst_2585_);
lean_dec(v_a_2581_);
v_val_2591_ = lean_ctor_get(v_fst_2585_, 0);
lean_inc(v_val_2591_);
lean_dec_ref_known(v_fst_2585_, 1);
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 0, v_val_2591_);
v___x_2593_ = v___x_2583_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_val_2591_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
else
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2603_; 
v_a_2596_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2598_ = v___x_2580_;
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2580_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2601_; 
if (v_isShared_2599_ == 0)
{
v___x_2601_ = v___x_2598_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_a_2596_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24_spec__35(lean_object* v_init_2604_, lean_object* v_as_2605_, size_t v_sz_2606_, size_t v_i_2607_, lean_object* v_b_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
uint8_t v___x_2612_; 
v___x_2612_ = lean_usize_dec_lt(v_i_2607_, v_sz_2606_);
if (v___x_2612_ == 0)
{
lean_object* v___x_2613_; 
v___x_2613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2613_, 0, v_b_2608_);
return v___x_2613_;
}
else
{
lean_object* v_snd_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2648_; 
v_snd_2614_ = lean_ctor_get(v_b_2608_, 1);
v_isSharedCheck_2648_ = !lean_is_exclusive(v_b_2608_);
if (v_isSharedCheck_2648_ == 0)
{
lean_object* v_unused_2649_; 
v_unused_2649_ = lean_ctor_get(v_b_2608_, 0);
lean_dec(v_unused_2649_);
v___x_2616_ = v_b_2608_;
v_isShared_2617_ = v_isSharedCheck_2648_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_snd_2614_);
lean_dec(v_b_2608_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2648_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v_a_2618_; lean_object* v___x_2619_; 
v_a_2618_ = lean_array_uget_borrowed(v_as_2605_, v_i_2607_);
lean_inc(v_snd_2614_);
v___x_2619_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24(v_init_2604_, v_a_2618_, v_snd_2614_, v___y_2609_, v___y_2610_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2639_; 
v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2622_ = v___x_2619_;
v_isShared_2623_ = v_isSharedCheck_2639_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2619_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2639_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
if (lean_obj_tag(v_a_2620_) == 0)
{
lean_object* v___x_2624_; lean_object* v___x_2626_; 
v___x_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2624_, 0, v_a_2620_);
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 0, v___x_2624_);
v___x_2626_ = v___x_2616_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v___x_2624_);
lean_ctor_set(v_reuseFailAlloc_2630_, 1, v_snd_2614_);
v___x_2626_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
lean_object* v___x_2628_; 
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 0, v___x_2626_);
v___x_2628_ = v___x_2622_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v___x_2626_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
else
{
lean_object* v_a_2631_; lean_object* v___x_2632_; lean_object* v___x_2634_; 
lean_del_object(v___x_2622_);
lean_dec(v_snd_2614_);
v_a_2631_ = lean_ctor_get(v_a_2620_, 0);
lean_inc(v_a_2631_);
lean_dec_ref_known(v_a_2620_, 1);
v___x_2632_ = lean_box(0);
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 1, v_a_2631_);
lean_ctor_set(v___x_2616_, 0, v___x_2632_);
v___x_2634_ = v___x_2616_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v___x_2632_);
lean_ctor_set(v_reuseFailAlloc_2638_, 1, v_a_2631_);
v___x_2634_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
size_t v___x_2635_; size_t v___x_2636_; 
v___x_2635_ = ((size_t)1ULL);
v___x_2636_ = lean_usize_add(v_i_2607_, v___x_2635_);
v_i_2607_ = v___x_2636_;
v_b_2608_ = v___x_2634_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2647_; 
lean_del_object(v___x_2616_);
lean_dec(v_snd_2614_);
v_a_2640_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2642_ = v___x_2619_;
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2619_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2645_; 
if (v_isShared_2643_ == 0)
{
v___x_2645_ = v___x_2642_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_a_2640_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24_spec__35___boxed(lean_object* v_init_2650_, lean_object* v_as_2651_, lean_object* v_sz_2652_, lean_object* v_i_2653_, lean_object* v_b_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_){
_start:
{
size_t v_sz_boxed_2658_; size_t v_i_boxed_2659_; lean_object* v_res_2660_; 
v_sz_boxed_2658_ = lean_unbox_usize(v_sz_2652_);
lean_dec(v_sz_2652_);
v_i_boxed_2659_ = lean_unbox_usize(v_i_2653_);
lean_dec(v_i_2653_);
v_res_2660_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24_spec__35(v_init_2650_, v_as_2651_, v_sz_boxed_2658_, v_i_boxed_2659_, v_b_2654_, v___y_2655_, v___y_2656_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec_ref(v_as_2651_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24___boxed(lean_object* v_init_2661_, lean_object* v_n_2662_, lean_object* v_b_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24(v_init_2661_, v_n_2662_, v_b_2663_, v___y_2664_, v___y_2665_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec_ref(v_n_2662_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__11(lean_object* v_t_2668_, lean_object* v_init_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
lean_object* v_root_2673_; lean_object* v_tail_2674_; lean_object* v___x_2675_; 
v_root_2673_ = lean_ctor_get(v_t_2668_, 0);
v_tail_2674_ = lean_ctor_get(v_t_2668_, 1);
v___x_2675_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24(v_init_2669_, v_root_2673_, v_init_2669_, v___y_2670_, v___y_2671_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2712_; 
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2678_ = v___x_2675_;
v_isShared_2679_ = v_isSharedCheck_2712_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2675_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2712_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
if (lean_obj_tag(v_a_2676_) == 0)
{
lean_object* v_a_2680_; lean_object* v___x_2682_; 
v_a_2680_ = lean_ctor_get(v_a_2676_, 0);
lean_inc(v_a_2680_);
lean_dec_ref_known(v_a_2676_, 1);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 0, v_a_2680_);
v___x_2682_ = v___x_2678_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_a_2680_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
else
{
lean_object* v_a_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; size_t v_sz_2687_; size_t v___x_2688_; lean_object* v___x_2689_; 
lean_del_object(v___x_2678_);
v_a_2684_ = lean_ctor_get(v_a_2676_, 0);
lean_inc(v_a_2684_);
lean_dec_ref_known(v_a_2676_, 1);
v___x_2685_ = lean_box(0);
v___x_2686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2685_);
lean_ctor_set(v___x_2686_, 1, v_a_2684_);
v_sz_2687_ = lean_array_size(v_tail_2674_);
v___x_2688_ = ((size_t)0ULL);
v___x_2689_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25(v_tail_2674_, v_sz_2687_, v___x_2688_, v___x_2686_, v___y_2670_, v___y_2671_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2703_; 
v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2692_ = v___x_2689_;
v_isShared_2693_ = v_isSharedCheck_2703_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2689_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2703_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v_fst_2694_; 
v_fst_2694_ = lean_ctor_get(v_a_2690_, 0);
if (lean_obj_tag(v_fst_2694_) == 0)
{
lean_object* v_snd_2695_; lean_object* v___x_2697_; 
v_snd_2695_ = lean_ctor_get(v_a_2690_, 1);
lean_inc(v_snd_2695_);
lean_dec(v_a_2690_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 0, v_snd_2695_);
v___x_2697_ = v___x_2692_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_snd_2695_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
else
{
lean_object* v_val_2699_; lean_object* v___x_2701_; 
lean_inc_ref(v_fst_2694_);
lean_dec(v_a_2690_);
v_val_2699_ = lean_ctor_get(v_fst_2694_, 0);
lean_inc(v_val_2699_);
lean_dec_ref_known(v_fst_2694_, 1);
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 0, v_val_2699_);
v___x_2701_ = v___x_2692_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_val_2699_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
else
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
v_a_2704_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___x_2689_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2689_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
}
}
else
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2720_; 
v_a_2713_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2715_ = v___x_2675_;
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___x_2675_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_a_2713_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__11___boxed(lean_object* v_t_2721_, lean_object* v_init_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
lean_object* v_res_2726_; 
v_res_2726_ = l_Lean_PersistentArray_forIn___at___00main_spec__11(v_t_2721_, v_init_2722_, v___y_2723_, v___y_2724_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec_ref(v_t_2721_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(lean_object* v_as_2727_, size_t v_sz_2728_, size_t v_i_2729_, lean_object* v_b_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
uint8_t v___x_2734_; 
v___x_2734_ = lean_usize_dec_lt(v_i_2729_, v_sz_2728_);
if (v___x_2734_ == 0)
{
lean_object* v___x_2735_; 
v___x_2735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2735_, 0, v_b_2730_);
return v___x_2735_;
}
else
{
lean_object* v_a_2736_; lean_object* v_declNames_2737_; lean_object* v___x_2738_; size_t v_sz_2739_; size_t v___x_2740_; lean_object* v___x_2741_; 
v_a_2736_ = lean_array_uget_borrowed(v_as_2727_, v_i_2729_);
v_declNames_2737_ = lean_ctor_get(v_a_2736_, 0);
v___x_2738_ = lean_box(0);
v_sz_2739_ = lean_array_size(v_declNames_2737_);
v___x_2740_ = ((size_t)0ULL);
v___x_2741_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10(v_declNames_2737_, v_sz_2739_, v___x_2740_, v___x_2738_, v___y_2731_, v___y_2732_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v___x_2742_; 
lean_dec_ref_known(v___x_2741_, 1);
v___x_2742_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v___y_2732_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; lean_object* v_unreported_2744_; lean_object* v___x_2745_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
lean_inc(v_a_2743_);
lean_dec_ref_known(v___x_2742_, 1);
v_unreported_2744_ = lean_ctor_get(v_a_2743_, 1);
lean_inc_ref(v_unreported_2744_);
lean_dec(v_a_2743_);
v___x_2745_ = l_Lean_PersistentArray_forIn___at___00main_spec__11(v_unreported_2744_, v___x_2738_, v___y_2731_, v___y_2732_);
lean_dec_ref(v_unreported_2744_);
if (lean_obj_tag(v___x_2745_) == 0)
{
size_t v___x_2746_; size_t v___x_2747_; 
lean_dec_ref_known(v___x_2745_, 1);
v___x_2746_ = ((size_t)1ULL);
v___x_2747_ = lean_usize_add(v_i_2729_, v___x_2746_);
v_i_2729_ = v___x_2747_;
v_b_2730_ = v___x_2738_;
goto _start;
}
else
{
return v___x_2745_;
}
}
else
{
lean_object* v_a_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2756_; 
v_a_2749_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2751_ = v___x_2742_;
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_a_2749_);
lean_dec(v___x_2742_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___x_2754_; 
if (v_isShared_2752_ == 0)
{
v___x_2754_ = v___x_2751_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2749_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
}
else
{
return v___x_2741_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___boxed(lean_object* v_as_2757_, lean_object* v_sz_2758_, lean_object* v_i_2759_, lean_object* v_b_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
size_t v_sz_boxed_2764_; size_t v_i_boxed_2765_; lean_object* v_res_2766_; 
v_sz_boxed_2764_ = lean_unbox_usize(v_sz_2758_);
lean_dec(v_sz_2758_);
v_i_boxed_2765_ = lean_unbox_usize(v_i_2759_);
lean_dec(v_i_2759_);
v_res_2766_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(v_as_2757_, v_sz_boxed_2764_, v_i_boxed_2765_, v_b_2760_, v___y_2761_, v___y_2762_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
lean_dec_ref(v_as_2757_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__9_spec__14(lean_object* v_as_2767_, size_t v_sz_2768_, size_t v_i_2769_, lean_object* v_b_2770_){
_start:
{
uint8_t v___x_2772_; 
v___x_2772_ = lean_usize_dec_lt(v_i_2769_, v_sz_2768_);
if (v___x_2772_ == 0)
{
lean_object* v___x_2773_; 
v___x_2773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2773_, 0, v_b_2770_);
return v___x_2773_;
}
else
{
uint8_t v___x_2774_; lean_object* v_a_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; 
lean_dec_ref(v_b_2770_);
v___x_2774_ = 0;
v_a_2775_ = lean_array_uget_borrowed(v_as_2767_, v_i_2769_);
lean_inc(v_a_2775_);
v___x_2776_ = l_Lean_Message_toString(v_a_2775_, v___x_2774_);
v___x_2777_ = l_IO_eprintln___at___00main_spec__5(v___x_2776_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v___x_2778_; size_t v___x_2779_; size_t v___x_2780_; 
lean_dec_ref_known(v___x_2777_, 1);
v___x_2778_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__38___redArg___closed__0));
v___x_2779_ = ((size_t)1ULL);
v___x_2780_ = lean_usize_add(v_i_2769_, v___x_2779_);
v_i_2769_ = v___x_2780_;
v_b_2770_ = v___x_2778_;
goto _start;
}
else
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
v_a_2782_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2777_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2777_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2782_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__9_spec__14___boxed(lean_object* v_as_2790_, lean_object* v_sz_2791_, lean_object* v_i_2792_, lean_object* v_b_2793_, lean_object* v___y_2794_){
_start:
{
size_t v_sz_boxed_2795_; size_t v_i_boxed_2796_; lean_object* v_res_2797_; 
v_sz_boxed_2795_ = lean_unbox_usize(v_sz_2791_);
lean_dec(v_sz_2791_);
v_i_boxed_2796_ = lean_unbox_usize(v_i_2792_);
lean_dec(v_i_2792_);
v_res_2797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__9_spec__14(v_as_2790_, v_sz_boxed_2795_, v_i_boxed_2796_, v_b_2793_);
lean_dec_ref(v_as_2790_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__9(lean_object* v_as_2798_, size_t v_sz_2799_, size_t v_i_2800_, lean_object* v_b_2801_){
_start:
{
uint8_t v___x_2803_; 
v___x_2803_ = lean_usize_dec_lt(v_i_2800_, v_sz_2799_);
if (v___x_2803_ == 0)
{
lean_object* v___x_2804_; 
v___x_2804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2804_, 0, v_b_2801_);
return v___x_2804_;
}
else
{
uint8_t v___x_2805_; lean_object* v_a_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
lean_dec_ref(v_b_2801_);
v___x_2805_ = 0;
v_a_2806_ = lean_array_uget_borrowed(v_as_2798_, v_i_2800_);
lean_inc(v_a_2806_);
v___x_2807_ = l_Lean_Message_toString(v_a_2806_, v___x_2805_);
v___x_2808_ = l_IO_eprintln___at___00main_spec__5(v___x_2807_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v___x_2809_; size_t v___x_2810_; size_t v___x_2811_; lean_object* v___x_2812_; 
lean_dec_ref_known(v___x_2808_, 1);
v___x_2809_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__38___redArg___closed__0));
v___x_2810_ = ((size_t)1ULL);
v___x_2811_ = lean_usize_add(v_i_2800_, v___x_2810_);
v___x_2812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__9_spec__14(v_as_2798_, v_sz_2799_, v___x_2811_, v___x_2809_);
return v___x_2812_;
}
else
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
v_a_2813_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2815_ = v___x_2808_;
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2808_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2816_ == 0)
{
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_a_2813_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__9___boxed(lean_object* v_as_2821_, lean_object* v_sz_2822_, lean_object* v_i_2823_, lean_object* v_b_2824_, lean_object* v___y_2825_){
_start:
{
size_t v_sz_boxed_2826_; size_t v_i_boxed_2827_; lean_object* v_res_2828_; 
v_sz_boxed_2826_ = lean_unbox_usize(v_sz_2822_);
lean_dec(v_sz_2822_);
v_i_boxed_2827_ = lean_unbox_usize(v_i_2823_);
lean_dec(v_i_2823_);
v_res_2828_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__9(v_as_2821_, v_sz_boxed_2826_, v_i_boxed_2827_, v_b_2824_);
lean_dec_ref(v_as_2821_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__8_spec__12_spec__25(lean_object* v_as_2829_, size_t v_sz_2830_, size_t v_i_2831_, lean_object* v_b_2832_){
_start:
{
uint8_t v___x_2834_; 
v___x_2834_ = lean_usize_dec_lt(v_i_2831_, v_sz_2830_);
if (v___x_2834_ == 0)
{
lean_object* v___x_2835_; 
v___x_2835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2835_, 0, v_b_2832_);
return v___x_2835_;
}
else
{
uint8_t v___x_2836_; lean_object* v_a_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
lean_dec_ref(v_b_2832_);
v___x_2836_ = 0;
v_a_2837_ = lean_array_uget_borrowed(v_as_2829_, v_i_2831_);
lean_inc(v_a_2837_);
v___x_2838_ = l_Lean_Message_toString(v_a_2837_, v___x_2836_);
v___x_2839_ = l_IO_eprintln___at___00main_spec__5(v___x_2838_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v___x_2840_; size_t v___x_2841_; size_t v___x_2842_; 
lean_dec_ref_known(v___x_2839_, 1);
v___x_2840_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24_spec__36_spec__50___redArg___closed__0));
v___x_2841_ = ((size_t)1ULL);
v___x_2842_ = lean_usize_add(v_i_2831_, v___x_2841_);
v_i_2831_ = v___x_2842_;
v_b_2832_ = v___x_2840_;
goto _start;
}
else
{
lean_object* v_a_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2851_; 
v_a_2844_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2846_ = v___x_2839_;
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_a_2844_);
lean_dec(v___x_2839_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__8_spec__12_spec__25___boxed(lean_object* v_as_2852_, lean_object* v_sz_2853_, lean_object* v_i_2854_, lean_object* v_b_2855_, lean_object* v___y_2856_){
_start:
{
size_t v_sz_boxed_2857_; size_t v_i_boxed_2858_; lean_object* v_res_2859_; 
v_sz_boxed_2857_ = lean_unbox_usize(v_sz_2853_);
lean_dec(v_sz_2853_);
v_i_boxed_2858_ = lean_unbox_usize(v_i_2854_);
lean_dec(v_i_2854_);
v_res_2859_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__8_spec__12_spec__25(v_as_2852_, v_sz_boxed_2857_, v_i_boxed_2858_, v_b_2855_);
lean_dec_ref(v_as_2852_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__8_spec__12(lean_object* v_as_2860_, size_t v_sz_2861_, size_t v_i_2862_, lean_object* v_b_2863_){
_start:
{
uint8_t v___x_2865_; 
v___x_2865_ = lean_usize_dec_lt(v_i_2862_, v_sz_2861_);
if (v___x_2865_ == 0)
{
lean_object* v___x_2866_; 
v___x_2866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2866_, 0, v_b_2863_);
return v___x_2866_;
}
else
{
uint8_t v___x_2867_; lean_object* v_a_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
lean_dec_ref(v_b_2863_);
v___x_2867_ = 0;
v_a_2868_ = lean_array_uget_borrowed(v_as_2860_, v_i_2862_);
lean_inc(v_a_2868_);
v___x_2869_ = l_Lean_Message_toString(v_a_2868_, v___x_2867_);
v___x_2870_ = l_IO_eprintln___at___00main_spec__5(v___x_2869_);
if (lean_obj_tag(v___x_2870_) == 0)
{
lean_object* v___x_2871_; size_t v___x_2872_; size_t v___x_2873_; lean_object* v___x_2874_; 
lean_dec_ref_known(v___x_2870_, 1);
v___x_2871_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24_spec__36_spec__50___redArg___closed__0));
v___x_2872_ = ((size_t)1ULL);
v___x_2873_ = lean_usize_add(v_i_2862_, v___x_2872_);
v___x_2874_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__8_spec__12_spec__25(v_as_2860_, v_sz_2861_, v___x_2873_, v___x_2871_);
return v___x_2874_;
}
else
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2882_; 
v_a_2875_ = lean_ctor_get(v___x_2870_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2870_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2877_ = v___x_2870_;
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___x_2870_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2880_; 
if (v_isShared_2878_ == 0)
{
v___x_2880_ = v___x_2877_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_a_2875_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__8_spec__12___boxed(lean_object* v_as_2883_, lean_object* v_sz_2884_, lean_object* v_i_2885_, lean_object* v_b_2886_, lean_object* v___y_2887_){
_start:
{
size_t v_sz_boxed_2888_; size_t v_i_boxed_2889_; lean_object* v_res_2890_; 
v_sz_boxed_2888_ = lean_unbox_usize(v_sz_2884_);
lean_dec(v_sz_2884_);
v_i_boxed_2889_ = lean_unbox_usize(v_i_2885_);
lean_dec(v_i_2885_);
v_res_2890_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__8_spec__12(v_as_2883_, v_sz_boxed_2888_, v_i_boxed_2889_, v_b_2886_);
lean_dec_ref(v_as_2883_);
return v_res_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__8(lean_object* v_init_2891_, lean_object* v_n_2892_, lean_object* v_b_2893_){
_start:
{
if (lean_obj_tag(v_n_2892_) == 0)
{
lean_object* v_cs_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; size_t v_sz_2898_; size_t v___x_2899_; lean_object* v___x_2900_; 
v_cs_2895_ = lean_ctor_get(v_n_2892_, 0);
v___x_2896_ = lean_box(0);
v___x_2897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2896_);
lean_ctor_set(v___x_2897_, 1, v_b_2893_);
v_sz_2898_ = lean_array_size(v_cs_2895_);
v___x_2899_ = ((size_t)0ULL);
v___x_2900_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__8_spec__11(v_init_2891_, v_cs_2895_, v_sz_2898_, v___x_2899_, v___x_2897_);
if (lean_obj_tag(v___x_2900_) == 0)
{
lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2915_; 
v_a_2901_ = lean_ctor_get(v___x_2900_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2900_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2903_ = v___x_2900_;
v_isShared_2904_ = v_isSharedCheck_2915_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2900_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2915_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v_fst_2905_; 
v_fst_2905_ = lean_ctor_get(v_a_2901_, 0);
if (lean_obj_tag(v_fst_2905_) == 0)
{
lean_object* v_snd_2906_; lean_object* v___x_2907_; lean_object* v___x_2909_; 
v_snd_2906_ = lean_ctor_get(v_a_2901_, 1);
lean_inc(v_snd_2906_);
lean_dec(v_a_2901_);
v___x_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2907_, 0, v_snd_2906_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 0, v___x_2907_);
v___x_2909_ = v___x_2903_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v___x_2907_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
else
{
lean_object* v_val_2911_; lean_object* v___x_2913_; 
lean_inc_ref(v_fst_2905_);
lean_dec(v_a_2901_);
v_val_2911_ = lean_ctor_get(v_fst_2905_, 0);
lean_inc(v_val_2911_);
lean_dec_ref_known(v_fst_2905_, 1);
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 0, v_val_2911_);
v___x_2913_ = v___x_2903_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_val_2911_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
}
else
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2923_; 
v_a_2916_ = lean_ctor_get(v___x_2900_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2900_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2918_ = v___x_2900_;
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2900_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_a_2916_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
}
else
{
lean_object* v_vs_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; size_t v_sz_2927_; size_t v___x_2928_; lean_object* v___x_2929_; 
v_vs_2924_ = lean_ctor_get(v_n_2892_, 0);
v___x_2925_ = lean_box(0);
v___x_2926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2925_);
lean_ctor_set(v___x_2926_, 1, v_b_2893_);
v_sz_2927_ = lean_array_size(v_vs_2924_);
v___x_2928_ = ((size_t)0ULL);
v___x_2929_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__8_spec__12(v_vs_2924_, v_sz_2927_, v___x_2928_, v___x_2926_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2944_; 
v_a_2930_ = lean_ctor_get(v___x_2929_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2932_ = v___x_2929_;
v_isShared_2933_ = v_isSharedCheck_2944_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2929_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2944_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v_fst_2934_; 
v_fst_2934_ = lean_ctor_get(v_a_2930_, 0);
if (lean_obj_tag(v_fst_2934_) == 0)
{
lean_object* v_snd_2935_; lean_object* v___x_2936_; lean_object* v___x_2938_; 
v_snd_2935_ = lean_ctor_get(v_a_2930_, 1);
lean_inc(v_snd_2935_);
lean_dec(v_a_2930_);
v___x_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2936_, 0, v_snd_2935_);
if (v_isShared_2933_ == 0)
{
lean_ctor_set(v___x_2932_, 0, v___x_2936_);
v___x_2938_ = v___x_2932_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v___x_2936_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
else
{
lean_object* v_val_2940_; lean_object* v___x_2942_; 
lean_inc_ref(v_fst_2934_);
lean_dec(v_a_2930_);
v_val_2940_ = lean_ctor_get(v_fst_2934_, 0);
lean_inc(v_val_2940_);
lean_dec_ref_known(v_fst_2934_, 1);
if (v_isShared_2933_ == 0)
{
lean_ctor_set(v___x_2932_, 0, v_val_2940_);
v___x_2942_ = v___x_2932_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_val_2940_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
}
else
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2952_; 
v_a_2945_ = lean_ctor_get(v___x_2929_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2947_ = v___x_2929_;
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2929_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2952_;
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
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2945_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__8_spec__11(lean_object* v_init_2953_, lean_object* v_as_2954_, size_t v_sz_2955_, size_t v_i_2956_, lean_object* v_b_2957_){
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
lean_object* v_snd_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2995_; 
v_snd_2961_ = lean_ctor_get(v_b_2957_, 1);
v_isSharedCheck_2995_ = !lean_is_exclusive(v_b_2957_);
if (v_isSharedCheck_2995_ == 0)
{
lean_object* v_unused_2996_; 
v_unused_2996_ = lean_ctor_get(v_b_2957_, 0);
lean_dec(v_unused_2996_);
v___x_2963_ = v_b_2957_;
v_isShared_2964_ = v_isSharedCheck_2995_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_snd_2961_);
lean_dec(v_b_2957_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2995_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v_a_2965_; lean_object* v___x_2966_; 
v_a_2965_ = lean_array_uget_borrowed(v_as_2954_, v_i_2956_);
lean_inc(v_snd_2961_);
v___x_2966_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__8(v_init_2953_, v_a_2965_, v_snd_2961_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2986_; 
v_a_2967_ = lean_ctor_get(v___x_2966_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2969_ = v___x_2966_;
v_isShared_2970_ = v_isSharedCheck_2986_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2966_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2986_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
if (lean_obj_tag(v_a_2967_) == 0)
{
lean_object* v___x_2971_; lean_object* v___x_2973_; 
v___x_2971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2971_, 0, v_a_2967_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 0, v___x_2971_);
v___x_2973_ = v___x_2963_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v___x_2971_);
lean_ctor_set(v_reuseFailAlloc_2977_, 1, v_snd_2961_);
v___x_2973_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
lean_object* v___x_2975_; 
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 0, v___x_2973_);
v___x_2975_ = v___x_2969_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2973_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
else
{
lean_object* v_a_2978_; lean_object* v___x_2979_; lean_object* v___x_2981_; 
lean_del_object(v___x_2969_);
lean_dec(v_snd_2961_);
v_a_2978_ = lean_ctor_get(v_a_2967_, 0);
lean_inc(v_a_2978_);
lean_dec_ref_known(v_a_2967_, 1);
v___x_2979_ = lean_box(0);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 1, v_a_2978_);
lean_ctor_set(v___x_2963_, 0, v___x_2979_);
v___x_2981_ = v___x_2963_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v___x_2979_);
lean_ctor_set(v_reuseFailAlloc_2985_, 1, v_a_2978_);
v___x_2981_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
size_t v___x_2982_; size_t v___x_2983_; 
v___x_2982_ = ((size_t)1ULL);
v___x_2983_ = lean_usize_add(v_i_2956_, v___x_2982_);
v_i_2956_ = v___x_2983_;
v_b_2957_ = v___x_2981_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_2994_; 
lean_del_object(v___x_2963_);
lean_dec(v_snd_2961_);
v_a_2987_ = lean_ctor_get(v___x_2966_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2989_ = v___x_2966_;
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_a_2987_);
lean_dec(v___x_2966_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2992_; 
if (v_isShared_2990_ == 0)
{
v___x_2992_ = v___x_2989_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_a_2987_);
v___x_2992_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
return v___x_2992_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__8_spec__11___boxed(lean_object* v_init_2997_, lean_object* v_as_2998_, lean_object* v_sz_2999_, lean_object* v_i_3000_, lean_object* v_b_3001_, lean_object* v___y_3002_){
_start:
{
size_t v_sz_boxed_3003_; size_t v_i_boxed_3004_; lean_object* v_res_3005_; 
v_sz_boxed_3003_ = lean_unbox_usize(v_sz_2999_);
lean_dec(v_sz_2999_);
v_i_boxed_3004_ = lean_unbox_usize(v_i_3000_);
lean_dec(v_i_3000_);
v_res_3005_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__8_spec__11(v_init_2997_, v_as_2998_, v_sz_boxed_3003_, v_i_boxed_3004_, v_b_3001_);
lean_dec_ref(v_as_2998_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__8___boxed(lean_object* v_init_3006_, lean_object* v_n_3007_, lean_object* v_b_3008_, lean_object* v___y_3009_){
_start:
{
lean_object* v_res_3010_; 
v_res_3010_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__8(v_init_3006_, v_n_3007_, v_b_3008_);
lean_dec_ref(v_n_3007_);
return v_res_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__6(lean_object* v_t_3011_, lean_object* v_init_3012_){
_start:
{
lean_object* v_root_3014_; lean_object* v_tail_3015_; lean_object* v___x_3016_; 
v_root_3014_ = lean_ctor_get(v_t_3011_, 0);
v_tail_3015_ = lean_ctor_get(v_t_3011_, 1);
v___x_3016_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__8(v_init_3012_, v_root_3014_, v_init_3012_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_a_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3053_; 
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3019_ = v___x_3016_;
v_isShared_3020_ = v_isSharedCheck_3053_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_a_3017_);
lean_dec(v___x_3016_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3053_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
if (lean_obj_tag(v_a_3017_) == 0)
{
lean_object* v_a_3021_; lean_object* v___x_3023_; 
v_a_3021_ = lean_ctor_get(v_a_3017_, 0);
lean_inc(v_a_3021_);
lean_dec_ref_known(v_a_3017_, 1);
if (v_isShared_3020_ == 0)
{
lean_ctor_set(v___x_3019_, 0, v_a_3021_);
v___x_3023_ = v___x_3019_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_a_3021_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
else
{
lean_object* v_a_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; size_t v_sz_3028_; size_t v___x_3029_; lean_object* v___x_3030_; 
lean_del_object(v___x_3019_);
v_a_3025_ = lean_ctor_get(v_a_3017_, 0);
lean_inc(v_a_3025_);
lean_dec_ref_known(v_a_3017_, 1);
v___x_3026_ = lean_box(0);
v___x_3027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3027_, 0, v___x_3026_);
lean_ctor_set(v___x_3027_, 1, v_a_3025_);
v_sz_3028_ = lean_array_size(v_tail_3015_);
v___x_3029_ = ((size_t)0ULL);
v___x_3030_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__6_spec__9(v_tail_3015_, v_sz_3028_, v___x_3029_, v___x_3027_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3044_; 
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3033_ = v___x_3030_;
v_isShared_3034_ = v_isSharedCheck_3044_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_3030_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3044_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v_fst_3035_; 
v_fst_3035_ = lean_ctor_get(v_a_3031_, 0);
if (lean_obj_tag(v_fst_3035_) == 0)
{
lean_object* v_snd_3036_; lean_object* v___x_3038_; 
v_snd_3036_ = lean_ctor_get(v_a_3031_, 1);
lean_inc(v_snd_3036_);
lean_dec(v_a_3031_);
if (v_isShared_3034_ == 0)
{
lean_ctor_set(v___x_3033_, 0, v_snd_3036_);
v___x_3038_ = v___x_3033_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_snd_3036_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
return v___x_3038_;
}
}
else
{
lean_object* v_val_3040_; lean_object* v___x_3042_; 
lean_inc_ref(v_fst_3035_);
lean_dec(v_a_3031_);
v_val_3040_ = lean_ctor_get(v_fst_3035_, 0);
lean_inc(v_val_3040_);
lean_dec_ref_known(v_fst_3035_, 1);
if (v_isShared_3034_ == 0)
{
lean_ctor_set(v___x_3033_, 0, v_val_3040_);
v___x_3042_ = v___x_3033_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_val_3040_);
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
else
{
lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3052_; 
v_a_3045_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3047_ = v___x_3030_;
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v___x_3030_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3050_; 
if (v_isShared_3048_ == 0)
{
v___x_3050_ = v___x_3047_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_a_3045_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
}
}
}
else
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3061_; 
v_a_3054_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3056_ = v___x_3016_;
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_3016_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__6___boxed(lean_object* v_t_3062_, lean_object* v_init_3063_, lean_object* v___y_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l_Lean_PersistentArray_forIn___at___00main_spec__6(v_t_3062_, v_init_3063_);
lean_dec_ref(v_t_3062_);
return v_res_3065_;
}
}
static lean_object* _init_l_main___closed__3(void){
_start:
{
lean_object* v___x_3069_; 
v___x_3069_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(lean_box(0), lean_box(0), lean_box(0));
return v___x_3069_;
}
}
static lean_object* _init_l_main___closed__4(void){
_start:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3070_ = l_Lean_instInhabitedClassState_default;
v___x_3071_ = lean_box(0);
v___x_3072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3071_);
lean_ctor_set(v___x_3072_, 1, v___x_3070_);
return v___x_3072_;
}
}
static lean_object* _init_l_main___closed__5(void){
_start:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3073_ = l_Lean_Meta_Match_Extension_instInhabitedState;
v___x_3074_ = lean_box(0);
v___x_3075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3074_);
lean_ctor_set(v___x_3075_, 1, v___x_3073_);
return v___x_3075_;
}
}
static lean_object* _init_l_main___closed__6(void){
_start:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3076_ = ((lean_object*)(l_main___closed__2));
v___x_3077_ = ((lean_object*)(l_main___closed__1));
v___x_3078_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_3077_, v___x_3076_);
return v___x_3078_;
}
}
static lean_object* _init_l_main___closed__7(void){
_start:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3079_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_3080_ = lean_box(0);
v___x_3081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3080_);
lean_ctor_set(v___x_3081_, 1, v___x_3079_);
return v___x_3081_;
}
}
static lean_object* _init_l_main___closed__8(void){
_start:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3082_ = lean_obj_once(&l_main___closed__7, &l_main___closed__7_once, _init_l_main___closed__7);
v___x_3083_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_3082_);
return v___x_3083_;
}
}
static lean_object* _init_l_main___closed__9(void){
_start:
{
lean_object* v___x_3084_; 
v___x_3084_ = l_Array_instInhabited(lean_box(0));
return v___x_3084_;
}
}
static lean_object* _init_l_main___closed__15(void){
_start:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3093_ = l_Lean_Options_empty;
v___x_3094_ = l_Lean_Core_getMaxHeartbeats(v___x_3093_);
return v___x_3094_;
}
}
static lean_object* _init_l_main___closed__20(void){
_start:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3099_ = ((lean_object*)(l_main___closed__19));
v___x_3100_ = lean_unsigned_to_nat(27u);
v___x_3101_ = lean_unsigned_to_nat(149u);
v___x_3102_ = ((lean_object*)(l_main___closed__18));
v___x_3103_ = ((lean_object*)(l_main___closed__17));
v___x_3104_ = l_mkPanicMessageWithDecl(v___x_3103_, v___x_3102_, v___x_3101_, v___x_3100_, v___x_3099_);
return v___x_3104_;
}
}
static lean_object* _init_l_main___closed__22(void){
_start:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3106_ = ((lean_object*)(l_main___closed__19));
v___x_3107_ = lean_unsigned_to_nat(51u);
v___x_3108_ = lean_unsigned_to_nat(122u);
v___x_3109_ = ((lean_object*)(l_main___closed__18));
v___x_3110_ = ((lean_object*)(l_main___closed__17));
v___x_3111_ = l_mkPanicMessageWithDecl(v___x_3110_, v___x_3109_, v___x_3108_, v___x_3107_, v___x_3106_);
return v___x_3111_;
}
}
static lean_object* _init_l_main___closed__23(void){
_start:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3112_ = lean_unsigned_to_nat(1u);
v___x_3113_ = l_Lean_firstFrontendMacroScope;
v___x_3114_ = lean_nat_add(v___x_3113_, v___x_3112_);
return v___x_3114_;
}
}
static lean_object* _init_l_main___closed__27(void){
_start:
{
lean_object* v___x_3121_; uint64_t v___x_3122_; lean_object* v___x_3123_; 
v___x_3121_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___redArg___closed__1);
v___x_3122_ = 0ULL;
v___x_3123_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3123_, 0, v___x_3121_);
lean_ctor_set_uint64(v___x_3123_, sizeof(void*)*1, v___x_3122_);
return v___x_3123_;
}
}
static lean_object* _init_l_main___closed__28(void){
_start:
{
lean_object* v___x_3124_; 
v___x_3124_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3124_;
}
}
static lean_object* _init_l_main___closed__29(void){
_start:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3125_ = lean_obj_once(&l_main___closed__28, &l_main___closed__28_once, _init_l_main___closed__28);
v___x_3126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3125_);
return v___x_3126_;
}
}
static lean_object* _init_l_main___closed__30(void){
_start:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3127_ = lean_obj_once(&l_main___closed__29, &l_main___closed__29_once, _init_l_main___closed__29);
v___x_3128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3128_, 0, v___x_3127_);
lean_ctor_set(v___x_3128_, 1, v___x_3127_);
return v___x_3128_;
}
}
static lean_object* _init_l_main___closed__31(void){
_start:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3129_ = l_Lean_NameSet_empty;
v___x_3130_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___redArg___closed__1);
v___x_3131_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3130_);
lean_ctor_set(v___x_3131_, 1, v___x_3130_);
lean_ctor_set(v___x_3131_, 2, v___x_3129_);
return v___x_3131_;
}
}
static lean_object* _init_l_main___closed__32(void){
_start:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; uint8_t v___x_3134_; lean_object* v___x_3135_; 
v___x_3132_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___redArg___closed__1);
v___x_3133_ = lean_obj_once(&l_main___closed__29, &l_main___closed__29_once, _init_l_main___closed__29);
v___x_3134_ = 1;
v___x_3135_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3135_, 0, v___x_3133_);
lean_ctor_set(v___x_3135_, 1, v___x_3133_);
lean_ctor_set(v___x_3135_, 2, v___x_3132_);
lean_ctor_set_uint8(v___x_3135_, sizeof(void*)*3, v___x_3134_);
return v___x_3135_;
}
}
static uint8_t _init_l_main___closed__37(void){
_start:
{
uint8_t v___x_3142_; uint8_t v___x_3143_; uint8_t v___x_3144_; 
v___x_3142_ = 2;
v___x_3143_ = 0;
v___x_3144_ = l_Lean_instOrdOLeanLevel_ord(v___x_3143_, v___x_3142_);
return v___x_3144_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_3145_; lean_object* v___x_3146_; 
v___x_3145_ = 1;
v___x_3146_ = lean_box_uint32(v___x_3145_);
return v___x_3146_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_3147_; lean_object* v___x_3148_; 
v___x_3147_ = 0;
v___x_3148_ = lean_box_uint32(v___x_3147_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_3149_){
_start:
{
if (lean_obj_tag(v_args_3149_) == 1)
{
lean_object* v_tail_3174_; 
v_tail_3174_ = lean_ctor_get(v_args_3149_, 1);
lean_inc(v_tail_3174_);
if (lean_obj_tag(v_tail_3174_) == 1)
{
lean_object* v_tail_3175_; 
v_tail_3175_ = lean_ctor_get(v_tail_3174_, 1);
lean_inc(v_tail_3175_);
if (lean_obj_tag(v_tail_3175_) == 1)
{
lean_object* v_head_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3822_; 
v_head_3176_ = lean_ctor_get(v_args_3149_, 0);
v_isSharedCheck_3822_ = !lean_is_exclusive(v_args_3149_);
if (v_isSharedCheck_3822_ == 0)
{
lean_object* v_unused_3823_; 
v_unused_3823_ = lean_ctor_get(v_args_3149_, 1);
lean_dec(v_unused_3823_);
v___x_3178_ = v_args_3149_;
v_isShared_3179_ = v_isSharedCheck_3822_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_head_3176_);
lean_dec(v_args_3149_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3822_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v_head_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3820_; 
v_head_3180_ = lean_ctor_get(v_tail_3174_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v_tail_3174_);
if (v_isSharedCheck_3820_ == 0)
{
lean_object* v_unused_3821_; 
v_unused_3821_ = lean_ctor_get(v_tail_3174_, 1);
lean_dec(v_unused_3821_);
v___x_3182_ = v_tail_3174_;
v_isShared_3183_ = v_isSharedCheck_3820_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_head_3180_);
lean_dec(v_tail_3174_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3820_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v_head_3184_; lean_object* v_tail_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3819_; 
v_head_3184_ = lean_ctor_get(v_tail_3175_, 0);
v_tail_3185_ = lean_ctor_get(v_tail_3175_, 1);
v_isSharedCheck_3819_ = !lean_is_exclusive(v_tail_3175_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3187_ = v_tail_3175_;
v_isShared_3188_ = v_isSharedCheck_3819_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_tail_3185_);
lean_inc(v_head_3184_);
lean_dec(v_tail_3175_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3819_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v___x_3189_; 
v___x_3189_ = l_Lean_ModuleSetup_load(v_head_3176_);
lean_dec(v_head_3176_);
if (lean_obj_tag(v___x_3189_) == 0)
{
lean_object* v_a_3190_; lean_object* v_name_3191_; lean_object* v_importArts_3192_; lean_object* v_options_3193_; uint8_t v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3198_; 
v_a_3190_ = lean_ctor_get(v___x_3189_, 0);
lean_inc(v_a_3190_);
lean_dec_ref_known(v___x_3189_, 1);
v_name_3191_ = lean_ctor_get(v_a_3190_, 0);
lean_inc(v_name_3191_);
v_importArts_3192_ = lean_ctor_get(v_a_3190_, 3);
lean_inc(v_importArts_3192_);
v_options_3193_ = lean_ctor_get(v_a_3190_, 6);
lean_inc(v_options_3193_);
lean_dec(v_a_3190_);
v___x_3194_ = 0;
v___x_3195_ = l_Lean_LeanOptions_toOptions(v_options_3193_);
v___x_3196_ = lean_box(v___x_3194_);
if (v_isShared_3188_ == 0)
{
lean_ctor_set_tag(v___x_3187_, 0);
lean_ctor_set(v___x_3187_, 1, v___x_3195_);
lean_ctor_set(v___x_3187_, 0, v___x_3196_);
v___x_3198_ = v___x_3187_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v___x_3196_);
lean_ctor_set(v_reuseFailAlloc_3810_, 1, v___x_3195_);
v___x_3198_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
lean_object* v___x_3199_; 
v___x_3199_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_tail_3185_, v___x_3198_);
lean_dec(v_tail_3185_);
if (lean_obj_tag(v___x_3199_) == 0)
{
lean_object* v_a_3200_; lean_object* v___x_3201_; 
v_a_3200_ = lean_ctor_get(v___x_3199_, 0);
lean_inc(v_a_3200_);
lean_dec_ref_known(v___x_3199_, 1);
v___x_3201_ = lean_init_search_path();
if (lean_obj_tag(v___x_3201_) == 0)
{
lean_object* v_fst_3202_; lean_object* v_snd_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3793_; 
lean_dec_ref_known(v___x_3201_, 1);
v_fst_3202_ = lean_ctor_get(v_a_3200_, 0);
v_snd_3203_ = lean_ctor_get(v_a_3200_, 1);
v_isSharedCheck_3793_ = !lean_is_exclusive(v_a_3200_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3205_ = v_a_3200_;
v_isShared_3206_ = v_isSharedCheck_3793_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_snd_3203_);
lean_inc(v_fst_3202_);
lean_dec(v_a_3200_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3793_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; uint8_t v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; uint8_t v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; uint8_t v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v_nextMacroScope_3386_; lean_object* v_ngen_3387_; lean_object* v_auxDeclNGen_3388_; lean_object* v_traceState_3389_; lean_object* v_messages_3390_; lean_object* v_infoState_3391_; lean_object* v_snapshotTasks_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; uint8_t v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v___y_3426_; lean_object* v___y_3427_; lean_object* v___y_3428_; uint8_t v___y_3429_; lean_object* v___y_3430_; lean_object* v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v___y_3435_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; uint8_t v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; uint8_t v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; uint8_t v___y_3514_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; uint8_t v___x_3539_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3646_; lean_object* v___y_3647_; lean_object* v___y_3648_; lean_object* v___y_3649_; lean_object* v___y_3667_; lean_object* v___y_3668_; lean_object* v___y_3669_; lean_object* v___y_3670_; lean_object* v___y_3671_; lean_object* v___y_3672_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v___y_3684_; lean_object* v___y_3685_; lean_object* v___y_3686_; uint8_t v___x_3696_; uint8_t v___y_3698_; uint8_t v___x_3792_; 
v___x_3207_ = lean_obj_once(&l_main___closed__3, &l_main___closed__3_once, _init_l_main___closed__3);
v___x_3208_ = lean_box(0);
v___x_3209_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_3210_ = lean_obj_once(&l_main___closed__5, &l_main___closed__5_once, _init_l_main___closed__5);
v___x_3211_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_3212_ = lean_obj_once(&l_main___closed__8, &l_main___closed__8_once, _init_l_main___closed__8);
v___x_3213_ = lean_obj_once(&l_main___closed__9, &l_main___closed__9_once, _init_l_main___closed__9);
v___x_3214_ = lean_box(1);
v___x_3215_ = ((lean_object*)(l_main___closed__10));
v___x_3216_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_3217_ = 1;
v___x_3218_ = l_Lean_Option_set___at___00Lean_Environment_realizeConst_spec__0(v_snd_3203_, v___x_3216_, v___x_3217_);
v___x_3219_ = l_Lean_maxHeartbeats;
v___x_3220_ = lean_unsigned_to_nat(0u);
v___x_3221_ = l_Lean_Option_set___at___00main_spec__3(v___x_3218_, v___x_3219_, v___x_3220_);
v___x_3534_ = ((lean_object*)(l_main___closed__21));
lean_inc(v_name_3191_);
v___x_3535_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_3535_, 0, v_name_3191_);
lean_ctor_set_uint8(v___x_3535_, sizeof(void*)*1, v___x_3217_);
lean_ctor_set_uint8(v___x_3535_, sizeof(void*)*1 + 1, v___x_3217_);
lean_ctor_set_uint8(v___x_3535_, sizeof(void*)*1 + 2, v___x_3194_);
v___x_3536_ = lean_unsigned_to_nat(1u);
v___x_3537_ = lean_mk_empty_array_with_capacity(v___x_3536_);
v___x_3538_ = lean_array_push(v___x_3537_, v___x_3535_);
v___x_3539_ = 0;
v___x_3696_ = 2;
v___x_3792_ = lean_uint8_once(&l_main___closed__37, &l_main___closed__37_once, _init_l_main___closed__37);
if (v___x_3792_ == 0)
{
v___y_3698_ = v___x_3217_;
goto v___jp_3697_;
}
else
{
v___y_3698_ = v___x_3194_;
goto v___jp_3697_;
}
v___jp_3222_:
{
lean_object* v___x_3242_; lean_object* v_messages_3243_; lean_object* v_env_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3368_; 
v___x_3242_ = lean_st_ref_get(v___y_3235_);
lean_dec(v___y_3235_);
v_messages_3243_ = lean_ctor_get(v___x_3242_, 6);
v_env_3244_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3368_ == 0)
{
lean_object* v_unused_3369_; lean_object* v_unused_3370_; lean_object* v_unused_3371_; lean_object* v_unused_3372_; lean_object* v_unused_3373_; lean_object* v_unused_3374_; lean_object* v_unused_3375_; 
v_unused_3369_ = lean_ctor_get(v___x_3242_, 8);
lean_dec(v_unused_3369_);
v_unused_3370_ = lean_ctor_get(v___x_3242_, 7);
lean_dec(v_unused_3370_);
v_unused_3371_ = lean_ctor_get(v___x_3242_, 5);
lean_dec(v_unused_3371_);
v_unused_3372_ = lean_ctor_get(v___x_3242_, 4);
lean_dec(v_unused_3372_);
v_unused_3373_ = lean_ctor_get(v___x_3242_, 3);
lean_dec(v_unused_3373_);
v_unused_3374_ = lean_ctor_get(v___x_3242_, 2);
lean_dec(v_unused_3374_);
v_unused_3375_ = lean_ctor_get(v___x_3242_, 1);
lean_dec(v_unused_3375_);
v___x_3246_ = v___x_3242_;
v_isShared_3247_ = v_isSharedCheck_3368_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_messages_3243_);
lean_inc(v_env_3244_);
lean_dec(v___x_3242_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3368_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v_unreported_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; 
v_unreported_3248_ = lean_ctor_get(v_messages_3243_, 1);
v___x_3249_ = lean_box(0);
v___x_3250_ = l_Lean_PersistentArray_forIn___at___00main_spec__6(v_unreported_3248_, v___x_3249_);
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3358_; 
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3358_ == 0)
{
lean_object* v_unused_3359_; 
v_unused_3359_ = lean_ctor_get(v___x_3250_, 0);
lean_dec(v_unused_3359_);
v___x_3252_ = v___x_3250_;
v_isShared_3253_ = v_isSharedCheck_3358_;
goto v_resetjp_3251_;
}
else
{
lean_dec(v___x_3250_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3358_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
uint8_t v___x_3254_; 
v___x_3254_ = l_Lean_MessageLog_hasErrors(v_messages_3243_);
lean_dec_ref(v_messages_3243_);
if (v___x_3254_ == 0)
{
lean_object* v___x_3255_; 
lean_del_object(v___x_3252_);
lean_inc_ref(v_env_3244_);
v___x_3255_ = l___private_LeanIR_0__mkIRSigData(v_env_3244_);
if (lean_obj_tag(v___x_3255_) == 0)
{
lean_object* v_a_3256_; lean_object* v___x_3257_; 
v_a_3256_ = lean_ctor_get(v___x_3255_, 0);
lean_inc(v_a_3256_);
lean_dec_ref_known(v___x_3255_, 1);
lean_inc_ref(v_env_3244_);
v___x_3257_ = l___private_LeanIR_0__mkIRData(v_env_3244_);
if (lean_obj_tag(v___x_3257_) == 0)
{
lean_object* v_a_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3265_; 
v_a_3258_ = lean_ctor_get(v___x_3257_, 0);
lean_inc(v_a_3258_);
lean_dec_ref_known(v___x_3257_, 1);
v___x_3259_ = ((lean_object*)(l_main___closed__11));
lean_inc(v_head_3180_);
v___x_3260_ = l_System_FilePath_addExtension(v_head_3180_, v___x_3259_);
v___x_3261_ = l_Lean_Environment_mainModule(v_env_3244_);
v___x_3262_ = ((lean_object*)(l_main___closed__13));
v___x_3263_ = l_Lean_Name_append(v___x_3261_, v___x_3262_);
if (v_isShared_3206_ == 0)
{
lean_ctor_set(v___x_3205_, 1, v_a_3256_);
lean_ctor_set(v___x_3205_, 0, v___x_3260_);
v___x_3265_ = v___x_3205_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v___x_3260_);
lean_ctor_set(v_reuseFailAlloc_3337_, 1, v_a_3256_);
v___x_3265_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
lean_object* v___x_3267_; 
lean_inc(v_head_3180_);
if (v_isShared_3183_ == 0)
{
lean_ctor_set_tag(v___x_3182_, 0);
lean_ctor_set(v___x_3182_, 1, v_a_3258_);
v___x_3267_ = v___x_3182_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_head_3180_);
lean_ctor_set(v_reuseFailAlloc_3336_, 1, v_a_3258_);
v___x_3267_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3268_ = lean_unsigned_to_nat(2u);
v___x_3269_ = lean_mk_empty_array_with_capacity(v___x_3268_);
v___x_3270_ = lean_array_push(v___x_3269_, v___x_3265_);
v___x_3271_ = lean_array_push(v___x_3270_, v___x_3267_);
v___x_3272_ = l_Lean_saveModuleDataParts(v___x_3263_, v___x_3271_);
lean_dec_ref(v___x_3271_);
lean_dec(v___x_3263_);
if (lean_obj_tag(v___x_3272_) == 0)
{
uint8_t v___x_3273_; lean_object* v___x_3274_; 
lean_dec_ref_known(v___x_3272_, 1);
v___x_3273_ = 1;
v___x_3274_ = lean_io_prim_handle_mk(v_head_3184_, v___x_3273_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3280_; 
lean_dec(v_head_3184_);
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_a_3275_);
lean_dec_ref_known(v___x_3274_, 1);
v___x_3276_ = ((lean_object*)(l_main___closed__14));
v___x_3277_ = l_Lean_Options_empty;
v___x_3278_ = lean_obj_once(&l_main___closed__15, &l_main___closed__15_once, _init_l_main___closed__15);
lean_inc_ref(v___y_3240_);
lean_inc_ref(v___y_3239_);
lean_inc_ref(v___y_3236_);
lean_inc_ref(v___y_3237_);
lean_inc_ref(v___y_3238_);
lean_inc_ref(v___y_3232_);
lean_inc(v___y_3233_);
lean_inc_ref(v_env_3244_);
if (v_isShared_3247_ == 0)
{
lean_ctor_set(v___x_3246_, 8, v___y_3240_);
lean_ctor_set(v___x_3246_, 7, v___y_3239_);
lean_ctor_set(v___x_3246_, 6, v___y_3236_);
lean_ctor_set(v___x_3246_, 5, v___y_3237_);
lean_ctor_set(v___x_3246_, 4, v___y_3238_);
lean_ctor_set(v___x_3246_, 3, v___y_3241_);
lean_ctor_set(v___x_3246_, 2, v___y_3232_);
lean_ctor_set(v___x_3246_, 1, v___y_3233_);
v___x_3280_ = v___x_3246_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_env_3244_);
lean_ctor_set(v_reuseFailAlloc_3305_, 1, v___y_3233_);
lean_ctor_set(v_reuseFailAlloc_3305_, 2, v___y_3232_);
lean_ctor_set(v_reuseFailAlloc_3305_, 3, v___y_3241_);
lean_ctor_set(v_reuseFailAlloc_3305_, 4, v___y_3238_);
lean_ctor_set(v_reuseFailAlloc_3305_, 5, v___y_3237_);
lean_ctor_set(v_reuseFailAlloc_3305_, 6, v___y_3236_);
lean_ctor_set(v_reuseFailAlloc_3305_, 7, v___y_3239_);
lean_ctor_set(v_reuseFailAlloc_3305_, 8, v___y_3240_);
v___x_3280_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___f_3284_; lean_object* v___x_3285_; 
v___x_3281_ = lean_box(v___x_3217_);
v___x_3282_ = lean_box(v___x_3194_);
v___x_3283_ = lean_box(v___y_3223_);
lean_inc(v___y_3229_);
lean_inc(v___y_3225_);
lean_inc(v___y_3231_);
lean_inc(v___y_3226_);
lean_inc_ref(v___y_3228_);
lean_inc_ref(v___y_3227_);
lean_inc(v___y_3230_);
v___f_3284_ = lean_alloc_closure((void*)(l_main___lam__1___boxed), 19, 18);
lean_closure_set(v___f_3284_, 0, v___x_3280_);
lean_closure_set(v___f_3284_, 1, v___y_3230_);
lean_closure_set(v___f_3284_, 2, v___x_3277_);
lean_closure_set(v___f_3284_, 3, v_name_3191_);
lean_closure_set(v___f_3284_, 4, v_a_3275_);
lean_closure_set(v___f_3284_, 5, v___x_3281_);
lean_closure_set(v___f_3284_, 6, v___y_3227_);
lean_closure_set(v___f_3284_, 7, v_head_3180_);
lean_closure_set(v___f_3284_, 8, v___y_3228_);
lean_closure_set(v___f_3284_, 9, v___x_3220_);
lean_closure_set(v___f_3284_, 10, v___y_3226_);
lean_closure_set(v___f_3284_, 11, v___y_3224_);
lean_closure_set(v___f_3284_, 12, v___y_3231_);
lean_closure_set(v___f_3284_, 13, v___x_3278_);
lean_closure_set(v___f_3284_, 14, v___y_3225_);
lean_closure_set(v___f_3284_, 15, v___y_3229_);
lean_closure_set(v___f_3284_, 16, v___x_3282_);
lean_closure_set(v___f_3284_, 17, v___x_3283_);
v___x_3285_ = l_Lean_profileitIOUnsafe___redArg(v___x_3276_, v___x_3221_, v___f_3284_, v___y_3234_);
lean_dec_ref(v___x_3221_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v___x_3286_; uint8_t v___x_3287_; 
lean_dec_ref_known(v___x_3285_, 1);
v___x_3286_ = lean_display_cumulative_profiling_times();
v___x_3287_ = lean_unbox(v_fst_3202_);
lean_dec(v_fst_3202_);
if (v___x_3287_ == 0)
{
lean_dec_ref(v_env_3244_);
goto v___jp_3171_;
}
else
{
lean_object* v___x_3288_; 
v___x_3288_ = l_Lean_Environment_displayStats(v_env_3244_);
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_dec_ref_known(v___x_3288_, 1);
goto v___jp_3171_;
}
else
{
lean_object* v_a_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3296_; 
v_a_3289_ = lean_ctor_get(v___x_3288_, 0);
v_isSharedCheck_3296_ = !lean_is_exclusive(v___x_3288_);
if (v_isSharedCheck_3296_ == 0)
{
v___x_3291_ = v___x_3288_;
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_a_3289_);
lean_dec(v___x_3288_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3294_; 
if (v_isShared_3292_ == 0)
{
v___x_3294_ = v___x_3291_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3289_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
return v___x_3294_;
}
}
}
}
}
else
{
lean_object* v_a_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3304_; 
lean_dec_ref(v_env_3244_);
lean_dec(v_fst_3202_);
v_a_3297_ = lean_ctor_get(v___x_3285_, 0);
v_isSharedCheck_3304_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3304_ == 0)
{
v___x_3299_ = v___x_3285_;
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_a_3297_);
lean_dec(v___x_3285_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v___x_3302_; 
if (v_isShared_3300_ == 0)
{
v___x_3302_ = v___x_3299_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_a_3297_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
}
}
else
{
lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
lean_dec_ref_known(v___x_3274_, 1);
lean_del_object(v___x_3246_);
lean_dec_ref(v_env_3244_);
lean_dec_ref(v___y_3241_);
lean_dec(v___y_3234_);
lean_dec(v___y_3224_);
lean_dec_ref(v___x_3221_);
lean_dec(v_fst_3202_);
lean_dec(v_name_3191_);
lean_dec(v_head_3180_);
v___x_3306_ = ((lean_object*)(l_main___closed__16));
v___x_3307_ = lean_string_append(v___x_3306_, v_head_3184_);
lean_dec(v_head_3184_);
v___x_3308_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__1));
v___x_3309_ = lean_string_append(v___x_3307_, v___x_3308_);
v___x_3310_ = l_IO_eprintln___at___00main_spec__5(v___x_3309_);
if (lean_obj_tag(v___x_3310_) == 0)
{
lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3318_; 
v_isSharedCheck_3318_ = !lean_is_exclusive(v___x_3310_);
if (v_isSharedCheck_3318_ == 0)
{
lean_object* v_unused_3319_; 
v_unused_3319_ = lean_ctor_get(v___x_3310_, 0);
lean_dec(v_unused_3319_);
v___x_3312_ = v___x_3310_;
v_isShared_3313_ = v_isSharedCheck_3318_;
goto v_resetjp_3311_;
}
else
{
lean_dec(v___x_3310_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3318_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v___x_3314_; lean_object* v___x_3316_; 
v___x_3314_ = l_main___boxed__const__1;
if (v_isShared_3313_ == 0)
{
lean_ctor_set(v___x_3312_, 0, v___x_3314_);
v___x_3316_ = v___x_3312_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v___x_3314_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
}
else
{
lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3327_; 
v_a_3320_ = lean_ctor_get(v___x_3310_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3310_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3322_ = v___x_3310_;
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_dec(v___x_3310_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3325_; 
if (v_isShared_3323_ == 0)
{
v___x_3325_ = v___x_3322_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_a_3320_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
return v___x_3325_;
}
}
}
}
}
else
{
lean_object* v_a_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3335_; 
lean_del_object(v___x_3246_);
lean_dec_ref(v_env_3244_);
lean_dec_ref(v___y_3241_);
lean_dec(v___y_3234_);
lean_dec(v___y_3224_);
lean_dec_ref(v___x_3221_);
lean_dec(v_fst_3202_);
lean_dec(v_name_3191_);
lean_dec(v_head_3184_);
lean_dec(v_head_3180_);
v_a_3328_ = lean_ctor_get(v___x_3272_, 0);
v_isSharedCheck_3335_ = !lean_is_exclusive(v___x_3272_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3330_ = v___x_3272_;
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_a_3328_);
lean_dec(v___x_3272_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___x_3333_; 
if (v_isShared_3331_ == 0)
{
v___x_3333_ = v___x_3330_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v_a_3328_);
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
}
}
else
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3345_; 
lean_dec(v_a_3256_);
lean_del_object(v___x_3246_);
lean_dec_ref(v_env_3244_);
lean_dec_ref(v___y_3241_);
lean_dec(v___y_3234_);
lean_dec(v___y_3224_);
lean_dec_ref(v___x_3221_);
lean_del_object(v___x_3205_);
lean_dec(v_fst_3202_);
lean_dec(v_name_3191_);
lean_dec(v_head_3184_);
lean_del_object(v___x_3182_);
lean_dec(v_head_3180_);
v_a_3338_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3340_ = v___x_3257_;
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3257_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3343_; 
if (v_isShared_3341_ == 0)
{
v___x_3343_ = v___x_3340_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_a_3338_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
}
}
else
{
lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3353_; 
lean_del_object(v___x_3246_);
lean_dec_ref(v_env_3244_);
lean_dec_ref(v___y_3241_);
lean_dec(v___y_3234_);
lean_dec(v___y_3224_);
lean_dec_ref(v___x_3221_);
lean_del_object(v___x_3205_);
lean_dec(v_fst_3202_);
lean_dec(v_name_3191_);
lean_dec(v_head_3184_);
lean_del_object(v___x_3182_);
lean_dec(v_head_3180_);
v_a_3346_ = lean_ctor_get(v___x_3255_, 0);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3255_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3348_ = v___x_3255_;
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3255_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3351_; 
if (v_isShared_3349_ == 0)
{
v___x_3351_ = v___x_3348_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_a_3346_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
}
}
else
{
lean_object* v___x_3354_; lean_object* v___x_3356_; 
lean_del_object(v___x_3246_);
lean_dec_ref(v_env_3244_);
lean_dec_ref(v___y_3241_);
lean_dec(v___y_3234_);
lean_dec(v___y_3224_);
lean_dec_ref(v___x_3221_);
lean_del_object(v___x_3205_);
lean_dec(v_fst_3202_);
lean_dec(v_name_3191_);
lean_dec(v_head_3184_);
lean_del_object(v___x_3182_);
lean_dec(v_head_3180_);
v___x_3354_ = l_main___boxed__const__1;
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 0, v___x_3354_);
v___x_3356_ = v___x_3252_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v___x_3354_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
}
}
else
{
lean_object* v_a_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3367_; 
lean_del_object(v___x_3246_);
lean_dec_ref(v_env_3244_);
lean_dec_ref(v_messages_3243_);
lean_dec_ref(v___y_3241_);
lean_dec(v___y_3234_);
lean_dec(v___y_3224_);
lean_dec_ref(v___x_3221_);
lean_del_object(v___x_3205_);
lean_dec(v_fst_3202_);
lean_dec(v_name_3191_);
lean_dec(v_head_3184_);
lean_del_object(v___x_3182_);
lean_dec(v_head_3180_);
v_a_3360_ = lean_ctor_get(v___x_3250_, 0);
v_isSharedCheck_3367_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3367_ == 0)
{
v___x_3362_ = v___x_3250_;
v_isShared_3363_ = v_isSharedCheck_3367_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_a_3360_);
lean_dec(v___x_3250_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3367_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
lean_object* v___x_3365_; 
if (v_isShared_3363_ == 0)
{
v___x_3365_ = v___x_3362_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v_a_3360_);
v___x_3365_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
return v___x_3365_;
}
}
}
}
}
v___jp_3376_:
{
lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; size_t v_sz_3410_; size_t v___x_3411_; lean_object* v___x_3412_; 
lean_inc_ref(v___y_3402_);
v___x_3407_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3407_, 0, v___y_3406_);
lean_ctor_set(v___x_3407_, 1, v_nextMacroScope_3386_);
lean_ctor_set(v___x_3407_, 2, v_ngen_3387_);
lean_ctor_set(v___x_3407_, 3, v_auxDeclNGen_3388_);
lean_ctor_set(v___x_3407_, 4, v_traceState_3389_);
lean_ctor_set(v___x_3407_, 5, v___y_3402_);
lean_ctor_set(v___x_3407_, 6, v_messages_3390_);
lean_ctor_set(v___x_3407_, 7, v_infoState_3391_);
lean_ctor_set(v___x_3407_, 8, v_snapshotTasks_3392_);
v___x_3408_ = lean_st_ref_put(v___y_3394_, v___x_3407_);
v___x_3409_ = lean_box(0);
v_sz_3410_ = lean_array_size(v___y_3396_);
v___x_3411_ = ((size_t)0ULL);
v___x_3412_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(v___y_3396_, v_sz_3410_, v___x_3411_, v___x_3409_, v___y_3397_, v___y_3394_);
lean_dec_ref(v___y_3396_);
if (lean_obj_tag(v___x_3412_) == 0)
{
lean_dec_ref_known(v___x_3412_, 1);
lean_dec_ref(v___y_3397_);
lean_dec(v___y_3394_);
v___y_3223_ = v___y_3377_;
v___y_3224_ = v___y_3378_;
v___y_3225_ = v___y_3379_;
v___y_3226_ = v___y_3380_;
v___y_3227_ = v___y_3381_;
v___y_3228_ = v___y_3382_;
v___y_3229_ = v___y_3383_;
v___y_3230_ = v___y_3384_;
v___y_3231_ = v___y_3385_;
v___y_3232_ = v___y_3399_;
v___y_3233_ = v___y_3393_;
v___y_3234_ = v___y_3400_;
v___y_3235_ = v___y_3395_;
v___y_3236_ = v___y_3401_;
v___y_3237_ = v___y_3402_;
v___y_3238_ = v___y_3403_;
v___y_3239_ = v___y_3404_;
v___y_3240_ = v___y_3405_;
v___y_3241_ = v___y_3398_;
goto v___jp_3222_;
}
else
{
if (lean_obj_tag(v___x_3412_) == 0)
{
lean_dec_ref_known(v___x_3412_, 1);
lean_dec_ref(v___y_3397_);
lean_dec(v___y_3394_);
v___y_3223_ = v___y_3377_;
v___y_3224_ = v___y_3378_;
v___y_3225_ = v___y_3379_;
v___y_3226_ = v___y_3380_;
v___y_3227_ = v___y_3381_;
v___y_3228_ = v___y_3382_;
v___y_3229_ = v___y_3383_;
v___y_3230_ = v___y_3384_;
v___y_3231_ = v___y_3385_;
v___y_3232_ = v___y_3399_;
v___y_3233_ = v___y_3393_;
v___y_3234_ = v___y_3400_;
v___y_3235_ = v___y_3395_;
v___y_3236_ = v___y_3401_;
v___y_3237_ = v___y_3402_;
v___y_3238_ = v___y_3403_;
v___y_3239_ = v___y_3404_;
v___y_3240_ = v___y_3405_;
v___y_3241_ = v___y_3398_;
goto v___jp_3222_;
}
else
{
lean_object* v_a_3413_; uint8_t v___x_3414_; 
v_a_3413_ = lean_ctor_get(v___x_3412_, 0);
lean_inc(v_a_3413_);
lean_dec_ref_known(v___x_3412_, 1);
v___x_3414_ = l_Lean_Exception_isInterrupt(v_a_3413_);
if (v___x_3414_ == 0)
{
lean_object* v___x_3415_; lean_object* v___x_3416_; 
v___x_3415_ = l_Lean_Exception_toMessageData(v_a_3413_);
v___x_3416_ = l_Lean_logError___at___00main_spec__13(v___x_3415_, v___y_3397_, v___y_3394_);
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3397_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_dec_ref_known(v___x_3416_, 1);
v___y_3223_ = v___y_3377_;
v___y_3224_ = v___y_3378_;
v___y_3225_ = v___y_3379_;
v___y_3226_ = v___y_3380_;
v___y_3227_ = v___y_3381_;
v___y_3228_ = v___y_3382_;
v___y_3229_ = v___y_3383_;
v___y_3230_ = v___y_3384_;
v___y_3231_ = v___y_3385_;
v___y_3232_ = v___y_3399_;
v___y_3233_ = v___y_3393_;
v___y_3234_ = v___y_3400_;
v___y_3235_ = v___y_3395_;
v___y_3236_ = v___y_3401_;
v___y_3237_ = v___y_3402_;
v___y_3238_ = v___y_3403_;
v___y_3239_ = v___y_3404_;
v___y_3240_ = v___y_3405_;
v___y_3241_ = v___y_3398_;
goto v___jp_3222_;
}
else
{
lean_object* v___x_3417_; lean_object* v___x_3418_; 
lean_dec_ref_known(v___x_3416_, 1);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3398_);
lean_dec(v___y_3395_);
lean_dec(v___y_3378_);
lean_dec_ref(v___x_3221_);
lean_del_object(v___x_3205_);
lean_dec(v_fst_3202_);
lean_dec(v_name_3191_);
lean_dec(v_head_3184_);
lean_del_object(v___x_3182_);
lean_dec(v_head_3180_);
v___x_3417_ = lean_obj_once(&l_main___closed__20, &l_main___closed__20_once, _init_l_main___closed__20);
v___x_3418_ = l_panic___at___00main_spec__4(v___x_3417_);
return v___x_3418_;
}
}
else
{
lean_dec(v_a_3413_);
lean_dec_ref(v___y_3397_);
lean_dec(v___y_3394_);
v___y_3223_ = v___y_3377_;
v___y_3224_ = v___y_3378_;
v___y_3225_ = v___y_3379_;
v___y_3226_ = v___y_3380_;
v___y_3227_ = v___y_3381_;
v___y_3228_ = v___y_3382_;
v___y_3229_ = v___y_3383_;
v___y_3230_ = v___y_3384_;
v___y_3231_ = v___y_3385_;
v___y_3232_ = v___y_3399_;
v___y_3233_ = v___y_3393_;
v___y_3234_ = v___y_3400_;
v___y_3235_ = v___y_3395_;
v___y_3236_ = v___y_3401_;
v___y_3237_ = v___y_3402_;
v___y_3238_ = v___y_3403_;
v___y_3239_ = v___y_3404_;
v___y_3240_ = v___y_3405_;
v___y_3241_ = v___y_3398_;
goto v___jp_3222_;
}
}
}
}
v___jp_3419_:
{
lean_object* v___x_3444_; lean_object* v_fileName_3445_; lean_object* v_fileMap_3446_; lean_object* v_currRecDepth_3447_; lean_object* v_ref_3448_; lean_object* v_currNamespace_3449_; lean_object* v_openDecls_3450_; lean_object* v_initHeartbeats_3451_; lean_object* v_maxHeartbeats_3452_; lean_object* v_quotContext_3453_; lean_object* v_currMacroScope_3454_; lean_object* v_cancelTk_x3f_3455_; uint8_t v_suppressElabErrors_3456_; lean_object* v_inheritedTraceOptions_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3487_; 
v___x_3444_ = lean_st_ref_take(v___y_3443_);
v_fileName_3445_ = lean_ctor_get(v___y_3442_, 0);
v_fileMap_3446_ = lean_ctor_get(v___y_3442_, 1);
v_currRecDepth_3447_ = lean_ctor_get(v___y_3442_, 3);
v_ref_3448_ = lean_ctor_get(v___y_3442_, 5);
v_currNamespace_3449_ = lean_ctor_get(v___y_3442_, 6);
v_openDecls_3450_ = lean_ctor_get(v___y_3442_, 7);
v_initHeartbeats_3451_ = lean_ctor_get(v___y_3442_, 8);
v_maxHeartbeats_3452_ = lean_ctor_get(v___y_3442_, 9);
v_quotContext_3453_ = lean_ctor_get(v___y_3442_, 10);
v_currMacroScope_3454_ = lean_ctor_get(v___y_3442_, 11);
v_cancelTk_x3f_3455_ = lean_ctor_get(v___y_3442_, 12);
v_suppressElabErrors_3456_ = lean_ctor_get_uint8(v___y_3442_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3457_ = lean_ctor_get(v___y_3442_, 13);
v_isSharedCheck_3487_ = !lean_is_exclusive(v___y_3442_);
if (v_isSharedCheck_3487_ == 0)
{
lean_object* v_unused_3488_; lean_object* v_unused_3489_; 
v_unused_3488_ = lean_ctor_get(v___y_3442_, 4);
lean_dec(v_unused_3488_);
v_unused_3489_ = lean_ctor_get(v___y_3442_, 2);
lean_dec(v_unused_3489_);
v___x_3459_ = v___y_3442_;
v_isShared_3460_ = v_isSharedCheck_3487_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_inheritedTraceOptions_3457_);
lean_inc(v_cancelTk_x3f_3455_);
lean_inc(v_currMacroScope_3454_);
lean_inc(v_quotContext_3453_);
lean_inc(v_maxHeartbeats_3452_);
lean_inc(v_initHeartbeats_3451_);
lean_inc(v_openDecls_3450_);
lean_inc(v_currNamespace_3449_);
lean_inc(v_ref_3448_);
lean_inc(v_currRecDepth_3447_);
lean_inc(v_fileMap_3446_);
lean_inc(v_fileName_3445_);
lean_dec(v___y_3442_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3487_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v_env_3461_; lean_object* v_nextMacroScope_3462_; lean_object* v_ngen_3463_; lean_object* v_auxDeclNGen_3464_; lean_object* v_traceState_3465_; lean_object* v_messages_3466_; lean_object* v_infoState_3467_; lean_object* v_snapshotTasks_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3472_; 
v_env_3461_ = lean_ctor_get(v___x_3444_, 0);
lean_inc_ref(v_env_3461_);
v_nextMacroScope_3462_ = lean_ctor_get(v___x_3444_, 1);
lean_inc(v_nextMacroScope_3462_);
v_ngen_3463_ = lean_ctor_get(v___x_3444_, 2);
lean_inc_ref(v_ngen_3463_);
v_auxDeclNGen_3464_ = lean_ctor_get(v___x_3444_, 3);
lean_inc_ref(v_auxDeclNGen_3464_);
v_traceState_3465_ = lean_ctor_get(v___x_3444_, 4);
lean_inc_ref(v_traceState_3465_);
v_messages_3466_ = lean_ctor_get(v___x_3444_, 6);
lean_inc_ref(v_messages_3466_);
v_infoState_3467_ = lean_ctor_get(v___x_3444_, 7);
lean_inc_ref(v_infoState_3467_);
v_snapshotTasks_3468_ = lean_ctor_get(v___x_3444_, 8);
lean_inc_ref(v_snapshotTasks_3468_);
lean_dec(v___x_3444_);
v___x_3469_ = l_Lean_maxRecDepth;
v___x_3470_ = l_Lean_Option_get___at___00main_spec__8(v___x_3221_, v___x_3469_);
lean_inc_ref(v___x_3221_);
if (v_isShared_3460_ == 0)
{
lean_ctor_set(v___x_3459_, 4, v___x_3470_);
lean_ctor_set(v___x_3459_, 2, v___x_3221_);
v___x_3472_ = v___x_3459_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_fileName_3445_);
lean_ctor_set(v_reuseFailAlloc_3486_, 1, v_fileMap_3446_);
lean_ctor_set(v_reuseFailAlloc_3486_, 2, v___x_3221_);
lean_ctor_set(v_reuseFailAlloc_3486_, 3, v_currRecDepth_3447_);
lean_ctor_set(v_reuseFailAlloc_3486_, 4, v___x_3470_);
lean_ctor_set(v_reuseFailAlloc_3486_, 5, v_ref_3448_);
lean_ctor_set(v_reuseFailAlloc_3486_, 6, v_currNamespace_3449_);
lean_ctor_set(v_reuseFailAlloc_3486_, 7, v_openDecls_3450_);
lean_ctor_set(v_reuseFailAlloc_3486_, 8, v_initHeartbeats_3451_);
lean_ctor_set(v_reuseFailAlloc_3486_, 9, v_maxHeartbeats_3452_);
lean_ctor_set(v_reuseFailAlloc_3486_, 10, v_quotContext_3453_);
lean_ctor_set(v_reuseFailAlloc_3486_, 11, v_currMacroScope_3454_);
lean_ctor_set(v_reuseFailAlloc_3486_, 12, v_cancelTk_x3f_3455_);
lean_ctor_set(v_reuseFailAlloc_3486_, 13, v_inheritedTraceOptions_3457_);
lean_ctor_set_uint8(v_reuseFailAlloc_3486_, sizeof(void*)*14 + 1, v_suppressElabErrors_3456_);
v___x_3472_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
lean_object* v___x_3473_; uint8_t v___x_3474_; 
lean_ctor_set_uint8(v___x_3472_, sizeof(void*)*14, v___y_3429_);
v___x_3473_ = lean_array_get_size(v___y_3433_);
v___x_3474_ = lean_nat_dec_lt(v___x_3220_, v___x_3473_);
if (v___x_3474_ == 0)
{
lean_object* v___x_3475_; 
lean_inc_ref(v___y_3432_);
v___x_3475_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3432_, v_env_3461_, v___x_3214_);
v___y_3377_ = v___y_3420_;
v___y_3378_ = v___y_3421_;
v___y_3379_ = v___y_3422_;
v___y_3380_ = v___y_3423_;
v___y_3381_ = v___y_3424_;
v___y_3382_ = v___y_3425_;
v___y_3383_ = v___y_3426_;
v___y_3384_ = v___y_3427_;
v___y_3385_ = v___y_3428_;
v_nextMacroScope_3386_ = v_nextMacroScope_3462_;
v_ngen_3387_ = v_ngen_3463_;
v_auxDeclNGen_3388_ = v_auxDeclNGen_3464_;
v_traceState_3389_ = v_traceState_3465_;
v_messages_3390_ = v_messages_3466_;
v_infoState_3391_ = v_infoState_3467_;
v_snapshotTasks_3392_ = v_snapshotTasks_3468_;
v___y_3393_ = v___y_3430_;
v___y_3394_ = v___y_3443_;
v___y_3395_ = v___y_3431_;
v___y_3396_ = v___y_3433_;
v___y_3397_ = v___x_3472_;
v___y_3398_ = v___y_3434_;
v___y_3399_ = v___y_3435_;
v___y_3400_ = v___y_3436_;
v___y_3401_ = v___y_3437_;
v___y_3402_ = v___y_3438_;
v___y_3403_ = v___y_3439_;
v___y_3404_ = v___y_3440_;
v___y_3405_ = v___y_3441_;
v___y_3406_ = v___x_3475_;
goto v___jp_3376_;
}
else
{
uint8_t v___x_3476_; 
v___x_3476_ = lean_nat_dec_le(v___x_3473_, v___x_3473_);
if (v___x_3476_ == 0)
{
if (v___x_3474_ == 0)
{
lean_object* v___x_3477_; 
lean_inc_ref(v___y_3432_);
v___x_3477_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3432_, v_env_3461_, v___x_3214_);
v___y_3377_ = v___y_3420_;
v___y_3378_ = v___y_3421_;
v___y_3379_ = v___y_3422_;
v___y_3380_ = v___y_3423_;
v___y_3381_ = v___y_3424_;
v___y_3382_ = v___y_3425_;
v___y_3383_ = v___y_3426_;
v___y_3384_ = v___y_3427_;
v___y_3385_ = v___y_3428_;
v_nextMacroScope_3386_ = v_nextMacroScope_3462_;
v_ngen_3387_ = v_ngen_3463_;
v_auxDeclNGen_3388_ = v_auxDeclNGen_3464_;
v_traceState_3389_ = v_traceState_3465_;
v_messages_3390_ = v_messages_3466_;
v_infoState_3391_ = v_infoState_3467_;
v_snapshotTasks_3392_ = v_snapshotTasks_3468_;
v___y_3393_ = v___y_3430_;
v___y_3394_ = v___y_3443_;
v___y_3395_ = v___y_3431_;
v___y_3396_ = v___y_3433_;
v___y_3397_ = v___x_3472_;
v___y_3398_ = v___y_3434_;
v___y_3399_ = v___y_3435_;
v___y_3400_ = v___y_3436_;
v___y_3401_ = v___y_3437_;
v___y_3402_ = v___y_3438_;
v___y_3403_ = v___y_3439_;
v___y_3404_ = v___y_3440_;
v___y_3405_ = v___y_3441_;
v___y_3406_ = v___x_3477_;
goto v___jp_3376_;
}
else
{
size_t v___x_3478_; size_t v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; 
v___x_3478_ = ((size_t)0ULL);
v___x_3479_ = lean_usize_of_nat(v___x_3473_);
v___x_3480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(v___y_3433_, v___x_3478_, v___x_3479_, v___x_3214_);
lean_inc_ref(v___y_3432_);
v___x_3481_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3432_, v_env_3461_, v___x_3480_);
v___y_3377_ = v___y_3420_;
v___y_3378_ = v___y_3421_;
v___y_3379_ = v___y_3422_;
v___y_3380_ = v___y_3423_;
v___y_3381_ = v___y_3424_;
v___y_3382_ = v___y_3425_;
v___y_3383_ = v___y_3426_;
v___y_3384_ = v___y_3427_;
v___y_3385_ = v___y_3428_;
v_nextMacroScope_3386_ = v_nextMacroScope_3462_;
v_ngen_3387_ = v_ngen_3463_;
v_auxDeclNGen_3388_ = v_auxDeclNGen_3464_;
v_traceState_3389_ = v_traceState_3465_;
v_messages_3390_ = v_messages_3466_;
v_infoState_3391_ = v_infoState_3467_;
v_snapshotTasks_3392_ = v_snapshotTasks_3468_;
v___y_3393_ = v___y_3430_;
v___y_3394_ = v___y_3443_;
v___y_3395_ = v___y_3431_;
v___y_3396_ = v___y_3433_;
v___y_3397_ = v___x_3472_;
v___y_3398_ = v___y_3434_;
v___y_3399_ = v___y_3435_;
v___y_3400_ = v___y_3436_;
v___y_3401_ = v___y_3437_;
v___y_3402_ = v___y_3438_;
v___y_3403_ = v___y_3439_;
v___y_3404_ = v___y_3440_;
v___y_3405_ = v___y_3441_;
v___y_3406_ = v___x_3481_;
goto v___jp_3376_;
}
}
else
{
size_t v___x_3482_; size_t v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3482_ = ((size_t)0ULL);
v___x_3483_ = lean_usize_of_nat(v___x_3473_);
v___x_3484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(v___y_3433_, v___x_3482_, v___x_3483_, v___x_3214_);
lean_inc_ref(v___y_3432_);
v___x_3485_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3432_, v_env_3461_, v___x_3484_);
v___y_3377_ = v___y_3420_;
v___y_3378_ = v___y_3421_;
v___y_3379_ = v___y_3422_;
v___y_3380_ = v___y_3423_;
v___y_3381_ = v___y_3424_;
v___y_3382_ = v___y_3425_;
v___y_3383_ = v___y_3426_;
v___y_3384_ = v___y_3427_;
v___y_3385_ = v___y_3428_;
v_nextMacroScope_3386_ = v_nextMacroScope_3462_;
v_ngen_3387_ = v_ngen_3463_;
v_auxDeclNGen_3388_ = v_auxDeclNGen_3464_;
v_traceState_3389_ = v_traceState_3465_;
v_messages_3390_ = v_messages_3466_;
v_infoState_3391_ = v_infoState_3467_;
v_snapshotTasks_3392_ = v_snapshotTasks_3468_;
v___y_3393_ = v___y_3430_;
v___y_3394_ = v___y_3443_;
v___y_3395_ = v___y_3431_;
v___y_3396_ = v___y_3433_;
v___y_3397_ = v___x_3472_;
v___y_3398_ = v___y_3434_;
v___y_3399_ = v___y_3435_;
v___y_3400_ = v___y_3436_;
v___y_3401_ = v___y_3437_;
v___y_3402_ = v___y_3438_;
v___y_3403_ = v___y_3439_;
v___y_3404_ = v___y_3440_;
v___y_3405_ = v___y_3441_;
v___y_3406_ = v___x_3485_;
goto v___jp_3376_;
}
}
}
}
}
v___jp_3490_:
{
if (v___y_3514_ == 0)
{
lean_object* v___x_3515_; lean_object* v_env_3516_; lean_object* v_nextMacroScope_3517_; lean_object* v_ngen_3518_; lean_object* v_auxDeclNGen_3519_; lean_object* v_traceState_3520_; lean_object* v_messages_3521_; lean_object* v_infoState_3522_; lean_object* v_snapshotTasks_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3532_; 
v___x_3515_ = lean_st_ref_take(v___y_3502_);
v_env_3516_ = lean_ctor_get(v___x_3515_, 0);
v_nextMacroScope_3517_ = lean_ctor_get(v___x_3515_, 1);
v_ngen_3518_ = lean_ctor_get(v___x_3515_, 2);
v_auxDeclNGen_3519_ = lean_ctor_get(v___x_3515_, 3);
v_traceState_3520_ = lean_ctor_get(v___x_3515_, 4);
v_messages_3521_ = lean_ctor_get(v___x_3515_, 6);
v_infoState_3522_ = lean_ctor_get(v___x_3515_, 7);
v_snapshotTasks_3523_ = lean_ctor_get(v___x_3515_, 8);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3532_ == 0)
{
lean_object* v_unused_3533_; 
v_unused_3533_ = lean_ctor_get(v___x_3515_, 5);
lean_dec(v_unused_3533_);
v___x_3525_ = v___x_3515_;
v_isShared_3526_ = v_isSharedCheck_3532_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_snapshotTasks_3523_);
lean_inc(v_infoState_3522_);
lean_inc(v_messages_3521_);
lean_inc(v_traceState_3520_);
lean_inc(v_auxDeclNGen_3519_);
lean_inc(v_ngen_3518_);
lean_inc(v_nextMacroScope_3517_);
lean_inc(v_env_3516_);
lean_dec(v___x_3515_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3532_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3527_; lean_object* v___x_3529_; 
v___x_3527_ = l_Lean_Kernel_enableDiag(v_env_3516_, v___y_3500_);
lean_inc_ref(v___y_3509_);
if (v_isShared_3526_ == 0)
{
lean_ctor_set(v___x_3525_, 5, v___y_3509_);
lean_ctor_set(v___x_3525_, 0, v___x_3527_);
v___x_3529_ = v___x_3525_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v___x_3527_);
lean_ctor_set(v_reuseFailAlloc_3531_, 1, v_nextMacroScope_3517_);
lean_ctor_set(v_reuseFailAlloc_3531_, 2, v_ngen_3518_);
lean_ctor_set(v_reuseFailAlloc_3531_, 3, v_auxDeclNGen_3519_);
lean_ctor_set(v_reuseFailAlloc_3531_, 4, v_traceState_3520_);
lean_ctor_set(v_reuseFailAlloc_3531_, 5, v___y_3509_);
lean_ctor_set(v_reuseFailAlloc_3531_, 6, v_messages_3521_);
lean_ctor_set(v_reuseFailAlloc_3531_, 7, v_infoState_3522_);
lean_ctor_set(v_reuseFailAlloc_3531_, 8, v_snapshotTasks_3523_);
v___x_3529_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
lean_object* v___x_3530_; 
v___x_3530_ = lean_st_ref_put(v___y_3502_, v___x_3529_);
lean_inc(v___y_3502_);
v___y_3420_ = v___y_3491_;
v___y_3421_ = v___y_3492_;
v___y_3422_ = v___y_3493_;
v___y_3423_ = v___y_3494_;
v___y_3424_ = v___y_3495_;
v___y_3425_ = v___y_3496_;
v___y_3426_ = v___y_3497_;
v___y_3427_ = v___y_3498_;
v___y_3428_ = v___y_3499_;
v___y_3429_ = v___y_3500_;
v___y_3430_ = v___y_3501_;
v___y_3431_ = v___y_3502_;
v___y_3432_ = v___y_3503_;
v___y_3433_ = v___y_3504_;
v___y_3434_ = v___y_3505_;
v___y_3435_ = v___y_3506_;
v___y_3436_ = v___y_3507_;
v___y_3437_ = v___y_3508_;
v___y_3438_ = v___y_3509_;
v___y_3439_ = v___y_3510_;
v___y_3440_ = v___y_3511_;
v___y_3441_ = v___y_3512_;
v___y_3442_ = v___y_3513_;
v___y_3443_ = v___y_3502_;
goto v___jp_3419_;
}
}
}
else
{
lean_inc(v___y_3502_);
v___y_3420_ = v___y_3491_;
v___y_3421_ = v___y_3492_;
v___y_3422_ = v___y_3493_;
v___y_3423_ = v___y_3494_;
v___y_3424_ = v___y_3495_;
v___y_3425_ = v___y_3496_;
v___y_3426_ = v___y_3497_;
v___y_3427_ = v___y_3498_;
v___y_3428_ = v___y_3499_;
v___y_3429_ = v___y_3500_;
v___y_3430_ = v___y_3501_;
v___y_3431_ = v___y_3502_;
v___y_3432_ = v___y_3503_;
v___y_3433_ = v___y_3504_;
v___y_3434_ = v___y_3505_;
v___y_3435_ = v___y_3506_;
v___y_3436_ = v___y_3507_;
v___y_3437_ = v___y_3508_;
v___y_3438_ = v___y_3509_;
v___y_3439_ = v___y_3510_;
v___y_3440_ = v___y_3511_;
v___y_3441_ = v___y_3512_;
v___y_3442_ = v___y_3513_;
v___y_3443_ = v___y_3502_;
goto v___jp_3419_;
}
}
v___jp_3540_:
{
lean_object* v___x_3549_; 
if (v_isShared_3179_ == 0)
{
lean_ctor_set_tag(v___x_3178_, 0);
lean_ctor_set(v___x_3178_, 1, v___y_3547_);
lean_ctor_set(v___x_3178_, 0, v___y_3542_);
v___x_3549_ = v___x_3178_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v___y_3542_);
lean_ctor_set(v_reuseFailAlloc_3644_, 1, v___y_3547_);
v___x_3549_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v_moduleData_3553_; lean_object* v___x_3554_; uint8_t v___x_3555_; 
v___x_3550_ = lean_box(0);
lean_inc_ref(v___y_3545_);
v___x_3551_ = l_Lean_EnvExtension_setState___redArg(v___y_3545_, v___y_3543_, v___x_3549_, v___x_3550_);
v___x_3552_ = l_Lean_Environment_header(v___x_3551_);
v_moduleData_3553_ = lean_ctor_get(v___x_3552_, 6);
lean_inc_ref(v_moduleData_3553_);
lean_dec_ref(v___x_3552_);
v___x_3554_ = lean_array_get_size(v_moduleData_3553_);
v___x_3555_ = lean_nat_dec_lt(v___y_3546_, v___x_3554_);
if (v___x_3555_ == 0)
{
lean_object* v___x_3556_; lean_object* v___x_3557_; 
lean_dec_ref(v_moduleData_3553_);
lean_dec_ref(v___x_3551_);
lean_dec(v___y_3546_);
lean_dec(v___y_3544_);
lean_dec(v___y_3541_);
lean_dec_ref(v___x_3221_);
lean_del_object(v___x_3205_);
lean_dec(v_fst_3202_);
lean_dec(v_name_3191_);
lean_dec(v_head_3184_);
lean_del_object(v___x_3182_);
lean_dec(v_head_3180_);
v___x_3556_ = lean_obj_once(&l_main___closed__22, &l_main___closed__22_once, _init_l_main___closed__22);
v___x_3557_ = l_panic___at___00main_spec__4(v___x_3556_);
return v___x_3557_;
}
else
{
lean_object* v_base_3558_; lean_object* v_private_3559_; lean_object* v_header_3560_; lean_object* v_serverBaseExts_3561_; lean_object* v_checked_3562_; lean_object* v_asyncConstsMap_3563_; lean_object* v_asyncCtx_x3f_3564_; lean_object* v_importRealizationCtx_x3f_3565_; lean_object* v_localRealizationCtxMap_3566_; lean_object* v_allRealizations_3567_; uint8_t v_isExporting_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3642_; 
v_base_3558_ = lean_ctor_get(v___x_3551_, 0);
lean_inc_ref(v_base_3558_);
v_private_3559_ = lean_ctor_get(v_base_3558_, 0);
lean_inc(v_private_3559_);
v_header_3560_ = lean_ctor_get(v_private_3559_, 5);
lean_inc_ref(v_header_3560_);
v_serverBaseExts_3561_ = lean_ctor_get(v___x_3551_, 1);
v_checked_3562_ = lean_ctor_get(v___x_3551_, 2);
v_asyncConstsMap_3563_ = lean_ctor_get(v___x_3551_, 3);
v_asyncCtx_x3f_3564_ = lean_ctor_get(v___x_3551_, 4);
v_importRealizationCtx_x3f_3565_ = lean_ctor_get(v___x_3551_, 5);
v_localRealizationCtxMap_3566_ = lean_ctor_get(v___x_3551_, 6);
v_allRealizations_3567_ = lean_ctor_get(v___x_3551_, 7);
v_isExporting_3568_ = lean_ctor_get_uint8(v___x_3551_, sizeof(void*)*8);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3642_ == 0)
{
lean_object* v_unused_3643_; 
v_unused_3643_ = lean_ctor_get(v___x_3551_, 0);
lean_dec(v_unused_3643_);
v___x_3570_ = v___x_3551_;
v_isShared_3571_ = v_isSharedCheck_3642_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_allRealizations_3567_);
lean_inc(v_localRealizationCtxMap_3566_);
lean_inc(v_importRealizationCtx_x3f_3565_);
lean_inc(v_asyncCtx_x3f_3564_);
lean_inc(v_asyncConstsMap_3563_);
lean_inc(v_checked_3562_);
lean_inc(v_serverBaseExts_3561_);
lean_dec(v___x_3551_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3642_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v_public_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3640_; 
v_public_3572_ = lean_ctor_get(v_base_3558_, 1);
v_isSharedCheck_3640_ = !lean_is_exclusive(v_base_3558_);
if (v_isSharedCheck_3640_ == 0)
{
lean_object* v_unused_3641_; 
v_unused_3641_ = lean_ctor_get(v_base_3558_, 0);
lean_dec(v_unused_3641_);
v___x_3574_ = v_base_3558_;
v_isShared_3575_ = v_isSharedCheck_3640_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_public_3572_);
lean_dec(v_base_3558_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3640_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v_constants_3576_; uint8_t v_quotInit_3577_; lean_object* v_diagnostics_3578_; lean_object* v_const2ModIdx_3579_; lean_object* v_extensions_3580_; lean_object* v_irBaseExts_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3638_; 
v_constants_3576_ = lean_ctor_get(v_private_3559_, 0);
v_quotInit_3577_ = lean_ctor_get_uint8(v_private_3559_, sizeof(void*)*6);
v_diagnostics_3578_ = lean_ctor_get(v_private_3559_, 1);
v_const2ModIdx_3579_ = lean_ctor_get(v_private_3559_, 2);
v_extensions_3580_ = lean_ctor_get(v_private_3559_, 3);
v_irBaseExts_3581_ = lean_ctor_get(v_private_3559_, 4);
v_isSharedCheck_3638_ = !lean_is_exclusive(v_private_3559_);
if (v_isSharedCheck_3638_ == 0)
{
lean_object* v_unused_3639_; 
v_unused_3639_ = lean_ctor_get(v_private_3559_, 5);
lean_dec(v_unused_3639_);
v___x_3583_ = v_private_3559_;
v_isShared_3584_ = v_isSharedCheck_3638_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_irBaseExts_3581_);
lean_inc(v_extensions_3580_);
lean_inc(v_const2ModIdx_3579_);
lean_inc(v_diagnostics_3578_);
lean_inc(v_constants_3576_);
lean_dec(v_private_3559_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3638_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
uint32_t v_trustLevel_3585_; lean_object* v_mainModule_3586_; uint8_t v_isModule_3587_; lean_object* v_regions_3588_; lean_object* v_modules_3589_; lean_object* v_moduleName2Idx_3590_; lean_object* v_importAllModules_3591_; lean_object* v_moduleData_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3636_; 
v_trustLevel_3585_ = lean_ctor_get_uint32(v_header_3560_, sizeof(void*)*7);
v_mainModule_3586_ = lean_ctor_get(v_header_3560_, 0);
v_isModule_3587_ = lean_ctor_get_uint8(v_header_3560_, sizeof(void*)*7 + 4);
v_regions_3588_ = lean_ctor_get(v_header_3560_, 2);
v_modules_3589_ = lean_ctor_get(v_header_3560_, 3);
v_moduleName2Idx_3590_ = lean_ctor_get(v_header_3560_, 4);
v_importAllModules_3591_ = lean_ctor_get(v_header_3560_, 5);
v_moduleData_3592_ = lean_ctor_get(v_header_3560_, 6);
v_isSharedCheck_3636_ = !lean_is_exclusive(v_header_3560_);
if (v_isSharedCheck_3636_ == 0)
{
lean_object* v_unused_3637_; 
v_unused_3637_ = lean_ctor_get(v_header_3560_, 1);
lean_dec(v_unused_3637_);
v___x_3594_ = v_header_3560_;
v_isShared_3595_ = v_isSharedCheck_3636_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_moduleData_3592_);
lean_inc(v_importAllModules_3591_);
lean_inc(v_moduleName2Idx_3590_);
lean_inc(v_modules_3589_);
lean_inc(v_regions_3588_);
lean_inc(v_mainModule_3586_);
lean_dec(v_header_3560_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3636_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3596_; lean_object* v_imports_3597_; lean_object* v___x_3599_; 
v___x_3596_ = lean_array_fget(v_moduleData_3553_, v___y_3546_);
lean_dec_ref(v_moduleData_3553_);
v_imports_3597_ = lean_ctor_get(v___x_3596_, 0);
lean_inc_ref(v_imports_3597_);
lean_dec(v___x_3596_);
if (v_isShared_3595_ == 0)
{
lean_ctor_set(v___x_3594_, 1, v_imports_3597_);
v___x_3599_ = v___x_3594_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 7, 5);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_mainModule_3586_);
lean_ctor_set(v_reuseFailAlloc_3635_, 1, v_imports_3597_);
lean_ctor_set(v_reuseFailAlloc_3635_, 2, v_regions_3588_);
lean_ctor_set(v_reuseFailAlloc_3635_, 3, v_modules_3589_);
lean_ctor_set(v_reuseFailAlloc_3635_, 4, v_moduleName2Idx_3590_);
lean_ctor_set(v_reuseFailAlloc_3635_, 5, v_importAllModules_3591_);
lean_ctor_set(v_reuseFailAlloc_3635_, 6, v_moduleData_3592_);
lean_ctor_set_uint32(v_reuseFailAlloc_3635_, sizeof(void*)*7, v_trustLevel_3585_);
lean_ctor_set_uint8(v_reuseFailAlloc_3635_, sizeof(void*)*7 + 4, v_isModule_3587_);
v___x_3599_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
lean_object* v___x_3601_; 
if (v_isShared_3584_ == 0)
{
lean_ctor_set(v___x_3583_, 5, v___x_3599_);
v___x_3601_ = v___x_3583_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_constants_3576_);
lean_ctor_set(v_reuseFailAlloc_3634_, 1, v_diagnostics_3578_);
lean_ctor_set(v_reuseFailAlloc_3634_, 2, v_const2ModIdx_3579_);
lean_ctor_set(v_reuseFailAlloc_3634_, 3, v_extensions_3580_);
lean_ctor_set(v_reuseFailAlloc_3634_, 4, v_irBaseExts_3581_);
lean_ctor_set(v_reuseFailAlloc_3634_, 5, v___x_3599_);
lean_ctor_set_uint8(v_reuseFailAlloc_3634_, sizeof(void*)*6, v_quotInit_3577_);
v___x_3601_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
lean_object* v___x_3603_; 
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 0, v___x_3601_);
v___x_3603_ = v___x_3574_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v___x_3601_);
lean_ctor_set(v_reuseFailAlloc_3633_, 1, v_public_3572_);
v___x_3603_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
lean_object* v___x_3605_; 
if (v_isShared_3571_ == 0)
{
lean_ctor_set(v___x_3570_, 0, v___x_3603_);
v___x_3605_ = v___x_3570_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v___x_3603_);
lean_ctor_set(v_reuseFailAlloc_3632_, 1, v_serverBaseExts_3561_);
lean_ctor_set(v_reuseFailAlloc_3632_, 2, v_checked_3562_);
lean_ctor_set(v_reuseFailAlloc_3632_, 3, v_asyncConstsMap_3563_);
lean_ctor_set(v_reuseFailAlloc_3632_, 4, v_asyncCtx_x3f_3564_);
lean_ctor_set(v_reuseFailAlloc_3632_, 5, v_importRealizationCtx_x3f_3565_);
lean_ctor_set(v_reuseFailAlloc_3632_, 6, v_localRealizationCtxMap_3566_);
lean_ctor_set(v_reuseFailAlloc_3632_, 7, v_allRealizations_3567_);
lean_ctor_set_uint8(v_reuseFailAlloc_3632_, sizeof(void*)*8, v_isExporting_3568_);
v___x_3605_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v_env_3628_; lean_object* v___x_3629_; uint8_t v___x_3630_; uint8_t v___x_3631_; 
v___x_3606_ = l_Lean_Compiler_LCNF_postponedCompileDeclsExt;
v___x_3607_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3215_, v___x_3606_, v___x_3605_, v___y_3546_, v___x_3539_);
lean_dec(v___y_3546_);
v___x_3608_ = l_Lean_firstFrontendMacroScope;
v___x_3609_ = lean_obj_once(&l_main___closed__23, &l_main___closed__23_once, _init_l_main___closed__23);
v___x_3610_ = ((lean_object*)(l_main___closed__26));
lean_inc_n(v___y_3544_, 3);
v___x_3611_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3611_, 0, v___y_3544_);
lean_ctor_set(v___x_3611_, 1, v___x_3536_);
lean_ctor_set(v___x_3611_, 2, v___x_3208_);
v___x_3612_ = lean_obj_once(&l_main___closed__27, &l_main___closed__27_once, _init_l_main___closed__27);
v___x_3613_ = lean_obj_once(&l_main___closed__30, &l_main___closed__30_once, _init_l_main___closed__30);
v___x_3614_ = lean_obj_once(&l_main___closed__31, &l_main___closed__31_once, _init_l_main___closed__31);
v___x_3615_ = lean_obj_once(&l_main___closed__32, &l_main___closed__32_once, _init_l_main___closed__32);
v___x_3616_ = ((lean_object*)(l_main___closed__33));
lean_inc_ref(v___x_3611_);
v___x_3617_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3605_);
lean_ctor_set(v___x_3617_, 1, v___x_3609_);
lean_ctor_set(v___x_3617_, 2, v___x_3610_);
lean_ctor_set(v___x_3617_, 3, v___x_3611_);
lean_ctor_set(v___x_3617_, 4, v___x_3612_);
lean_ctor_set(v___x_3617_, 5, v___x_3613_);
lean_ctor_set(v___x_3617_, 6, v___x_3614_);
lean_ctor_set(v___x_3617_, 7, v___x_3615_);
lean_ctor_set(v___x_3617_, 8, v___x_3616_);
v___x_3618_ = lean_st_mk_ref(v___x_3617_);
v___x_3619_ = l_Lean_inheritedTraceOptions;
v___x_3620_ = lean_st_ref_get(v___x_3619_);
v___x_3621_ = lean_st_ref_get(v___x_3618_);
v___x_3622_ = l_Lean_instInhabitedFileMap_default;
v___x_3623_ = lean_unsigned_to_nat(1000u);
v___x_3624_ = lean_box(0);
v___x_3625_ = l_Lean_Core_getMaxHeartbeats(v___x_3221_);
v___x_3626_ = lean_box(0);
lean_inc_ref(v___x_3221_);
lean_inc(v_head_3180_);
v___x_3627_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3627_, 0, v_head_3180_);
lean_ctor_set(v___x_3627_, 1, v___x_3622_);
lean_ctor_set(v___x_3627_, 2, v___x_3221_);
lean_ctor_set(v___x_3627_, 3, v___x_3220_);
lean_ctor_set(v___x_3627_, 4, v___x_3623_);
lean_ctor_set(v___x_3627_, 5, v___x_3624_);
lean_ctor_set(v___x_3627_, 6, v___y_3544_);
lean_ctor_set(v___x_3627_, 7, v___x_3208_);
lean_ctor_set(v___x_3627_, 8, v___x_3220_);
lean_ctor_set(v___x_3627_, 9, v___x_3625_);
lean_ctor_set(v___x_3627_, 10, v___y_3544_);
lean_ctor_set(v___x_3627_, 11, v___x_3608_);
lean_ctor_set(v___x_3627_, 12, v___x_3626_);
lean_ctor_set(v___x_3627_, 13, v___x_3620_);
lean_ctor_set_uint8(v___x_3627_, sizeof(void*)*14, v___x_3194_);
lean_ctor_set_uint8(v___x_3627_, sizeof(void*)*14 + 1, v___x_3194_);
v_env_3628_ = lean_ctor_get(v___x_3621_, 0);
lean_inc_ref(v_env_3628_);
lean_dec(v___x_3621_);
v___x_3629_ = l_Lean_diagnostics;
v___x_3630_ = l_Lean_Option_get___at___00main_spec__7(v___x_3221_, v___x_3629_);
v___x_3631_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3628_);
lean_dec_ref(v_env_3628_);
if (v___x_3631_ == 0)
{
if (v___x_3630_ == 0)
{
v___y_3491_ = v___x_3555_;
v___y_3492_ = v___y_3541_;
v___y_3493_ = v___x_3608_;
v___y_3494_ = v___x_3624_;
v___y_3495_ = v___x_3613_;
v___y_3496_ = v___x_3622_;
v___y_3497_ = v___x_3626_;
v___y_3498_ = v___x_3619_;
v___y_3499_ = v___x_3208_;
v___y_3500_ = v___x_3630_;
v___y_3501_ = v___x_3609_;
v___y_3502_ = v___x_3618_;
v___y_3503_ = v___x_3606_;
v___y_3504_ = v___x_3607_;
v___y_3505_ = v___x_3611_;
v___y_3506_ = v___x_3610_;
v___y_3507_ = v___y_3544_;
v___y_3508_ = v___x_3614_;
v___y_3509_ = v___x_3613_;
v___y_3510_ = v___x_3612_;
v___y_3511_ = v___x_3615_;
v___y_3512_ = v___x_3616_;
v___y_3513_ = v___x_3627_;
v___y_3514_ = v___x_3555_;
goto v___jp_3490_;
}
else
{
v___y_3491_ = v___x_3555_;
v___y_3492_ = v___y_3541_;
v___y_3493_ = v___x_3608_;
v___y_3494_ = v___x_3624_;
v___y_3495_ = v___x_3613_;
v___y_3496_ = v___x_3622_;
v___y_3497_ = v___x_3626_;
v___y_3498_ = v___x_3619_;
v___y_3499_ = v___x_3208_;
v___y_3500_ = v___x_3630_;
v___y_3501_ = v___x_3609_;
v___y_3502_ = v___x_3618_;
v___y_3503_ = v___x_3606_;
v___y_3504_ = v___x_3607_;
v___y_3505_ = v___x_3611_;
v___y_3506_ = v___x_3610_;
v___y_3507_ = v___y_3544_;
v___y_3508_ = v___x_3614_;
v___y_3509_ = v___x_3613_;
v___y_3510_ = v___x_3612_;
v___y_3511_ = v___x_3615_;
v___y_3512_ = v___x_3616_;
v___y_3513_ = v___x_3627_;
v___y_3514_ = v___x_3631_;
goto v___jp_3490_;
}
}
else
{
v___y_3491_ = v___x_3555_;
v___y_3492_ = v___y_3541_;
v___y_3493_ = v___x_3608_;
v___y_3494_ = v___x_3624_;
v___y_3495_ = v___x_3613_;
v___y_3496_ = v___x_3622_;
v___y_3497_ = v___x_3626_;
v___y_3498_ = v___x_3619_;
v___y_3499_ = v___x_3208_;
v___y_3500_ = v___x_3630_;
v___y_3501_ = v___x_3609_;
v___y_3502_ = v___x_3618_;
v___y_3503_ = v___x_3606_;
v___y_3504_ = v___x_3607_;
v___y_3505_ = v___x_3611_;
v___y_3506_ = v___x_3610_;
v___y_3507_ = v___y_3544_;
v___y_3508_ = v___x_3614_;
v___y_3509_ = v___x_3613_;
v___y_3510_ = v___x_3612_;
v___y_3511_ = v___x_3615_;
v___y_3512_ = v___x_3616_;
v___y_3513_ = v___x_3627_;
v___y_3514_ = v___x_3630_;
goto v___jp_3490_;
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
v___jp_3645_:
{
lean_object* v___x_3650_; lean_object* v_toEnvExtension_3651_; lean_object* v_asyncMode_3652_; lean_object* v___x_3653_; lean_object* v_importedEntries_3654_; lean_object* v_state_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; uint8_t v___x_3658_; 
v___x_3650_ = l_Lean_IR_declMapExt;
v_toEnvExtension_3651_ = lean_ctor_get(v___x_3650_, 0);
v_asyncMode_3652_ = lean_ctor_get(v_toEnvExtension_3651_, 2);
lean_inc(v___y_3647_);
lean_inc_ref(v___y_3649_);
v___x_3653_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3212_, v_toEnvExtension_3651_, v___y_3649_, v_asyncMode_3652_, v___y_3647_);
v_importedEntries_3654_ = lean_ctor_get(v___x_3653_, 0);
lean_inc_ref(v_importedEntries_3654_);
v_state_3655_ = lean_ctor_get(v___x_3653_, 1);
lean_inc(v_state_3655_);
lean_dec(v___x_3653_);
v___x_3656_ = lean_array_get_borrowed(v___x_3213_, v_importedEntries_3654_, v___y_3648_);
v___x_3657_ = lean_array_get_size(v___x_3656_);
v___x_3658_ = lean_nat_dec_lt(v___x_3220_, v___x_3657_);
if (v___x_3658_ == 0)
{
v___y_3541_ = v___y_3646_;
v___y_3542_ = v_importedEntries_3654_;
v___y_3543_ = v___y_3649_;
v___y_3544_ = v___y_3647_;
v___y_3545_ = v_toEnvExtension_3651_;
v___y_3546_ = v___y_3648_;
v___y_3547_ = v_state_3655_;
goto v___jp_3540_;
}
else
{
uint8_t v___x_3659_; 
v___x_3659_ = lean_nat_dec_le(v___x_3657_, v___x_3657_);
if (v___x_3659_ == 0)
{
if (v___x_3658_ == 0)
{
v___y_3541_ = v___y_3646_;
v___y_3542_ = v_importedEntries_3654_;
v___y_3543_ = v___y_3649_;
v___y_3544_ = v___y_3647_;
v___y_3545_ = v_toEnvExtension_3651_;
v___y_3546_ = v___y_3648_;
v___y_3547_ = v_state_3655_;
goto v___jp_3540_;
}
else
{
size_t v___x_3660_; size_t v___x_3661_; lean_object* v___x_3662_; 
v___x_3660_ = ((size_t)0ULL);
v___x_3661_ = lean_usize_of_nat(v___x_3657_);
lean_inc_ref(v___y_3649_);
v___x_3662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3649_, v___x_3656_, v___x_3660_, v___x_3661_, v_state_3655_);
v___y_3541_ = v___y_3646_;
v___y_3542_ = v_importedEntries_3654_;
v___y_3543_ = v___y_3649_;
v___y_3544_ = v___y_3647_;
v___y_3545_ = v_toEnvExtension_3651_;
v___y_3546_ = v___y_3648_;
v___y_3547_ = v___x_3662_;
goto v___jp_3540_;
}
}
else
{
size_t v___x_3663_; size_t v___x_3664_; lean_object* v___x_3665_; 
v___x_3663_ = ((size_t)0ULL);
v___x_3664_ = lean_usize_of_nat(v___x_3657_);
lean_inc_ref(v___y_3649_);
v___x_3665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3649_, v___x_3656_, v___x_3663_, v___x_3664_, v_state_3655_);
v___y_3541_ = v___y_3646_;
v___y_3542_ = v_importedEntries_3654_;
v___y_3543_ = v___y_3649_;
v___y_3544_ = v___y_3647_;
v___y_3545_ = v_toEnvExtension_3651_;
v___y_3546_ = v___y_3648_;
v___y_3547_ = v___x_3665_;
goto v___jp_3540_;
}
}
}
v___jp_3666_:
{
uint8_t v___x_3673_; 
v___x_3673_ = lean_nat_dec_lt(v___x_3220_, v___y_3668_);
if (v___x_3673_ == 0)
{
lean_dec_ref(v___y_3670_);
lean_dec(v___y_3668_);
v___y_3646_ = v___y_3667_;
v___y_3647_ = v___y_3669_;
v___y_3648_ = v___y_3671_;
v___y_3649_ = v___y_3672_;
goto v___jp_3645_;
}
else
{
uint8_t v___x_3674_; 
v___x_3674_ = lean_nat_dec_le(v___y_3668_, v___y_3668_);
if (v___x_3674_ == 0)
{
if (v___x_3673_ == 0)
{
lean_dec_ref(v___y_3670_);
lean_dec(v___y_3668_);
v___y_3646_ = v___y_3667_;
v___y_3647_ = v___y_3669_;
v___y_3648_ = v___y_3671_;
v___y_3649_ = v___y_3672_;
goto v___jp_3645_;
}
else
{
size_t v___x_3675_; size_t v___x_3676_; lean_object* v___x_3677_; 
v___x_3675_ = ((size_t)0ULL);
v___x_3676_ = lean_usize_of_nat(v___y_3668_);
lean_dec(v___y_3668_);
v___x_3677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3670_, v___x_3675_, v___x_3676_, v___y_3672_);
lean_dec_ref(v___y_3670_);
v___y_3646_ = v___y_3667_;
v___y_3647_ = v___y_3669_;
v___y_3648_ = v___y_3671_;
v___y_3649_ = v___x_3677_;
goto v___jp_3645_;
}
}
else
{
size_t v___x_3678_; size_t v___x_3679_; lean_object* v___x_3680_; 
v___x_3678_ = ((size_t)0ULL);
v___x_3679_ = lean_usize_of_nat(v___y_3668_);
lean_dec(v___y_3668_);
v___x_3680_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3670_, v___x_3678_, v___x_3679_, v___y_3672_);
lean_dec_ref(v___y_3670_);
v___y_3646_ = v___y_3667_;
v___y_3647_ = v___y_3669_;
v___y_3648_ = v___y_3671_;
v___y_3649_ = v___x_3680_;
goto v___jp_3645_;
}
}
}
v___jp_3681_:
{
lean_object* v___x_3687_; uint8_t v___x_3688_; 
v___x_3687_ = lean_array_get_size(v___y_3686_);
v___x_3688_ = lean_nat_dec_lt(v___x_3220_, v___x_3687_);
if (v___x_3688_ == 0)
{
v___y_3667_ = v___y_3682_;
v___y_3668_ = v___x_3687_;
v___y_3669_ = v___y_3685_;
v___y_3670_ = v___y_3686_;
v___y_3671_ = v___y_3683_;
v___y_3672_ = v___y_3684_;
goto v___jp_3666_;
}
else
{
uint8_t v___x_3689_; 
v___x_3689_ = lean_nat_dec_le(v___x_3687_, v___x_3687_);
if (v___x_3689_ == 0)
{
if (v___x_3688_ == 0)
{
v___y_3667_ = v___y_3682_;
v___y_3668_ = v___x_3687_;
v___y_3669_ = v___y_3685_;
v___y_3670_ = v___y_3686_;
v___y_3671_ = v___y_3683_;
v___y_3672_ = v___y_3684_;
goto v___jp_3666_;
}
else
{
size_t v___x_3690_; size_t v___x_3691_; lean_object* v___x_3692_; 
v___x_3690_ = ((size_t)0ULL);
v___x_3691_ = lean_usize_of_nat(v___x_3687_);
v___x_3692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3686_, v___x_3690_, v___x_3691_, v___y_3684_);
v___y_3667_ = v___y_3682_;
v___y_3668_ = v___x_3687_;
v___y_3669_ = v___y_3685_;
v___y_3670_ = v___y_3686_;
v___y_3671_ = v___y_3683_;
v___y_3672_ = v___x_3692_;
goto v___jp_3666_;
}
}
else
{
size_t v___x_3693_; size_t v___x_3694_; lean_object* v___x_3695_; 
v___x_3693_ = ((size_t)0ULL);
v___x_3694_ = lean_usize_of_nat(v___x_3687_);
v___x_3695_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3686_, v___x_3693_, v___x_3694_, v___y_3684_);
v___y_3667_ = v___y_3682_;
v___y_3668_ = v___x_3687_;
v___y_3669_ = v___y_3685_;
v___y_3670_ = v___y_3686_;
v___y_3671_ = v___y_3683_;
v___y_3672_ = v___x_3695_;
goto v___jp_3666_;
}
}
}
v___jp_3697_:
{
lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___f_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; 
v___x_3699_ = l_Lean_instInhabitedImportState_default;
v___x_3700_ = lean_box(v___x_3539_);
v___x_3701_ = lean_box(v___y_3698_);
v___x_3702_ = lean_box(v___x_3217_);
v___x_3703_ = lean_box(v___x_3696_);
v___x_3704_ = lean_box(v___x_3194_);
lean_inc(v_name_3191_);
lean_inc_ref(v___x_3221_);
v___f_3705_ = lean_alloc_closure((void*)(l_main___lam__0___boxed), 11, 10);
lean_closure_set(v___f_3705_, 0, v___x_3699_);
lean_closure_set(v___f_3705_, 1, v___x_3538_);
lean_closure_set(v___f_3705_, 2, v___x_3700_);
lean_closure_set(v___f_3705_, 3, v_importArts_3192_);
lean_closure_set(v___f_3705_, 4, v___x_3701_);
lean_closure_set(v___f_3705_, 5, v___x_3702_);
lean_closure_set(v___f_3705_, 6, v___x_3703_);
lean_closure_set(v___f_3705_, 7, v___x_3221_);
lean_closure_set(v___f_3705_, 8, v___x_3704_);
lean_closure_set(v___f_3705_, 9, v_name_3191_);
v___x_3706_ = lean_alloc_closure((void*)(l_Lean_withImporting___boxed), 3, 2);
lean_closure_set(v___x_3706_, 0, lean_box(0));
lean_closure_set(v___x_3706_, 1, v___f_3705_);
v___x_3707_ = lean_box(0);
v___x_3708_ = l_Lean_profileitIOUnsafe___redArg(v___x_3534_, v___x_3221_, v___x_3706_, v___x_3707_);
if (lean_obj_tag(v___x_3708_) == 0)
{
lean_object* v_a_3709_; lean_object* v___x_3710_; lean_object* v_ext_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; 
v_a_3709_ = lean_ctor_get(v___x_3708_, 0);
lean_inc(v_a_3709_);
lean_dec_ref_known(v___x_3708_, 1);
v___x_3710_ = l_Lean_Compiler_CSimp_ext;
v_ext_3711_ = lean_ctor_get(v___x_3710_, 1);
lean_inc(v_name_3191_);
v___x_3712_ = l_Lean_Environment_setMainModule(v_a_3709_, v_name_3191_);
lean_inc_ref(v_ext_3711_);
v___x_3713_ = l_main___elam__0___redArg(v___x_3707_, v___x_3207_, v_ext_3711_, v___x_3712_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v_a_3714_; lean_object* v___x_3715_; lean_object* v_ext_3716_; lean_object* v___x_3717_; 
v_a_3714_ = lean_ctor_get(v___x_3713_, 0);
lean_inc(v_a_3714_);
lean_dec_ref_known(v___x_3713_, 1);
v___x_3715_ = l_Lean_Meta_instanceExtension;
v_ext_3716_ = lean_ctor_get(v___x_3715_, 1);
lean_inc_ref(v_ext_3716_);
v___x_3717_ = l_main___elam__0___redArg(v___x_3707_, v___x_3207_, v_ext_3716_, v_a_3714_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_a_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; 
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_a_3718_);
lean_dec_ref_known(v___x_3717_, 1);
v___x_3719_ = l_Lean_classExtension;
v___x_3720_ = l_main___elam__0___redArg(v___x_3707_, v___x_3209_, v___x_3719_, v_a_3718_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_object* v_a_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; 
v_a_3721_ = lean_ctor_get(v___x_3720_, 0);
lean_inc(v_a_3721_);
lean_dec_ref_known(v___x_3720_, 1);
v___x_3722_ = l_Lean_Meta_Match_Extension_extension;
v___x_3723_ = l_main___elam__0___redArg(v___x_3707_, v___x_3210_, v___x_3722_, v_a_3721_);
if (lean_obj_tag(v___x_3723_) == 0)
{
lean_object* v_a_3724_; lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3751_; 
v_a_3724_ = lean_ctor_get(v___x_3723_, 0);
v_isSharedCheck_3751_ = !lean_is_exclusive(v___x_3723_);
if (v_isSharedCheck_3751_ == 0)
{
v___x_3726_ = v___x_3723_;
v_isShared_3727_ = v_isSharedCheck_3751_;
goto v_resetjp_3725_;
}
else
{
lean_inc(v_a_3724_);
lean_dec(v___x_3723_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3751_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v___x_3728_; 
v___x_3728_ = l_Lean_Environment_getModuleIdx_x3f(v_a_3724_, v_name_3191_);
if (lean_obj_tag(v___x_3728_) == 1)
{
lean_object* v_val_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; uint8_t v___x_3734_; 
lean_del_object(v___x_3726_);
v_val_3729_ = lean_ctor_get(v___x_3728_, 0);
lean_inc(v_val_3729_);
lean_dec_ref_known(v___x_3728_, 1);
v___x_3730_ = l_Lean_Compiler_LCNF_impureSigExt;
v___x_3731_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3211_, v___x_3730_, v_a_3724_, v_val_3729_, v___x_3539_);
v___x_3732_ = lean_array_get_size(v___x_3731_);
v___x_3733_ = ((lean_object*)(l_main___closed__34));
v___x_3734_ = lean_nat_dec_lt(v___x_3220_, v___x_3732_);
if (v___x_3734_ == 0)
{
lean_dec_ref(v___x_3731_);
v___y_3682_ = v___x_3707_;
v___y_3683_ = v_val_3729_;
v___y_3684_ = v_a_3724_;
v___y_3685_ = v___x_3707_;
v___y_3686_ = v___x_3733_;
goto v___jp_3681_;
}
else
{
uint8_t v___x_3735_; 
v___x_3735_ = lean_nat_dec_le(v___x_3732_, v___x_3732_);
if (v___x_3735_ == 0)
{
if (v___x_3734_ == 0)
{
lean_dec_ref(v___x_3731_);
v___y_3682_ = v___x_3707_;
v___y_3683_ = v_val_3729_;
v___y_3684_ = v_a_3724_;
v___y_3685_ = v___x_3707_;
v___y_3686_ = v___x_3733_;
goto v___jp_3681_;
}
else
{
size_t v___x_3736_; size_t v___x_3737_; lean_object* v___x_3738_; 
v___x_3736_ = ((size_t)0ULL);
v___x_3737_ = lean_usize_of_nat(v___x_3732_);
lean_inc(v_a_3724_);
v___x_3738_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_a_3724_, v___x_3731_, v___x_3736_, v___x_3737_, v___x_3733_);
lean_dec_ref(v___x_3731_);
v___y_3682_ = v___x_3707_;
v___y_3683_ = v_val_3729_;
v___y_3684_ = v_a_3724_;
v___y_3685_ = v___x_3707_;
v___y_3686_ = v___x_3738_;
goto v___jp_3681_;
}
}
else
{
size_t v___x_3739_; size_t v___x_3740_; lean_object* v___x_3741_; 
v___x_3739_ = ((size_t)0ULL);
v___x_3740_ = lean_usize_of_nat(v___x_3732_);
lean_inc(v_a_3724_);
v___x_3741_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_a_3724_, v___x_3731_, v___x_3739_, v___x_3740_, v___x_3733_);
lean_dec_ref(v___x_3731_);
v___y_3682_ = v___x_3707_;
v___y_3683_ = v_val_3729_;
v___y_3684_ = v_a_3724_;
v___y_3685_ = v___x_3707_;
v___y_3686_ = v___x_3741_;
goto v___jp_3681_;
}
}
}
else
{
lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3749_; 
lean_dec(v___x_3728_);
lean_dec(v_a_3724_);
lean_dec_ref(v___x_3221_);
lean_del_object(v___x_3205_);
lean_dec(v_fst_3202_);
lean_dec(v_head_3184_);
lean_del_object(v___x_3182_);
lean_dec(v_head_3180_);
lean_del_object(v___x_3178_);
v___x_3742_ = ((lean_object*)(l_main___closed__35));
v___x_3743_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3191_, v___x_3217_);
v___x_3744_ = lean_string_append(v___x_3742_, v___x_3743_);
lean_dec_ref(v___x_3743_);
v___x_3745_ = ((lean_object*)(l_main___closed__36));
v___x_3746_ = lean_string_append(v___x_3744_, v___x_3745_);
v___x_3747_ = lean_mk_io_user_error(v___x_3746_);
if (v_isShared_3727_ == 0)
{
lean_ctor_set_tag(v___x_3726_, 1);
lean_ctor_set(v___x_3726_, 0, v___x_3747_);
v___x_3749_ = v___x_3726_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v___x_3747_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
}
}
else
{
lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3759_; 
lean_dec_ref(v___x_3221_);
lean_del_object(v___x_3205_);
lean_dec(v_fst_3202_);
lean_dec(v_name_3191_);
lean_dec(v_head_3184_);
lean_del_object(v___x_3182_);
lean_dec(v_head_3180_);
lean_del_object(v___x_3178_);
v_a_3752_ = lean_ctor_get(v___x_3723_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v___x_3723_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3754_ = v___x_3723_;
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___x_3723_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3757_; 
if (v_isShared_3755_ == 0)
{
v___x_3757_ = v___x_3754_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_a_3752_);
v___x_3757_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
return v___x_3757_;
}
}
}
}
else
{
lean_object* v_a_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3767_; 
lean_dec_ref(v___x_3221_);
lean_del_object(v___x_3205_);
lean_dec(v_fst_3202_);
lean_dec(v_name_3191_);
lean_dec(v_head_3184_);
lean_del_object(v___x_3182_);
lean_dec(v_head_3180_);
lean_del_object(v___x_3178_);
v_a_3760_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3762_ = v___x_3720_;
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_a_3760_);
lean_dec(v___x_3720_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3765_; 
if (v_isShared_3763_ == 0)
{
v___x_3765_ = v___x_3762_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_a_3760_);
v___x_3765_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
return v___x_3765_;
}
}
}
}
else
{
lean_object* v_a_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3775_; 
lean_dec_ref(v___x_3221_);
lean_del_object(v___x_3205_);
lean_dec(v_fst_3202_);
lean_dec(v_name_3191_);
lean_dec(v_head_3184_);
lean_del_object(v___x_3182_);
lean_dec(v_head_3180_);
lean_del_object(v___x_3178_);
v_a_3768_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3770_ = v___x_3717_;
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_a_3768_);
lean_dec(v___x_3717_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3773_; 
if (v_isShared_3771_ == 0)
{
v___x_3773_ = v___x_3770_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_a_3768_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
}
else
{
lean_object* v_a_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3783_; 
lean_dec_ref(v___x_3221_);
lean_del_object(v___x_3205_);
lean_dec(v_fst_3202_);
lean_dec(v_name_3191_);
lean_dec(v_head_3184_);
lean_del_object(v___x_3182_);
lean_dec(v_head_3180_);
lean_del_object(v___x_3178_);
v_a_3776_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3783_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3783_ == 0)
{
v___x_3778_ = v___x_3713_;
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_a_3776_);
lean_dec(v___x_3713_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
lean_object* v___x_3781_; 
if (v_isShared_3779_ == 0)
{
v___x_3781_ = v___x_3778_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_a_3776_);
v___x_3781_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
return v___x_3781_;
}
}
}
}
else
{
lean_object* v_a_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3791_; 
lean_dec_ref(v___x_3221_);
lean_del_object(v___x_3205_);
lean_dec(v_fst_3202_);
lean_dec(v_name_3191_);
lean_dec(v_head_3184_);
lean_del_object(v___x_3182_);
lean_dec(v_head_3180_);
lean_del_object(v___x_3178_);
v_a_3784_ = lean_ctor_get(v___x_3708_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v___x_3708_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3786_ = v___x_3708_;
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_a_3784_);
lean_dec(v___x_3708_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v___x_3789_; 
if (v_isShared_3787_ == 0)
{
v___x_3789_ = v___x_3786_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_a_3784_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
return v___x_3789_;
}
}
}
}
}
}
else
{
lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3801_; 
lean_dec(v_a_3200_);
lean_dec(v_importArts_3192_);
lean_dec(v_name_3191_);
lean_dec(v_head_3184_);
lean_del_object(v___x_3182_);
lean_dec(v_head_3180_);
lean_del_object(v___x_3178_);
v_a_3794_ = lean_ctor_get(v___x_3201_, 0);
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3201_);
if (v_isSharedCheck_3801_ == 0)
{
v___x_3796_ = v___x_3201_;
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_a_3794_);
lean_dec(v___x_3201_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3799_; 
if (v_isShared_3797_ == 0)
{
v___x_3799_ = v___x_3796_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_a_3794_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
}
}
else
{
lean_object* v_a_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3809_; 
lean_dec(v_importArts_3192_);
lean_dec(v_name_3191_);
lean_dec(v_head_3184_);
lean_del_object(v___x_3182_);
lean_dec(v_head_3180_);
lean_del_object(v___x_3178_);
v_a_3802_ = lean_ctor_get(v___x_3199_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3804_ = v___x_3199_;
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_a_3802_);
lean_dec(v___x_3199_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3807_; 
if (v_isShared_3805_ == 0)
{
v___x_3807_ = v___x_3804_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_a_3802_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
}
}
}
else
{
lean_object* v_a_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3818_; 
lean_del_object(v___x_3187_);
lean_dec(v_tail_3185_);
lean_dec(v_head_3184_);
lean_del_object(v___x_3182_);
lean_dec(v_head_3180_);
lean_del_object(v___x_3178_);
v_a_3811_ = lean_ctor_get(v___x_3189_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3813_ = v___x_3189_;
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_a_3811_);
lean_dec(v___x_3189_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3816_; 
if (v_isShared_3814_ == 0)
{
v___x_3816_ = v___x_3813_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v_a_3811_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
return v___x_3816_;
}
}
}
}
}
}
}
else
{
lean_dec(v_tail_3175_);
lean_dec_ref_known(v_tail_3174_, 2);
lean_dec_ref_known(v_args_3149_, 2);
goto v___jp_3151_;
}
}
else
{
lean_dec(v_tail_3174_);
lean_dec_ref_known(v_args_3149_, 2);
goto v___jp_3151_;
}
}
else
{
lean_dec(v_args_3149_);
goto v___jp_3151_;
}
v___jp_3151_:
{
lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3152_ = ((lean_object*)(l_main___closed__0));
v___x_3153_ = l_IO_println___at___00Lean_Environment_displayStats_spec__1(v___x_3152_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3161_; 
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3161_ == 0)
{
lean_object* v_unused_3162_; 
v_unused_3162_ = lean_ctor_get(v___x_3153_, 0);
lean_dec(v_unused_3162_);
v___x_3155_ = v___x_3153_;
v_isShared_3156_ = v_isSharedCheck_3161_;
goto v_resetjp_3154_;
}
else
{
lean_dec(v___x_3153_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3161_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3157_; lean_object* v___x_3159_; 
v___x_3157_ = l_main___boxed__const__1;
if (v_isShared_3156_ == 0)
{
lean_ctor_set(v___x_3155_, 0, v___x_3157_);
v___x_3159_ = v___x_3155_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3170_; 
v_a_3163_ = lean_ctor_get(v___x_3153_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3165_ = v___x_3153_;
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_dec(v___x_3153_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3168_; 
if (v_isShared_3166_ == 0)
{
v___x_3168_ = v___x_3165_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_a_3163_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
}
}
v___jp_3171_:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3172_ = l_main___boxed__const__2;
v___x_3173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3172_);
return v___x_3173_;
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_3824_, lean_object* v_a_3825_){
_start:
{
lean_object* v_res_3826_; 
v_res_3826_ = _lean_main(v_args_3824_);
return v_res_3826_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1(lean_object* v_as_3827_, lean_object* v_as_x27_3828_, lean_object* v_b_3829_, lean_object* v_a_3830_){
_start:
{
lean_object* v___x_3832_; 
v___x_3832_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_3828_, v_b_3829_);
return v___x_3832_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___boxed(lean_object* v_as_3833_, lean_object* v_as_x27_3834_, lean_object* v_b_3835_, lean_object* v_a_3836_, lean_object* v___y_3837_){
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l_List_forIn_x27_loop___at___00main_spec__1(v_as_3833_, v_as_x27_3834_, v_b_3835_, v_a_3836_);
lean_dec(v_as_x27_3834_);
lean_dec(v_as_3833_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14(lean_object* v___y_3839_, lean_object* v___y_3840_){
_start:
{
lean_object* v___x_3842_; 
v___x_3842_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___redArg(v___y_3840_);
return v___x_3842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___boxed(lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_){
_start:
{
lean_object* v_res_3846_; 
v_res_3846_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14(v___y_3843_, v___y_3844_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
return v_res_3846_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(lean_object* v_00_u03b2_3847_, lean_object* v_m_3848_, lean_object* v_a_3849_, lean_object* v_fallback_3850_){
_start:
{
lean_object* v___x_3851_; 
v___x_3851_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg(v_m_3848_, v_a_3849_, v_fallback_3850_);
return v___x_3851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___boxed(lean_object* v_00_u03b2_3852_, lean_object* v_m_3853_, lean_object* v_a_3854_, lean_object* v_fallback_3855_){
_start:
{
lean_object* v_res_3856_; 
v_res_3856_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(v_00_u03b2_3852_, v_m_3853_, v_a_3854_, v_fallback_3855_);
lean_dec(v_fallback_3855_);
lean_dec_ref(v_a_3854_);
lean_dec_ref(v_m_3853_);
return v_res_3856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16(lean_object* v_00_u03b2_3857_, lean_object* v_m_3858_, lean_object* v_query_3859_){
_start:
{
lean_object* v___x_3860_; 
v___x_3860_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v_m_3858_, v_query_3859_);
return v___x_3860_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___boxed(lean_object* v_00_u03b2_3861_, lean_object* v_m_3862_, lean_object* v_query_3863_){
_start:
{
lean_object* v_res_3864_; 
v_res_3864_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16(v_00_u03b2_3861_, v_m_3862_, v_query_3863_);
lean_dec_ref(v_query_3863_);
lean_dec_ref(v_m_3862_);
return v_res_3864_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17(lean_object* v_00_u03b2_3865_, lean_object* v_m_3866_){
_start:
{
lean_object* v___x_3867_; 
v___x_3867_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_m_3866_);
return v___x_3867_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___boxed(lean_object* v_00_u03b2_3868_, lean_object* v_m_3869_){
_start:
{
lean_object* v_res_3870_; 
v_res_3870_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17(v_00_u03b2_3868_, v_m_3869_);
lean_dec_ref(v_m_3869_);
return v_res_3870_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21(lean_object* v_n_3871_, lean_object* v_as_3872_, lean_object* v_lo_3873_, lean_object* v_hi_3874_, lean_object* v_w_3875_, lean_object* v_hlo_3876_, lean_object* v_hhi_3877_){
_start:
{
lean_object* v___x_3878_; 
v___x_3878_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(v_n_3871_, v_as_3872_, v_lo_3873_, v_hi_3874_);
return v___x_3878_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___boxed(lean_object* v_n_3879_, lean_object* v_as_3880_, lean_object* v_lo_3881_, lean_object* v_hi_3882_, lean_object* v_w_3883_, lean_object* v_hlo_3884_, lean_object* v_hhi_3885_){
_start:
{
lean_object* v_res_3886_; 
v_res_3886_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21(v_n_3879_, v_as_3880_, v_lo_3881_, v_hi_3882_, v_w_3883_, v_hlo_3884_, v_hhi_3885_);
lean_dec(v_hi_3882_);
lean_dec(v_n_3879_);
return v_res_3886_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15_spec__19(lean_object* v_00_u03b2_3887_, lean_object* v_m_3888_, lean_object* v_a_3889_){
_start:
{
lean_object* v___x_3890_; 
v___x_3890_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15_spec__19___redArg(v_m_3888_, v_a_3889_);
return v___x_3890_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15_spec__19___boxed(lean_object* v_00_u03b2_3891_, lean_object* v_m_3892_, lean_object* v_a_3893_){
_start:
{
lean_object* v_res_3894_; 
v_res_3894_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15_spec__19(v_00_u03b2_3891_, v_m_3892_, v_a_3893_);
lean_dec_ref(v_a_3893_);
lean_dec_ref(v_m_3892_);
return v_res_3894_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16_spec__21(lean_object* v_00_u03b2_3895_, lean_object* v_m_3896_, lean_object* v_query_3897_, lean_object* v_x_3898_, lean_object* v_x_3899_, lean_object* v_x_3900_, lean_object* v_x_3901_){
_start:
{
lean_object* v___x_3902_; 
v___x_3902_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16_spec__21___redArg(v_m_3896_, v_query_3897_, v_x_3898_, v_x_3899_, v_x_3900_);
return v___x_3902_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16_spec__21___boxed(lean_object* v_00_u03b2_3903_, lean_object* v_m_3904_, lean_object* v_query_3905_, lean_object* v_x_3906_, lean_object* v_x_3907_, lean_object* v_x_3908_, lean_object* v_x_3909_){
_start:
{
lean_object* v_res_3910_; 
v_res_3910_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16_spec__21(v_00_u03b2_3903_, v_m_3904_, v_query_3905_, v_x_3906_, v_x_3907_, v_x_3908_, v_x_3909_);
lean_dec_ref(v_query_3905_);
lean_dec_ref(v_m_3904_);
return v_res_3910_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23(lean_object* v_00_u03b2_3911_, lean_object* v_init_3912_, lean_object* v_b_3913_){
_start:
{
lean_object* v___x_3914_; 
v___x_3914_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23___redArg(v_init_3912_, v_b_3913_);
return v___x_3914_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23___boxed(lean_object* v_00_u03b2_3915_, lean_object* v_init_3916_, lean_object* v_b_3917_){
_start:
{
lean_object* v_res_3918_; 
v_res_3918_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23(v_00_u03b2_3915_, v_init_3916_, v_b_3917_);
lean_dec_ref(v_b_3917_);
return v_res_3918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31(lean_object* v_n_3919_, lean_object* v_lo_3920_, lean_object* v_hi_3921_, lean_object* v_hhi_3922_, lean_object* v_pivot_3923_, lean_object* v_as_3924_, lean_object* v_i_3925_, lean_object* v_k_3926_, lean_object* v_ilo_3927_, lean_object* v_ik_3928_, lean_object* v_w_3929_){
_start:
{
lean_object* v___x_3930_; 
v___x_3930_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg(v_hi_3921_, v_pivot_3923_, v_as_3924_, v_i_3925_, v_k_3926_);
return v___x_3930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___boxed(lean_object* v_n_3931_, lean_object* v_lo_3932_, lean_object* v_hi_3933_, lean_object* v_hhi_3934_, lean_object* v_pivot_3935_, lean_object* v_as_3936_, lean_object* v_i_3937_, lean_object* v_k_3938_, lean_object* v_ilo_3939_, lean_object* v_ik_3940_, lean_object* v_w_3941_){
_start:
{
lean_object* v_res_3942_; 
v_res_3942_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31(v_n_3931_, v_lo_3932_, v_hi_3933_, v_hhi_3934_, v_pivot_3935_, v_as_3936_, v_i_3937_, v_k_3938_, v_ilo_3939_, v_ik_3940_, v_w_3941_);
lean_dec_ref(v_pivot_3935_);
lean_dec(v_hi_3933_);
lean_dec(v_lo_3932_);
lean_dec(v_n_3931_);
return v_res_3942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__38(lean_object* v_as_3943_, size_t v_sz_3944_, size_t v_i_3945_, lean_object* v_b_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
lean_object* v___x_3950_; 
v___x_3950_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__38___redArg(v_as_3943_, v_sz_3944_, v_i_3945_, v_b_3946_, v___y_3947_);
return v___x_3950_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__38___boxed(lean_object* v_as_3951_, lean_object* v_sz_3952_, lean_object* v_i_3953_, lean_object* v_b_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
size_t v_sz_boxed_3958_; size_t v_i_boxed_3959_; lean_object* v_res_3960_; 
v_sz_boxed_3958_ = lean_unbox_usize(v_sz_3952_);
lean_dec(v_sz_3952_);
v_i_boxed_3959_ = lean_unbox_usize(v_i_3953_);
lean_dec(v_i_3953_);
v_res_3960_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__38(v_as_3951_, v_sz_boxed_3958_, v_i_boxed_3959_, v_b_3954_, v___y_3955_, v___y_3956_);
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
lean_dec_ref(v_as_3951_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15_spec__19_spec__30(lean_object* v_00_u03b2_3961_, lean_object* v_m_3962_, lean_object* v_query_3963_){
_start:
{
lean_object* v___x_3964_; 
v___x_3964_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15_spec__19_spec__30___redArg(v_m_3962_, v_query_3963_);
return v___x_3964_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15_spec__19_spec__30___boxed(lean_object* v_00_u03b2_3965_, lean_object* v_m_3966_, lean_object* v_query_3967_){
_start:
{
lean_object* v_res_3968_; 
v_res_3968_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15_spec__19_spec__30(v_00_u03b2_3965_, v_m_3966_, v_query_3967_);
lean_dec_ref(v_query_3967_);
lean_dec_ref(v_m_3966_);
return v_res_3968_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23_spec__35(lean_object* v_00_u03b2_3969_, lean_object* v_b_3970_, lean_object* v_acc_3971_, lean_object* v_i_3972_){
_start:
{
lean_object* v___x_3973_; 
v___x_3973_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23_spec__35___redArg(v_b_3970_, v_acc_3971_, v_i_3972_);
return v___x_3973_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23_spec__35___boxed(lean_object* v_00_u03b2_3974_, lean_object* v_b_3975_, lean_object* v_acc_3976_, lean_object* v_i_3977_){
_start:
{
lean_object* v_res_3978_; 
v_res_3978_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23_spec__35(v_00_u03b2_3974_, v_b_3975_, v_acc_3976_, v_i_3977_);
lean_dec_ref(v_b_3975_);
return v_res_3978_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__41(uint8_t v___x_3979_, lean_object* v_as_3980_, size_t v_sz_3981_, size_t v_i_3982_, lean_object* v_b_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_){
_start:
{
lean_object* v___x_3987_; 
v___x_3987_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__41___redArg(v___x_3979_, v_as_3980_, v_sz_3981_, v_i_3982_, v_b_3983_, v___y_3984_);
return v___x_3987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__41___boxed(lean_object* v___x_3988_, lean_object* v_as_3989_, lean_object* v_sz_3990_, lean_object* v_i_3991_, lean_object* v_b_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_){
_start:
{
uint8_t v___x_42929__boxed_3996_; size_t v_sz_boxed_3997_; size_t v_i_boxed_3998_; lean_object* v_res_3999_; 
v___x_42929__boxed_3996_ = lean_unbox(v___x_3988_);
v_sz_boxed_3997_ = lean_unbox_usize(v_sz_3990_);
lean_dec(v_sz_3990_);
v_i_boxed_3998_ = lean_unbox_usize(v_i_3991_);
lean_dec(v_i_3991_);
v_res_3999_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__41(v___x_42929__boxed_3996_, v_as_3989_, v_sz_boxed_3997_, v_i_boxed_3998_, v_b_3992_, v___y_3993_, v___y_3994_);
lean_dec(v___y_3994_);
lean_dec_ref(v___y_3993_);
lean_dec_ref(v_as_3989_);
return v_res_3999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24_spec__36_spec__50(lean_object* v_as_4000_, size_t v_sz_4001_, size_t v_i_4002_, lean_object* v_b_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_){
_start:
{
lean_object* v___x_4007_; 
v___x_4007_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24_spec__36_spec__50___redArg(v_as_4000_, v_sz_4001_, v_i_4002_, v_b_4003_, v___y_4004_);
return v___x_4007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24_spec__36_spec__50___boxed(lean_object* v_as_4008_, lean_object* v_sz_4009_, lean_object* v_i_4010_, lean_object* v_b_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_){
_start:
{
size_t v_sz_boxed_4015_; size_t v_i_boxed_4016_; lean_object* v_res_4017_; 
v_sz_boxed_4015_ = lean_unbox_usize(v_sz_4009_);
lean_dec(v_sz_4009_);
v_i_boxed_4016_ = lean_unbox_usize(v_i_4010_);
lean_dec(v_i_4010_);
v_res_4017_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__24_spec__36_spec__50(v_as_4008_, v_sz_boxed_4015_, v_i_boxed_4016_, v_b_4011_, v___y_4012_, v___y_4013_);
lean_dec(v___y_4013_);
lean_dec_ref(v___y_4012_);
lean_dec_ref(v_as_4008_);
return v_res_4017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25_spec__39_spec__46(uint8_t v___x_4018_, lean_object* v_as_4019_, size_t v_sz_4020_, size_t v_i_4021_, lean_object* v_b_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_){
_start:
{
lean_object* v___x_4026_; 
v___x_4026_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25_spec__39_spec__46___redArg(v___x_4018_, v_as_4019_, v_sz_4020_, v_i_4021_, v_b_4022_, v___y_4023_);
return v___x_4026_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25_spec__39_spec__46___boxed(lean_object* v___x_4027_, lean_object* v_as_4028_, lean_object* v_sz_4029_, lean_object* v_i_4030_, lean_object* v_b_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_){
_start:
{
uint8_t v___x_42954__boxed_4035_; size_t v_sz_boxed_4036_; size_t v_i_boxed_4037_; lean_object* v_res_4038_; 
v___x_42954__boxed_4035_ = lean_unbox(v___x_4027_);
v_sz_boxed_4036_ = lean_unbox_usize(v_sz_4029_);
lean_dec(v_sz_4029_);
v_i_boxed_4037_ = lean_unbox_usize(v_i_4030_);
lean_dec(v_i_4030_);
v_res_4038_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25_spec__39_spec__46(v___x_42954__boxed_4035_, v_as_4028_, v_sz_boxed_4036_, v_i_boxed_4037_, v_b_4031_, v___y_4032_, v___y_4033_);
lean_dec(v___y_4033_);
lean_dec_ref(v___y_4032_);
lean_dec_ref(v_as_4028_);
return v_res_4038_;
}
}
lean_object* runtime_initialize_Init(uint8_t builtin);
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_ForEachExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_Path(uint8_t builtin);
lean_object* runtime_initialize_Lean_Environment(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_Options(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_CSimpAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_EmitC(uint8_t builtin);
lean_object* runtime_initialize_Lean_Language_Lean(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Main(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_LeanIR(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_Path(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_CSimpAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_EmitC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Language_Lean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_main___boxed__const__1 = _init_l_main___boxed__const__1();
lean_mark_persistent(l_main___boxed__const__1);
l_main___boxed__const__2 = _init_l_main___boxed__const__2();
lean_mark_persistent(l_main___boxed__const__2);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_LeanIR(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean_CoreM(uint8_t builtin);
lean_object* initialize_Lean_Util_ForEachExpr(uint8_t builtin);
lean_object* initialize_Lean_Util_Path(uint8_t builtin);
lean_object* initialize_Lean_Environment(uint8_t builtin);
lean_object* initialize_Lean_Compiler_Options(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_CSimpAttr(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_EmitC(uint8_t builtin);
lean_object* initialize_Lean_Language_Lean(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Main(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LeanIR(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Path(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_CSimpAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_EmitC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Language_Lean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_LeanIR(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_LeanIR(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_LeanIR(builtin);
}
char ** lean_setup_args(int argc, char ** argv);
#if defined(WIN32) || defined(_WIN32)
#include <windows.h>
#endif
lean_object* run_main(int argc, char ** argv) {
    lean_object* in = lean_box(0);
    int i = argc;
    while (i > 1) {
      lean_object* n;
      i--;
      n = lean_alloc_ctor(1,2,0); lean_ctor_set(n, 0, lean_mk_string(argv[i])); lean_ctor_set(n, 1, in);
      in = n;
    }
    return _lean_main(in);
}
int main(int argc, char ** argv) {
#if defined(WIN32) || defined(_WIN32)
  SetErrorMode(SEM_FAILCRITICALERRORS);
  SetConsoleOutputCP(CP_UTF8);
#endif
  lean_object* res;
  argv = lean_setup_args(argc, argv);
  res = runtime_initialize_LeanIR(1 /* builtin */);
  lean_io_mark_end_initialization();
  if (lean_io_result_is_ok(res)) {
    lean_dec_ref(res);
    lean_init_task_manager();
    res = lean_run_main(&run_main, argc, argv);
  }
  lean_finalize_task_manager();
  if (lean_io_result_is_ok(res)) {
    int ret = lean_unbox_uint32(lean_io_result_get_value(res));
    lean_dec_ref(res);
    return ret;
  } else {
    lean_io_result_show_error(res);
    lean_dec_ref(res);
    return 1;
  }
}
#ifdef __cplusplus
}
#endif
