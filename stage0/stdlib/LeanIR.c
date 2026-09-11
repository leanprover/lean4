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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Message_toString(lean_object*, uint8_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stderr();
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_importModulesCore(lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_OLeanLevel_ctorIdx(uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_finalizeImport(lean_object*, lean_object*, lean_object*, uint32_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t);
uint8_t l_Lean_instOrdOLeanLevel_ord(uint8_t, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_String_Slice_toName(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecls();
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_setOption(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_String_instHashableRaw_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* lean_ir_export_entries(lean_object*);
lean_object* l_Lean_mkModuleData(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_get_ir_extra_const_names(lean_object*, uint8_t, uint8_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_println___at___00Lean_Environment_displayStats_spec__1(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg();
extern lean_object* l_Lean_instInhabitedClassState_default;
extern lean_object* l_Lean_Meta_Match_Extension_instInhabitedState;
lean_object* l_Lean_PersistentHashMap_instInhabited___redArg();
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___redArg(lean_object*);
lean_object* l_Array_instInhabited___redArg();
lean_object* l_Lean_ModuleSetup_load(lean_object*);
lean_object* l_Lean_LeanOptions_toOptions(lean_object*);
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
extern lean_object* l_Lean_inheritedTraceOptions;
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
lean_object* l_Lean_Compiler_LCNF_resumeCompilation(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_output;
extern lean_object* l_Lean_trace_profiler_serve;
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
double lean_float_of_nat(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Elab_mkMessageCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Core_getAndEmptyMessageLog___redArg(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
extern lean_object* l_instInhabitedError;
lean_object* l_instInhabitedEIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_setState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_init_search_path();
lean_object* l_Lean_EnvExtension_setState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_postponedCompileDeclsExt;
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedFileMap_default;
extern lean_object* l_Lean_firstFrontendMacroScope;
extern lean_object* l_Lean_NameSet_empty;
extern lean_object* l_Lean_IR_declMapExt;
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_name(lean_object*);
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_panic___at___00main_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00main_spec__5___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00main_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00main_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00main_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_main___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_main___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_main___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "internal exception "};
static const lean_object* l_main___lam__1___closed__0 = (const lean_object*)&l_main___lam__1___closed__0_value;
static const lean_string_object l_main___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l_main___lam__1___closed__1 = (const lean_object*)&l_main___lam__1___closed__1_value;
static const lean_string_object l_main___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " (unknown)"};
static const lean_object* l_main___lam__1___closed__2 = (const lean_object*)&l_main___lam__1___closed__2_value;
LEAN_EXPORT lean_object* l_main___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_main___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00main_spec__3(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_boxed"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "--stat"};
static const lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0(uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0;
static lean_once_cell_t l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1;
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_main___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "usage: leanir <setup.json> <output.ir> <output.c> [--stat] <-Dopt=val>..."};
static const lean_object* l_main___closed__0 = (const lean_object*)&l_main___closed__0_value;
static lean_once_cell_t l_main___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__1;
static lean_once_cell_t l_main___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__2;
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
static const lean_ctor_object l_main___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_main___closed__8 = (const lean_object*)&l_main___closed__8_value;
static const lean_string_object l_main___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sig"};
static const lean_object* l_main___closed__9 = (const lean_object*)&l_main___closed__9_value;
static const lean_string_object l_main___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ir"};
static const lean_object* l_main___closed__10 = (const lean_object*)&l_main___closed__10_value;
static const lean_ctor_object l_main___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__10_value),LEAN_SCALAR_PTR_LITERAL(157, 0, 67, 166, 172, 92, 38, 85)}};
static const lean_object* l_main___closed__11 = (const lean_object*)&l_main___closed__11_value;
static const lean_string_object l_main___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "C code generation"};
static const lean_object* l_main___closed__12 = (const lean_object*)&l_main___closed__12_value;
static lean_once_cell_t l_main___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__13;
static const lean_string_object l_main___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "failed to create '"};
static const lean_object* l_main___closed__14 = (const lean_object*)&l_main___closed__14_value;
static const lean_string_object l_main___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "LeanIR"};
static const lean_object* l_main___closed__15 = (const lean_object*)&l_main___closed__15_value;
static const lean_string_object l_main___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "main"};
static const lean_object* l_main___closed__16 = (const lean_object*)&l_main___closed__16_value;
static const lean_string_object l_main___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_main___closed__17 = (const lean_object*)&l_main___closed__17_value;
static lean_once_cell_t l_main___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__18;
static const lean_string_object l_main___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "import"};
static const lean_object* l_main___closed__19 = (const lean_object*)&l_main___closed__19_value;
static lean_once_cell_t l_main___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__20;
static lean_once_cell_t l_main___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__21;
static const lean_string_object l_main___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l_main___closed__22 = (const lean_object*)&l_main___closed__22_value;
static const lean_ctor_object l_main___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__22_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l_main___closed__23 = (const lean_object*)&l_main___closed__23_value;
static const lean_ctor_object l_main___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_main___closed__23_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_main___closed__24 = (const lean_object*)&l_main___closed__24_value;
static lean_once_cell_t l_main___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__25;
static lean_once_cell_t l_main___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__26;
static lean_once_cell_t l_main___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__27;
static lean_once_cell_t l_main___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__28;
static lean_once_cell_t l_main___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__29;
static lean_once_cell_t l_main___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__30;
static const lean_array_object l_main___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_main___closed__31 = (const lean_object*)&l_main___closed__31_value;
static const lean_array_object l_main___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_main___closed__32 = (const lean_object*)&l_main___closed__32_value;
static const lean_string_object l_main___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "module '"};
static const lean_object* l_main___closed__33 = (const lean_object*)&l_main___closed__33_value;
static const lean_string_object l_main___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "' not found"};
static const lean_object* l_main___closed__34 = (const lean_object*)&l_main___closed__34_value;
static lean_once_cell_t l_main___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_main___closed__35;
LEAN_EXPORT lean_object* l_main___boxed__const__1;
LEAN_EXPORT lean_object* l_main___boxed__const__2;
LEAN_EXPORT lean_object* _lean_main(lean_object*);
LEAN_EXPORT lean_object* l_main___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_irEntries_110_; size_t v_sz_111_; size_t v___x_112_; lean_object* v_irExtNames_113_; uint8_t v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
lean_inc_ref_n(v_env_108_, 2);
v_irEntries_110_ = lean_ir_export_entries(v_env_108_);
v_sz_111_ = lean_array_size(v_irEntries_110_);
v___x_112_ = ((size_t)0ULL);
lean_inc_ref(v_irEntries_110_);
v_irExtNames_113_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0(v_sz_111_, v___x_112_, v_irEntries_110_);
v___x_114_ = 2;
v___x_115_ = lean_box(0);
v___x_116_ = l_Lean_mkModuleData(v_env_108_, v___x_114_, v___x_115_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v_a_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_144_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_144_ == 0)
{
v___x_119_ = v___x_116_;
v_isShared_120_ = v_isSharedCheck_144_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_a_117_);
lean_dec(v___x_116_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_144_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___y_122_; lean_object* v_entries_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v_entries_134_ = lean_ctor_get(v_a_117_, 4);
lean_inc_ref(v_entries_134_);
lean_dec(v_a_117_);
v___x_135_ = lean_unsigned_to_nat(0u);
v___x_136_ = lean_array_get_size(v_entries_134_);
v___x_137_ = ((lean_object*)(l___private_LeanIR_0__mkIRData___closed__1));
v___x_138_ = lean_nat_dec_lt(v___x_135_, v___x_136_);
if (v___x_138_ == 0)
{
lean_dec_ref(v_entries_134_);
lean_dec_ref(v_irExtNames_113_);
v___y_122_ = v___x_137_;
goto v___jp_121_;
}
else
{
uint8_t v___x_139_; 
v___x_139_ = lean_nat_dec_le(v___x_136_, v___x_136_);
if (v___x_139_ == 0)
{
if (v___x_138_ == 0)
{
lean_dec_ref(v_entries_134_);
lean_dec_ref(v_irExtNames_113_);
v___y_122_ = v___x_137_;
goto v___jp_121_;
}
else
{
size_t v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_usize_of_nat(v___x_136_);
v___x_141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2(v_irExtNames_113_, v_entries_134_, v___x_112_, v___x_140_, v___x_137_);
lean_dec_ref(v_entries_134_);
lean_dec_ref(v_irExtNames_113_);
v___y_122_ = v___x_141_;
goto v___jp_121_;
}
}
else
{
size_t v___x_142_; lean_object* v___x_143_; 
v___x_142_ = lean_usize_of_nat(v___x_136_);
v___x_143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2(v_irExtNames_113_, v_entries_134_, v___x_112_, v___x_142_, v___x_137_);
lean_dec_ref(v_entries_134_);
lean_dec_ref(v_irExtNames_113_);
v___y_122_ = v___x_143_;
goto v___jp_121_;
}
}
v___jp_121_:
{
lean_object* v___x_123_; uint8_t v_isModule_124_; lean_object* v_imports_125_; lean_object* v___x_126_; uint8_t v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_132_; 
v___x_123_ = l_Lean_Environment_header(v_env_108_);
v_isModule_124_ = lean_ctor_get_uint8(v___x_123_, sizeof(void*)*7 + 4);
v_imports_125_ = lean_ctor_get(v___x_123_, 1);
lean_inc_ref(v_imports_125_);
lean_dec_ref(v___x_123_);
v___x_126_ = ((lean_object*)(l___private_LeanIR_0__mkIRData___closed__0));
v___x_127_ = 1;
v___x_128_ = lean_get_ir_extra_const_names(v_env_108_, v___x_114_, v___x_127_);
v___x_129_ = l_Array_append___redArg(v_irEntries_110_, v___y_122_);
lean_dec_ref(v___y_122_);
v___x_130_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_130_, 0, v_imports_125_);
lean_ctor_set(v___x_130_, 1, v___x_126_);
lean_ctor_set(v___x_130_, 2, v___x_126_);
lean_ctor_set(v___x_130_, 3, v___x_128_);
lean_ctor_set(v___x_130_, 4, v___x_129_);
lean_ctor_set_uint8(v___x_130_, sizeof(void*)*5, v_isModule_124_);
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 0, v___x_130_);
v___x_132_ = v___x_119_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_130_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
}
else
{
lean_dec_ref(v_irExtNames_113_);
lean_dec_ref(v_irEntries_110_);
lean_dec_ref(v_env_108_);
return v___x_116_;
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
lean_object* v_str_173_; lean_object* v_startInclusive_174_; lean_object* v_endExclusive_175_; lean_object* v___x_176_; uint8_t v_decide_177_; 
v_str_173_ = lean_ctor_get(v_val_170_, 0);
v_startInclusive_174_ = lean_ctor_get(v_val_170_, 1);
v_endExclusive_175_ = lean_ctor_get(v_val_170_, 2);
v___x_176_ = lean_nat_sub(v_endExclusive_175_, v_startInclusive_174_);
v_decide_177_ = lean_nat_dec_eq(v_a_171_, v___x_176_);
lean_dec(v___x_176_);
if (v_decide_177_ == 0)
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
lean_object* v___x_214_; uint8_t v_decide_215_; 
v___x_214_ = lean_nat_sub(v_endExclusive_210_, v_startInclusive_209_);
v_decide_215_ = lean_nat_dec_eq(v___y_207_, v___x_214_);
lean_dec(v___x_214_);
if (v_decide_215_ == 0)
{
lean_object* v___x_216_; lean_object* v___x_218_; 
v___x_216_ = lean_nat_add(v_startInclusive_209_, v___y_207_);
lean_dec(v___y_207_);
lean_inc(v___x_216_);
lean_inc(v_startInclusive_209_);
lean_inc_ref(v_str_208_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 2, v___x_216_);
v___x_218_ = v___x_212_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_str_208_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v_startInclusive_209_);
lean_ctor_set(v_reuseFailAlloc_253_, 2, v___x_216_);
v___x_218_ = v_reuseFailAlloc_253_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
lean_object* v_name_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v_val_223_; lean_object* v___x_224_; 
v_name_219_ = l_String_Slice_toName(v___x_218_);
lean_dec_ref(v___x_218_);
v___x_220_ = lean_string_utf8_next_fast(v_str_208_, v___x_216_);
lean_dec(v___x_216_);
v___x_221_ = lean_nat_sub(v___x_220_, v_startInclusive_209_);
v___x_222_ = lean_nat_add(v_startInclusive_209_, v___x_221_);
lean_dec(v___x_221_);
lean_dec(v_startInclusive_209_);
v_val_223_ = lean_string_utf8_extract_fast(v_str_208_, v___x_222_, v_endExclusive_210_);
lean_dec(v_endExclusive_210_);
lean_dec(v___x_222_);
lean_dec_ref(v_str_208_);
v___x_224_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_244_; 
v_a_225_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_244_ == 0)
{
v___x_227_ = v___x_224_;
v_isShared_228_ = v_isSharedCheck_244_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_224_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_244_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_229_; 
v___x_229_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_225_, v_name_219_);
lean_dec(v_a_225_);
if (lean_obj_tag(v___x_229_) == 1)
{
lean_object* v_val_230_; lean_object* v___x_231_; 
lean_del_object(v___x_227_);
lean_del_object(v___x_204_);
v_val_230_ = lean_ctor_get(v___x_229_, 0);
lean_inc(v_val_230_);
lean_dec_ref_known(v___x_229_, 1);
v___x_231_ = l_Lean_Language_Lean_setOption(v_opts_198_, v_val_230_, v_name_219_, v_val_223_);
return v___x_231_;
}
else
{
lean_object* v___x_232_; uint8_t v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
lean_dec(v___x_229_);
lean_dec_ref(v_val_223_);
lean_dec_ref(v_opts_198_);
v___x_232_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__0));
v___x_233_ = 1;
v___x_234_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_219_, v___x_233_);
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
if (v_isShared_228_ == 0)
{
lean_ctor_set_tag(v___x_227_, 1);
lean_ctor_set(v___x_227_, 0, v___x_239_);
v___x_241_ = v___x_227_;
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
else
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_252_; 
lean_dec_ref(v_val_223_);
lean_dec(v_name_219_);
lean_del_object(v___x_204_);
lean_dec_ref(v_opts_198_);
v_a_245_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_252_ == 0)
{
v___x_247_ = v___x_224_;
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_224_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_248_ == 0)
{
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_a_245_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
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
static lean_object* _init_l_panic___at___00main_spec__5___closed__0(void){
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
LEAN_EXPORT lean_object* l_panic___at___00main_spec__5(lean_object* v_msg_357_){
_start:
{
lean_object* v___x_359_; lean_object* v___x_18560__overap_360_; lean_object* v___x_361_; 
v___x_359_ = lean_obj_once(&l_panic___at___00main_spec__5___closed__0, &l_panic___at___00main_spec__5___closed__0_once, _init_l_panic___at___00main_spec__5___closed__0);
v___x_18560__overap_360_ = lean_panic_fn_borrowed(v___x_359_, v_msg_357_);
v___x_361_ = lean_apply_1(v___x_18560__overap_360_, lean_box(0));
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00main_spec__5___boxed(lean_object* v_msg_362_, lean_object* v___y_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_panic___at___00main_spec__5(v_msg_362_);
return v_res_364_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00main_spec__8(lean_object* v_opts_365_, lean_object* v_opt_366_){
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__8___boxed(lean_object* v_opts_375_, lean_object* v_opt_376_){
_start:
{
uint8_t v_res_377_; lean_object* v_r_378_; 
v_res_377_ = l_Lean_Option_get___at___00main_spec__8(v_opts_375_, v_opt_376_);
lean_dec_ref(v_opt_376_);
lean_dec_ref(v_opts_375_);
v_r_378_ = lean_box(v_res_377_);
return v_r_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__9(lean_object* v_opts_379_, lean_object* v_opt_380_){
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__9___boxed(lean_object* v_opts_387_, lean_object* v_opt_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_Option_get___at___00main_spec__9(v_opts_387_, v_opt_388_);
lean_dec_ref(v_opt_388_);
lean_dec_ref(v_opts_387_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(lean_object* v_a_390_, lean_object* v_x_391_){
_start:
{
if (lean_obj_tag(v_x_391_) == 0)
{
lean_dec(v_a_390_);
return v_x_391_;
}
else
{
lean_object* v_key_392_; lean_object* v_value_393_; lean_object* v_tail_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_427_; 
v_key_392_ = lean_ctor_get(v_x_391_, 0);
v_value_393_ = lean_ctor_get(v_x_391_, 1);
v_tail_394_ = lean_ctor_get(v_x_391_, 2);
v_isSharedCheck_427_ = !lean_is_exclusive(v_x_391_);
if (v_isSharedCheck_427_ == 0)
{
v___x_396_ = v_x_391_;
v_isShared_397_ = v_isSharedCheck_427_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_tail_394_);
lean_inc(v_value_393_);
lean_inc(v_key_392_);
lean_dec(v_x_391_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_427_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
uint8_t v___x_398_; 
v___x_398_ = lean_name_eq(v_key_392_, v_a_390_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; lean_object* v___x_401_; 
v___x_399_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(v_a_390_, v_tail_394_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 2, v___x_399_);
v___x_401_ = v___x_396_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_key_392_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_value_393_);
lean_ctor_set(v_reuseFailAlloc_402_, 2, v___x_399_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
else
{
lean_object* v_toEffectiveImport_403_; lean_object* v_parts_404_; lean_object* v_irParts_405_; uint8_t v_needsIRTrans_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_426_; 
lean_dec(v_key_392_);
v_toEffectiveImport_403_ = lean_ctor_get(v_value_393_, 0);
v_parts_404_ = lean_ctor_get(v_value_393_, 1);
v_irParts_405_ = lean_ctor_get(v_value_393_, 2);
v_needsIRTrans_406_ = lean_ctor_get_uint8(v_value_393_, sizeof(void*)*3);
v_isSharedCheck_426_ = !lean_is_exclusive(v_value_393_);
if (v_isSharedCheck_426_ == 0)
{
v___x_408_ = v_value_393_;
v_isShared_409_ = v_isSharedCheck_426_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_irParts_405_);
lean_inc(v_parts_404_);
lean_inc(v_toEffectiveImport_403_);
lean_dec(v_value_393_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_426_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v_toImport_410_; uint8_t v_hasData_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_425_; 
v_toImport_410_ = lean_ctor_get(v_toEffectiveImport_403_, 0);
v_hasData_411_ = lean_ctor_get_uint8(v_toEffectiveImport_403_, sizeof(void*)*1 + 1);
v_isSharedCheck_425_ = !lean_is_exclusive(v_toEffectiveImport_403_);
if (v_isSharedCheck_425_ == 0)
{
v___x_413_ = v_toEffectiveImport_403_;
v_isShared_414_ = v_isSharedCheck_425_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_toImport_410_);
lean_dec(v_toEffectiveImport_403_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_425_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
uint8_t v___x_415_; lean_object* v___x_417_; 
v___x_415_ = 0;
if (v_isShared_414_ == 0)
{
v___x_417_ = v___x_413_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_toImport_410_);
lean_ctor_set_uint8(v_reuseFailAlloc_424_, sizeof(void*)*1 + 1, v_hasData_411_);
v___x_417_ = v_reuseFailAlloc_424_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
lean_object* v___x_419_; 
lean_ctor_set_uint8(v___x_417_, sizeof(void*)*1, v___x_415_);
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 0, v___x_417_);
v___x_419_ = v___x_408_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_417_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v_parts_404_);
lean_ctor_set(v_reuseFailAlloc_423_, 2, v_irParts_405_);
lean_ctor_set_uint8(v_reuseFailAlloc_423_, sizeof(void*)*3, v_needsIRTrans_406_);
v___x_419_ = v_reuseFailAlloc_423_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
lean_object* v___x_421_; 
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 1, v___x_419_);
lean_ctor_set(v___x_396_, 0, v_a_390_);
v___x_421_ = v___x_396_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_a_390_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_422_, 2, v_tail_394_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(lean_object* v_m_428_, lean_object* v_a_429_){
_start:
{
lean_object* v_size_430_; lean_object* v_buckets_431_; lean_object* v___x_432_; uint64_t v___y_434_; 
v_size_430_ = lean_ctor_get(v_m_428_, 0);
v_buckets_431_ = lean_ctor_get(v_m_428_, 1);
v___x_432_ = lean_array_get_size(v_buckets_431_);
if (lean_obj_tag(v_a_429_) == 0)
{
uint64_t v___x_461_; 
v___x_461_ = 1723ULL;
v___y_434_ = v___x_461_;
goto v___jp_433_;
}
else
{
uint64_t v_hash_462_; 
v_hash_462_ = lean_ctor_get_uint64(v_a_429_, sizeof(void*)*2);
v___y_434_ = v_hash_462_;
goto v___jp_433_;
}
v___jp_433_:
{
uint64_t v___x_435_; uint64_t v___x_436_; uint64_t v_fold_437_; uint64_t v___x_438_; uint64_t v___x_439_; uint64_t v___x_440_; size_t v___x_441_; size_t v___x_442_; size_t v___x_443_; size_t v___x_444_; size_t v___x_445_; lean_object* v_bucket_446_; uint8_t v___x_447_; 
v___x_435_ = 32ULL;
v___x_436_ = lean_uint64_shift_right(v___y_434_, v___x_435_);
v_fold_437_ = lean_uint64_xor(v___y_434_, v___x_436_);
v___x_438_ = 16ULL;
v___x_439_ = lean_uint64_shift_right(v_fold_437_, v___x_438_);
v___x_440_ = lean_uint64_xor(v_fold_437_, v___x_439_);
v___x_441_ = lean_uint64_to_usize(v___x_440_);
v___x_442_ = lean_usize_of_nat(v___x_432_);
v___x_443_ = ((size_t)1ULL);
v___x_444_ = lean_usize_sub(v___x_442_, v___x_443_);
v___x_445_ = lean_usize_land(v___x_441_, v___x_444_);
v_bucket_446_ = lean_array_uget_borrowed(v_buckets_431_, v___x_445_);
v___x_447_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_a_429_, v_bucket_446_);
if (v___x_447_ == 0)
{
lean_dec(v_a_429_);
return v_m_428_;
}
else
{
lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_458_; 
lean_inc(v_bucket_446_);
lean_inc_ref(v_buckets_431_);
lean_inc(v_size_430_);
v_isSharedCheck_458_ = !lean_is_exclusive(v_m_428_);
if (v_isSharedCheck_458_ == 0)
{
lean_object* v_unused_459_; lean_object* v_unused_460_; 
v_unused_459_ = lean_ctor_get(v_m_428_, 1);
lean_dec(v_unused_459_);
v_unused_460_ = lean_ctor_get(v_m_428_, 0);
lean_dec(v_unused_460_);
v___x_449_ = v_m_428_;
v_isShared_450_ = v_isSharedCheck_458_;
goto v_resetjp_448_;
}
else
{
lean_dec(v_m_428_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_458_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; lean_object* v_buckets_452_; lean_object* v_bucket_453_; lean_object* v___x_454_; lean_object* v___x_456_; 
v___x_451_ = lean_box(0);
v_buckets_452_ = lean_array_uset(v_buckets_431_, v___x_445_, v___x_451_);
v_bucket_453_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(v_a_429_, v_bucket_446_);
v___x_454_ = lean_array_uset(v_buckets_452_, v___x_445_, v_bucket_453_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 1, v___x_454_);
v___x_456_ = v___x_449_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_size_430_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v___x_454_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__0(lean_object* v___x_463_, lean_object* v___x_464_, uint8_t v___x_465_, lean_object* v_importArts_466_, uint8_t v___y_467_, uint8_t v___x_468_, lean_object* v_name_469_, uint8_t v___x_470_, lean_object* v___x_471_, uint8_t v___x_472_){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_474_ = lean_st_mk_ref(v___x_463_);
v___x_475_ = l_Lean_importModulesCore(v___x_464_, v___x_465_, v_importArts_466_, v___y_467_, v___x_468_, v___x_474_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v___x_476_; lean_object* v_moduleNameMap_477_; lean_object* v_moduleNames_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_492_; 
lean_dec_ref_known(v___x_475_, 1);
v___x_476_ = lean_st_ref_get(v___x_474_);
lean_dec(v___x_474_);
v_moduleNameMap_477_ = lean_ctor_get(v___x_476_, 0);
v_moduleNames_478_ = lean_ctor_get(v___x_476_, 1);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_492_ == 0)
{
v___x_480_ = v___x_476_;
v_isShared_481_ = v_isSharedCheck_492_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_moduleNames_478_);
lean_inc(v_moduleNameMap_477_);
lean_dec(v___x_476_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_492_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_482_; lean_object* v___x_484_; 
v___x_482_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(v_moduleNameMap_477_, v_name_469_);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v___x_482_);
v___x_484_ = v___x_480_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_482_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_moduleNames_478_);
v___x_484_ = v_reuseFailAlloc_491_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
uint32_t v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_485_ = 0;
v___x_486_ = l_Lean_OLeanLevel_ctorIdx(v___x_465_);
v___x_487_ = l_Lean_OLeanLevel_ctorIdx(v___x_470_);
v___x_488_ = lean_nat_dec_eq(v___x_486_, v___x_487_);
lean_dec(v___x_487_);
lean_dec(v___x_486_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; 
v___x_489_ = l_Lean_finalizeImport(v___x_484_, v___x_464_, v___x_471_, v___x_485_, v___x_468_, v___x_472_, v___x_465_, v___x_468_, v___x_468_);
lean_dec_ref(v___x_484_);
return v___x_489_;
}
else
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_finalizeImport(v___x_484_, v___x_464_, v___x_471_, v___x_485_, v___x_468_, v___x_472_, v___x_465_, v___x_472_, v___x_468_);
lean_dec_ref(v___x_484_);
return v___x_490_;
}
}
}
}
else
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
lean_dec(v___x_474_);
lean_dec_ref(v___x_471_);
lean_dec(v_name_469_);
lean_dec_ref(v___x_464_);
v_a_493_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_500_ == 0)
{
v___x_495_ = v___x_475_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_475_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_493_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__0___boxed(lean_object* v___x_501_, lean_object* v___x_502_, lean_object* v___x_503_, lean_object* v_importArts_504_, lean_object* v___y_505_, lean_object* v___x_506_, lean_object* v_name_507_, lean_object* v___x_508_, lean_object* v___x_509_, lean_object* v___x_510_, lean_object* v___y_511_){
_start:
{
uint8_t v___x_35406__boxed_512_; uint8_t v___y_35407__boxed_513_; uint8_t v___x_35408__boxed_514_; uint8_t v___x_35409__boxed_515_; uint8_t v___x_35411__boxed_516_; lean_object* v_res_517_; 
v___x_35406__boxed_512_ = lean_unbox(v___x_503_);
v___y_35407__boxed_513_ = lean_unbox(v___y_505_);
v___x_35408__boxed_514_ = lean_unbox(v___x_506_);
v___x_35409__boxed_515_ = lean_unbox(v___x_508_);
v___x_35411__boxed_516_ = lean_unbox(v___x_510_);
v_res_517_ = l_main___lam__0(v___x_501_, v___x_502_, v___x_35406__boxed_512_, v_importArts_504_, v___y_35407__boxed_513_, v___x_35408__boxed_514_, v_name_507_, v___x_35409__boxed_515_, v___x_509_, v___x_35411__boxed_516_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_main___lam__1(lean_object* v___x_521_, lean_object* v___x_522_, lean_object* v_head_523_, lean_object* v___x_524_, lean_object* v___x_525_, lean_object* v___x_526_, lean_object* v___x_527_, lean_object* v___x_528_, lean_object* v___x_529_, lean_object* v___x_530_, lean_object* v___x_531_, uint8_t v___x_532_, lean_object* v_name_533_, lean_object* v_a_534_, uint8_t v___x_535_, lean_object* v___x_536_){
_start:
{
lean_object* v_a_539_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; uint8_t v___x_547_; lean_object* v___y_549_; lean_object* v___x_581_; uint8_t v___y_583_; lean_object* v_env_603_; uint8_t v___x_604_; 
v___x_542_ = lean_io_get_num_heartbeats();
v___x_543_ = lean_st_mk_ref(v___x_521_);
v___x_544_ = l_Lean_inheritedTraceOptions;
v___x_545_ = lean_st_ref_get(v___x_544_);
v___x_546_ = l_Lean_diagnostics;
v___x_547_ = l_Lean_Option_get___at___00main_spec__8(v___x_522_, v___x_546_);
v___x_581_ = lean_st_ref_get(v___x_543_);
v_env_603_ = lean_ctor_get(v___x_581_, 0);
lean_inc_ref(v_env_603_);
lean_dec(v___x_581_);
v___x_604_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_603_);
lean_dec_ref(v_env_603_);
if (v___x_547_ == 0)
{
if (v___x_604_ == 0)
{
v___y_583_ = v___x_535_;
goto v___jp_582_;
}
else
{
v___y_583_ = v___x_547_;
goto v___jp_582_;
}
}
else
{
v___y_583_ = v___x_604_;
goto v___jp_582_;
}
v___jp_538_:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = lean_mk_io_user_error(v_a_539_);
v___x_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
return v___x_541_;
}
v___jp_548_:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_550_ = l_Lean_maxRecDepth;
v___x_551_ = l_Lean_Option_get___at___00main_spec__9(v___x_522_, v___x_550_);
lean_inc(v___x_525_);
v___x_552_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_552_, 0, v_head_523_);
lean_ctor_set(v___x_552_, 1, v___x_524_);
lean_ctor_set(v___x_552_, 2, v___x_522_);
lean_ctor_set(v___x_552_, 3, v___x_551_);
lean_ctor_set(v___x_552_, 4, v___x_525_);
lean_ctor_set(v___x_552_, 5, v___x_526_);
lean_ctor_set(v___x_552_, 6, v___x_542_);
lean_ctor_set(v___x_552_, 7, v___x_527_);
lean_ctor_set(v___x_552_, 8, v___x_525_);
lean_ctor_set(v___x_552_, 9, v___x_528_);
lean_ctor_set(v___x_552_, 10, v___x_529_);
lean_ctor_set(v___x_552_, 11, v___x_545_);
v___x_553_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_553_, 0, v___x_552_);
lean_ctor_set(v___x_553_, 1, v___x_530_);
lean_ctor_set(v___x_553_, 2, v___x_531_);
lean_ctor_set_uint8(v___x_553_, sizeof(void*)*3, v___x_547_);
lean_ctor_set_uint8(v___x_553_, sizeof(void*)*3 + 1, v___x_532_);
v___x_554_ = l_Lean_Compiler_LCNF_emitC(v_name_533_, v___x_553_, v___y_549_);
lean_dec(v___y_549_);
lean_dec_ref_known(v___x_553_, 3);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_a_555_);
lean_dec_ref_known(v___x_554_, 1);
v___x_556_ = lean_st_ref_get(v___x_543_);
lean_dec(v___x_543_);
lean_dec(v___x_556_);
v___x_557_ = lean_string_to_utf8(v_a_555_);
lean_dec(v_a_555_);
v___x_558_ = lean_io_prim_handle_write(v_a_534_, v___x_557_);
lean_dec_ref(v___x_557_);
return v___x_558_;
}
else
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_580_; 
lean_dec(v___x_543_);
v_a_559_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_580_ == 0)
{
v___x_561_ = v___x_554_;
v_isShared_562_ = v_isSharedCheck_580_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_554_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_580_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
if (lean_obj_tag(v_a_559_) == 0)
{
lean_object* v_msg_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_567_; 
v_msg_563_ = lean_ctor_get(v_a_559_, 1);
lean_inc_ref(v_msg_563_);
lean_dec_ref_known(v_a_559_, 2);
v___x_564_ = l_Lean_MessageData_toString(v_msg_563_);
v___x_565_ = lean_mk_io_user_error(v___x_564_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v___x_565_);
v___x_567_ = v___x_561_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_565_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
else
{
lean_object* v_id_569_; lean_object* v___x_570_; 
lean_del_object(v___x_561_);
v_id_569_ = lean_ctor_get(v_a_559_, 0);
lean_inc(v_id_569_);
lean_dec_ref_known(v_a_559_, 2);
v___x_570_ = l_Lean_InternalExceptionId_getName(v_id_569_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec(v_id_569_);
v_a_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_a_571_);
lean_dec_ref_known(v___x_570_, 1);
v___x_572_ = ((lean_object*)(l_main___lam__1___closed__0));
v___x_573_ = l_Lean_Name_toString(v_a_571_, v___x_535_);
v___x_574_ = lean_string_append(v___x_572_, v___x_573_);
lean_dec_ref(v___x_573_);
v_a_539_ = v___x_574_;
goto v___jp_538_;
}
else
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec_ref_known(v___x_570_, 1);
v___x_575_ = ((lean_object*)(l_main___lam__1___closed__1));
v___x_576_ = l_Nat_reprFast(v_id_569_);
v___x_577_ = lean_string_append(v___x_575_, v___x_576_);
lean_dec_ref(v___x_576_);
v___x_578_ = ((lean_object*)(l_main___lam__1___closed__2));
v___x_579_ = lean_string_append(v___x_577_, v___x_578_);
v_a_539_ = v___x_579_;
goto v___jp_538_;
}
}
}
}
}
v___jp_582_:
{
if (v___y_583_ == 0)
{
lean_object* v___x_584_; lean_object* v_env_585_; lean_object* v_nextMacroScope_586_; lean_object* v_ngen_587_; lean_object* v_auxDeclNGen_588_; lean_object* v_traceState_589_; lean_object* v_messages_590_; lean_object* v_infoState_591_; lean_object* v_snapshotTasks_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_601_; 
v___x_584_ = lean_st_ref_take(v___x_543_);
v_env_585_ = lean_ctor_get(v___x_584_, 0);
v_nextMacroScope_586_ = lean_ctor_get(v___x_584_, 1);
v_ngen_587_ = lean_ctor_get(v___x_584_, 2);
v_auxDeclNGen_588_ = lean_ctor_get(v___x_584_, 3);
v_traceState_589_ = lean_ctor_get(v___x_584_, 4);
v_messages_590_ = lean_ctor_get(v___x_584_, 6);
v_infoState_591_ = lean_ctor_get(v___x_584_, 7);
v_snapshotTasks_592_ = lean_ctor_get(v___x_584_, 8);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_601_ == 0)
{
lean_object* v_unused_602_; 
v_unused_602_ = lean_ctor_get(v___x_584_, 5);
lean_dec(v_unused_602_);
v___x_594_ = v___x_584_;
v_isShared_595_ = v_isSharedCheck_601_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_snapshotTasks_592_);
lean_inc(v_infoState_591_);
lean_inc(v_messages_590_);
lean_inc(v_traceState_589_);
lean_inc(v_auxDeclNGen_588_);
lean_inc(v_ngen_587_);
lean_inc(v_nextMacroScope_586_);
lean_inc(v_env_585_);
lean_dec(v___x_584_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_601_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; lean_object* v___x_598_; 
v___x_596_ = l_Lean_Kernel_enableDiag(v_env_585_, v___x_547_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 5, v___x_536_);
lean_ctor_set(v___x_594_, 0, v___x_596_);
v___x_598_ = v___x_594_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v_nextMacroScope_586_);
lean_ctor_set(v_reuseFailAlloc_600_, 2, v_ngen_587_);
lean_ctor_set(v_reuseFailAlloc_600_, 3, v_auxDeclNGen_588_);
lean_ctor_set(v_reuseFailAlloc_600_, 4, v_traceState_589_);
lean_ctor_set(v_reuseFailAlloc_600_, 5, v___x_536_);
lean_ctor_set(v_reuseFailAlloc_600_, 6, v_messages_590_);
lean_ctor_set(v_reuseFailAlloc_600_, 7, v_infoState_591_);
lean_ctor_set(v_reuseFailAlloc_600_, 8, v_snapshotTasks_592_);
v___x_598_ = v_reuseFailAlloc_600_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v___x_599_; 
v___x_599_ = lean_st_ref_put(v___x_543_, v___x_598_);
lean_inc(v___x_543_);
v___y_549_ = v___x_543_;
goto v___jp_548_;
}
}
}
else
{
lean_dec_ref(v___x_536_);
lean_inc(v___x_543_);
v___y_549_ = v___x_543_;
goto v___jp_548_;
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__1___boxed(lean_object** _args){
lean_object* v___x_605_ = _args[0];
lean_object* v___x_606_ = _args[1];
lean_object* v_head_607_ = _args[2];
lean_object* v___x_608_ = _args[3];
lean_object* v___x_609_ = _args[4];
lean_object* v___x_610_ = _args[5];
lean_object* v___x_611_ = _args[6];
lean_object* v___x_612_ = _args[7];
lean_object* v___x_613_ = _args[8];
lean_object* v___x_614_ = _args[9];
lean_object* v___x_615_ = _args[10];
lean_object* v___x_616_ = _args[11];
lean_object* v_name_617_ = _args[12];
lean_object* v_a_618_ = _args[13];
lean_object* v___x_619_ = _args[14];
lean_object* v___x_620_ = _args[15];
lean_object* v___y_621_ = _args[16];
_start:
{
uint8_t v___x_35499__boxed_622_; uint8_t v___x_35501__boxed_623_; lean_object* v_res_624_; 
v___x_35499__boxed_622_ = lean_unbox(v___x_616_);
v___x_35501__boxed_623_ = lean_unbox(v___x_619_);
v_res_624_ = l_main___lam__1(v___x_605_, v___x_606_, v_head_607_, v___x_608_, v___x_609_, v___x_610_, v___x_611_, v___x_612_, v___x_613_, v___x_614_, v___x_615_, v___x_35499__boxed_622_, v_name_617_, v_a_618_, v___x_35501__boxed_623_, v___x_620_);
lean_dec(v_a_618_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(lean_object* v_s_625_){
_start:
{
lean_object* v___x_627_; lean_object* v_putStr_628_; lean_object* v___x_629_; 
v___x_627_ = lean_get_stderr();
v_putStr_628_ = lean_ctor_get(v___x_627_, 4);
lean_inc_ref(v_putStr_628_);
lean_dec_ref(v___x_627_);
v___x_629_ = lean_apply_2(v_putStr_628_, v_s_625_, lean_box(0));
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8___boxed(lean_object* v_s_630_, lean_object* v_a_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v_s_630_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6(lean_object* v_s_633_){
_start:
{
uint32_t v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_635_ = 10;
v___x_636_ = lean_string_push(v_s_633_, v___x_635_);
v___x_637_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v___x_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6___boxed(lean_object* v_s_638_, lean_object* v_a_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_IO_eprintln___at___00main_spec__6(v_s_638_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(lean_object* v_o_644_, lean_object* v_k_645_, lean_object* v_v_646_){
_start:
{
lean_object* v_map_647_; uint8_t v_hasTrace_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_662_; 
v_map_647_ = lean_ctor_get(v_o_644_, 0);
v_hasTrace_648_ = lean_ctor_get_uint8(v_o_644_, sizeof(void*)*1);
v_isSharedCheck_662_ = !lean_is_exclusive(v_o_644_);
if (v_isSharedCheck_662_ == 0)
{
v___x_650_ = v_o_644_;
v_isShared_651_ = v_isSharedCheck_662_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_map_647_);
lean_dec(v_o_644_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_662_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_652_, 0, v_v_646_);
lean_inc(v_k_645_);
v___x_653_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_645_, v___x_652_, v_map_647_);
if (v_hasTrace_648_ == 0)
{
lean_object* v___x_654_; uint8_t v___x_655_; lean_object* v___x_657_; 
v___x_654_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_655_ = l_Lean_Name_isPrefixOf(v___x_654_, v_k_645_);
lean_dec(v_k_645_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 0, v___x_653_);
v___x_657_ = v___x_650_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_653_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
lean_ctor_set_uint8(v___x_657_, sizeof(void*)*1, v___x_655_);
return v___x_657_;
}
}
else
{
lean_object* v___x_660_; 
lean_dec(v_k_645_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 0, v___x_653_);
v___x_660_ = v___x_650_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_653_);
lean_ctor_set_uint8(v_reuseFailAlloc_661_, sizeof(void*)*1, v_hasTrace_648_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00main_spec__3(lean_object* v_opts_663_, lean_object* v_opt_664_, lean_object* v_val_665_){
_start:
{
lean_object* v_name_666_; lean_object* v___x_667_; 
v_name_666_ = lean_ctor_get(v_opt_664_, 0);
lean_inc(v_name_666_);
lean_dec_ref(v_opt_664_);
v___x_667_ = l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(v_opts_663_, v_name_666_, v_val_665_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(lean_object* v___y_669_, lean_object* v_as_670_, size_t v_i_671_, size_t v_stop_672_, lean_object* v_b_673_){
_start:
{
lean_object* v___y_675_; uint8_t v___x_679_; 
v___x_679_ = lean_usize_dec_eq(v_i_671_, v_stop_672_);
if (v___x_679_ == 0)
{
lean_object* v_fst_680_; lean_object* v_snd_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___y_685_; 
v_fst_680_ = lean_ctor_get(v_b_673_, 0);
v_snd_681_ = lean_ctor_get(v_b_673_, 1);
v___x_682_ = lean_array_uget_borrowed(v_as_670_, v_i_671_);
v___x_683_ = l_Lean_IR_Decl_name(v___x_682_);
if (lean_obj_tag(v___x_683_) == 1)
{
lean_object* v_pre_698_; lean_object* v_str_699_; lean_object* v___x_700_; uint8_t v___x_701_; 
v_pre_698_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_pre_698_);
v_str_699_ = lean_ctor_get(v___x_683_, 1);
lean_inc_ref(v_str_699_);
v___x_700_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___closed__0));
v___x_701_ = lean_string_dec_eq(v_str_699_, v___x_700_);
lean_dec_ref(v_str_699_);
if (v___x_701_ == 0)
{
lean_dec(v_pre_698_);
lean_inc_ref(v___x_683_);
v___y_685_ = v___x_683_;
goto v___jp_684_;
}
else
{
v___y_685_ = v_pre_698_;
goto v___jp_684_;
}
}
else
{
lean_inc(v___x_683_);
v___y_685_ = v___x_683_;
goto v___jp_684_;
}
v___jp_684_:
{
uint8_t v___x_686_; 
lean_inc_ref(v___y_669_);
v___x_686_ = l_Lean_isExtern(v___y_669_, v___y_685_);
if (v___x_686_ == 0)
{
lean_dec(v___x_683_);
v___y_675_ = v_b_673_;
goto v___jp_674_;
}
else
{
lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_695_; 
lean_inc(v_snd_681_);
lean_inc(v_fst_680_);
v_isSharedCheck_695_ = !lean_is_exclusive(v_b_673_);
if (v_isSharedCheck_695_ == 0)
{
lean_object* v_unused_696_; lean_object* v_unused_697_; 
v_unused_696_ = lean_ctor_get(v_b_673_, 1);
lean_dec(v_unused_696_);
v_unused_697_ = lean_ctor_get(v_b_673_, 0);
lean_dec(v_unused_697_);
v___x_688_ = v_b_673_;
v_isShared_689_ = v_isSharedCheck_695_;
goto v_resetjp_687_;
}
else
{
lean_dec(v_b_673_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_695_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_693_; 
lean_inc_n(v___x_682_, 2);
v___x_690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_682_);
lean_ctor_set(v___x_690_, 1, v_fst_680_);
v___x_691_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(v_snd_681_, v___x_683_, v___x_682_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 1, v___x_691_);
lean_ctor_set(v___x_688_, 0, v___x_690_);
v___x_693_ = v___x_688_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v___x_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
v___y_675_ = v___x_693_;
goto v___jp_674_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_669_);
return v_b_673_;
}
v___jp_674_:
{
size_t v___x_676_; size_t v___x_677_; 
v___x_676_ = ((size_t)1ULL);
v___x_677_ = lean_usize_add(v_i_671_, v___x_676_);
v_i_671_ = v___x_677_;
v_b_673_ = v___y_675_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___boxed(lean_object* v___y_702_, lean_object* v_as_703_, lean_object* v_i_704_, lean_object* v_stop_705_, lean_object* v_b_706_){
_start:
{
size_t v_i_boxed_707_; size_t v_stop_boxed_708_; lean_object* v_res_709_; 
v_i_boxed_707_ = lean_unbox_usize(v_i_704_);
lean_dec(v_i_704_);
v_stop_boxed_708_ = lean_unbox_usize(v_stop_705_);
lean_dec(v_stop_705_);
v_res_709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_702_, v_as_703_, v_i_boxed_707_, v_stop_boxed_708_, v_b_706_);
lean_dec_ref(v_as_703_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg(lean_object* v_as_x27_711_, lean_object* v_b_712_){
_start:
{
if (lean_obj_tag(v_as_x27_711_) == 0)
{
lean_object* v___x_714_; 
v___x_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_714_, 0, v_b_712_);
return v___x_714_;
}
else
{
lean_object* v_head_715_; lean_object* v_tail_716_; lean_object* v_fst_717_; lean_object* v_snd_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_743_; 
v_head_715_ = lean_ctor_get(v_as_x27_711_, 0);
v_tail_716_ = lean_ctor_get(v_as_x27_711_, 1);
v_fst_717_ = lean_ctor_get(v_b_712_, 0);
v_snd_718_ = lean_ctor_get(v_b_712_, 1);
v_isSharedCheck_743_ = !lean_is_exclusive(v_b_712_);
if (v_isSharedCheck_743_ == 0)
{
v___x_720_ = v_b_712_;
v_isShared_721_ = v_isSharedCheck_743_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_snd_718_);
lean_inc(v_fst_717_);
lean_dec(v_b_712_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_743_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_722_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0));
v___x_723_ = lean_string_dec_eq(v_head_715_, v___x_722_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; 
lean_inc(v_head_715_);
v___x_724_ = l___private_LeanIR_0__setConfigOption(v_snd_718_, v_head_715_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_727_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc(v_a_725_);
lean_dec_ref_known(v___x_724_, 1);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 1, v_a_725_);
v___x_727_ = v___x_720_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_fst_717_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_a_725_);
v___x_727_ = v_reuseFailAlloc_729_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
v_as_x27_711_ = v_tail_716_;
v_b_712_ = v___x_727_;
goto _start;
}
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_del_object(v___x_720_);
lean_dec(v_fst_717_);
v_a_730_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_724_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_724_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
else
{
lean_object* v___x_738_; lean_object* v___x_740_; 
lean_dec(v_fst_717_);
v___x_738_ = lean_box(v___x_723_);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 0, v___x_738_);
v___x_740_ = v___x_720_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_738_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_snd_718_);
v___x_740_ = v_reuseFailAlloc_742_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
v_as_x27_711_ = v_tail_716_;
v_b_712_ = v___x_740_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg___boxed(lean_object* v_as_x27_744_, lean_object* v_b_745_, lean_object* v___y_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_744_, v_b_745_);
lean_dec(v_as_x27_744_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(lean_object* v_as_748_, size_t v_i_749_, size_t v_stop_750_, lean_object* v_b_751_){
_start:
{
uint8_t v___x_752_; 
v___x_752_ = lean_usize_dec_eq(v_i_749_, v_stop_750_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; lean_object* v_toEnvExtension_754_; lean_object* v_asyncMode_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; size_t v___x_759_; size_t v___x_760_; 
v___x_753_ = l_Lean_Compiler_LCNF_impureSigExt;
v_toEnvExtension_754_ = lean_ctor_get(v___x_753_, 0);
v_asyncMode_755_ = lean_ctor_get(v_toEnvExtension_754_, 2);
v___x_756_ = lean_box(0);
v___x_757_ = lean_array_uget_borrowed(v_as_748_, v_i_749_);
lean_inc(v___x_757_);
v___x_758_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_753_, v_b_751_, v___x_757_, v_asyncMode_755_, v___x_756_);
v___x_759_ = ((size_t)1ULL);
v___x_760_ = lean_usize_add(v_i_749_, v___x_759_);
v_i_749_ = v___x_760_;
v_b_751_ = v___x_758_;
goto _start;
}
else
{
return v_b_751_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18___boxed(lean_object* v_as_762_, lean_object* v_i_763_, lean_object* v_stop_764_, lean_object* v_b_765_){
_start:
{
size_t v_i_boxed_766_; size_t v_stop_boxed_767_; lean_object* v_res_768_; 
v_i_boxed_766_ = lean_unbox_usize(v_i_763_);
lean_dec(v_i_763_);
v_stop_boxed_767_ = lean_unbox_usize(v_stop_764_);
lean_dec(v_stop_764_);
v_res_768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_as_762_, v_i_boxed_766_, v_stop_boxed_767_, v_b_765_);
lean_dec_ref(v_as_762_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(lean_object* v_as_772_, size_t v_sz_773_, size_t v_i_774_, lean_object* v_b_775_, lean_object* v___y_776_){
_start:
{
uint8_t v___x_778_; 
v___x_778_ = lean_usize_dec_lt(v_i_774_, v_sz_773_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; 
v___x_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_779_, 0, v_b_775_);
return v___x_779_;
}
else
{
uint8_t v___x_780_; lean_object* v_a_781_; lean_object* v___x_782_; lean_object* v_ref_783_; lean_object* v___x_784_; 
lean_dec_ref(v_b_775_);
v___x_780_ = 0;
v_a_781_ = lean_array_uget_borrowed(v_as_772_, v_i_774_);
lean_inc(v_a_781_);
v___x_782_ = l_Lean_Message_toString(v_a_781_, v___x_780_);
v_ref_783_ = lean_ctor_get(v___y_776_, 2);
v___x_784_ = l_IO_eprintln___at___00main_spec__6(v___x_782_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v___x_785_; size_t v___x_786_; size_t v___x_787_; 
lean_dec_ref_known(v___x_784_, 1);
v___x_785_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_786_ = ((size_t)1ULL);
v___x_787_ = lean_usize_add(v_i_774_, v___x_786_);
v_i_774_ = v___x_787_;
v_b_775_ = v___x_785_;
goto _start;
}
else
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_800_; 
v_a_789_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_800_ == 0)
{
v___x_791_ = v___x_784_;
v_isShared_792_ = v_isSharedCheck_800_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_784_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_800_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_798_; 
v___x_793_ = lean_io_error_to_string(v_a_789_);
v___x_794_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
v___x_795_ = l_Lean_MessageData_ofFormat(v___x_794_);
lean_inc(v_ref_783_);
v___x_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_796_, 0, v_ref_783_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v___x_796_);
v___x_798_ = v___x_791_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_796_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___boxed(lean_object* v_as_801_, lean_object* v_sz_802_, lean_object* v_i_803_, lean_object* v_b_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
size_t v_sz_boxed_807_; size_t v_i_boxed_808_; lean_object* v_res_809_; 
v_sz_boxed_807_ = lean_unbox_usize(v_sz_802_);
lean_dec(v_sz_802_);
v_i_boxed_808_ = lean_unbox_usize(v_i_803_);
lean_dec(v_i_803_);
v_res_809_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_801_, v_sz_boxed_807_, v_i_boxed_808_, v_b_804_, v___y_805_);
lean_dec_ref(v___y_805_);
lean_dec_ref(v_as_801_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(lean_object* v_as_810_, size_t v_sz_811_, size_t v_i_812_, lean_object* v_b_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
uint8_t v___x_817_; 
v___x_817_ = lean_usize_dec_lt(v_i_812_, v_sz_811_);
if (v___x_817_ == 0)
{
lean_object* v___x_818_; 
v___x_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_818_, 0, v_b_813_);
return v___x_818_;
}
else
{
uint8_t v___x_819_; lean_object* v_a_820_; lean_object* v___x_821_; lean_object* v_ref_822_; lean_object* v___x_823_; 
lean_dec_ref(v_b_813_);
v___x_819_ = 0;
v_a_820_ = lean_array_uget_borrowed(v_as_810_, v_i_812_);
lean_inc(v_a_820_);
v___x_821_ = l_Lean_Message_toString(v_a_820_, v___x_819_);
v_ref_822_ = lean_ctor_get(v___y_814_, 2);
v___x_823_ = l_IO_eprintln___at___00main_spec__6(v___x_821_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v___x_824_; size_t v___x_825_; size_t v___x_826_; lean_object* v___x_827_; 
lean_dec_ref_known(v___x_823_, 1);
v___x_824_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_825_ = ((size_t)1ULL);
v___x_826_ = lean_usize_add(v_i_812_, v___x_825_);
v___x_827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_810_, v_sz_811_, v___x_826_, v___x_824_, v___y_814_);
return v___x_827_;
}
else
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_839_; 
v_a_828_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_839_ == 0)
{
v___x_830_ = v___x_823_;
v_isShared_831_ = v_isSharedCheck_839_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_823_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_839_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_837_; 
v___x_832_ = lean_io_error_to_string(v_a_828_);
v___x_833_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
v___x_834_ = l_Lean_MessageData_ofFormat(v___x_833_);
lean_inc(v_ref_822_);
v___x_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_835_, 0, v_ref_822_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_835_);
v___x_837_ = v___x_830_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_835_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27___boxed(lean_object* v_as_840_, lean_object* v_sz_841_, lean_object* v_i_842_, lean_object* v_b_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
size_t v_sz_boxed_847_; size_t v_i_boxed_848_; lean_object* v_res_849_; 
v_sz_boxed_847_ = lean_unbox_usize(v_sz_841_);
lean_dec(v_sz_841_);
v_i_boxed_848_ = lean_unbox_usize(v_i_842_);
lean_dec(v_i_842_);
v_res_849_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(v_as_840_, v_sz_boxed_847_, v_i_boxed_848_, v_b_843_, v___y_844_, v___y_845_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec_ref(v_as_840_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(lean_object* v_as_853_, size_t v_sz_854_, size_t v_i_855_, lean_object* v_b_856_, lean_object* v___y_857_){
_start:
{
uint8_t v___x_859_; 
v___x_859_ = lean_usize_dec_lt(v_i_855_, v_sz_854_);
if (v___x_859_ == 0)
{
lean_object* v___x_860_; 
v___x_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_860_, 0, v_b_856_);
return v___x_860_;
}
else
{
uint8_t v___x_861_; lean_object* v_a_862_; lean_object* v___x_863_; lean_object* v_ref_864_; lean_object* v___x_865_; 
lean_dec_ref(v_b_856_);
v___x_861_ = 0;
v_a_862_ = lean_array_uget_borrowed(v_as_853_, v_i_855_);
lean_inc(v_a_862_);
v___x_863_ = l_Lean_Message_toString(v_a_862_, v___x_861_);
v_ref_864_ = lean_ctor_get(v___y_857_, 2);
v___x_865_ = l_IO_eprintln___at___00main_spec__6(v___x_863_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v___x_866_; size_t v___x_867_; size_t v___x_868_; 
lean_dec_ref_known(v___x_865_, 1);
v___x_866_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_867_ = ((size_t)1ULL);
v___x_868_ = lean_usize_add(v_i_855_, v___x_867_);
v_i_855_ = v___x_868_;
v_b_856_ = v___x_866_;
goto _start;
}
else
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_881_; 
v_a_870_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_881_ == 0)
{
v___x_872_ = v___x_865_;
v_isShared_873_ = v_isSharedCheck_881_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_865_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_881_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_879_; 
v___x_874_ = lean_io_error_to_string(v_a_870_);
v___x_875_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
v___x_876_ = l_Lean_MessageData_ofFormat(v___x_875_);
lean_inc(v_ref_864_);
v___x_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_877_, 0, v_ref_864_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v___x_877_);
v___x_879_ = v___x_872_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___boxed(lean_object* v_as_882_, lean_object* v_sz_883_, lean_object* v_i_884_, lean_object* v_b_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
size_t v_sz_boxed_888_; size_t v_i_boxed_889_; lean_object* v_res_890_; 
v_sz_boxed_888_ = lean_unbox_usize(v_sz_883_);
lean_dec(v_sz_883_);
v_i_boxed_889_ = lean_unbox_usize(v_i_884_);
lean_dec(v_i_884_);
v_res_890_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_882_, v_sz_boxed_888_, v_i_boxed_889_, v_b_885_, v___y_886_);
lean_dec_ref(v___y_886_);
lean_dec_ref(v_as_882_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(lean_object* v_as_891_, size_t v_sz_892_, size_t v_i_893_, lean_object* v_b_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
uint8_t v___x_898_; 
v___x_898_ = lean_usize_dec_lt(v_i_893_, v_sz_892_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; 
v___x_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_899_, 0, v_b_894_);
return v___x_899_;
}
else
{
uint8_t v___x_900_; lean_object* v_a_901_; lean_object* v___x_902_; lean_object* v_ref_903_; lean_object* v___x_904_; 
lean_dec_ref(v_b_894_);
v___x_900_ = 0;
v_a_901_ = lean_array_uget_borrowed(v_as_891_, v_i_893_);
lean_inc(v_a_901_);
v___x_902_ = l_Lean_Message_toString(v_a_901_, v___x_900_);
v_ref_903_ = lean_ctor_get(v___y_895_, 2);
v___x_904_ = l_IO_eprintln___at___00main_spec__6(v___x_902_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v___x_905_; size_t v___x_906_; size_t v___x_907_; lean_object* v___x_908_; 
lean_dec_ref_known(v___x_904_, 1);
v___x_905_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_906_ = ((size_t)1ULL);
v___x_907_ = lean_usize_add(v_i_893_, v___x_906_);
v___x_908_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_891_, v_sz_892_, v___x_907_, v___x_905_, v___y_895_);
return v___x_908_;
}
else
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_920_; 
v_a_909_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_920_ == 0)
{
v___x_911_ = v___x_904_;
v_isShared_912_ = v_isSharedCheck_920_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_904_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_920_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_918_; 
v___x_913_ = lean_io_error_to_string(v_a_909_);
v___x_914_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
v___x_915_ = l_Lean_MessageData_ofFormat(v___x_914_);
lean_inc(v_ref_903_);
v___x_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_916_, 0, v_ref_903_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v___x_916_);
v___x_918_ = v___x_911_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_916_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38___boxed(lean_object* v_as_921_, lean_object* v_sz_922_, lean_object* v_i_923_, lean_object* v_b_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
size_t v_sz_boxed_928_; size_t v_i_boxed_929_; lean_object* v_res_930_; 
v_sz_boxed_928_ = lean_unbox_usize(v_sz_922_);
lean_dec(v_sz_922_);
v_i_boxed_929_ = lean_unbox_usize(v_i_923_);
lean_dec(v_i_923_);
v_res_930_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(v_as_921_, v_sz_boxed_928_, v_i_boxed_929_, v_b_924_, v___y_925_, v___y_926_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec_ref(v_as_921_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(lean_object* v_init_931_, lean_object* v_n_932_, lean_object* v_b_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
if (lean_obj_tag(v_n_932_) == 0)
{
lean_object* v_cs_937_; lean_object* v___x_938_; lean_object* v___x_939_; size_t v_sz_940_; size_t v___x_941_; lean_object* v___x_942_; 
v_cs_937_ = lean_ctor_get(v_n_932_, 0);
v___x_938_ = lean_box(0);
v___x_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
lean_ctor_set(v___x_939_, 1, v_b_933_);
v_sz_940_ = lean_array_size(v_cs_937_);
v___x_941_ = ((size_t)0ULL);
v___x_942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(v_init_931_, v_cs_937_, v_sz_940_, v___x_941_, v___x_939_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_957_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_957_ == 0)
{
v___x_945_ = v___x_942_;
v_isShared_946_ = v_isSharedCheck_957_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_942_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_957_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v_fst_947_; 
v_fst_947_ = lean_ctor_get(v_a_943_, 0);
if (lean_obj_tag(v_fst_947_) == 0)
{
lean_object* v_snd_948_; lean_object* v___x_949_; lean_object* v___x_951_; 
v_snd_948_ = lean_ctor_get(v_a_943_, 1);
lean_inc(v_snd_948_);
lean_dec(v_a_943_);
v___x_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_949_, 0, v_snd_948_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v___x_949_);
v___x_951_ = v___x_945_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_949_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
else
{
lean_object* v_val_953_; lean_object* v___x_955_; 
lean_inc_ref(v_fst_947_);
lean_dec(v_a_943_);
v_val_953_ = lean_ctor_get(v_fst_947_, 0);
lean_inc(v_val_953_);
lean_dec_ref_known(v_fst_947_, 1);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v_val_953_);
v___x_955_ = v___x_945_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_val_953_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
v_a_958_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_942_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_942_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
else
{
lean_object* v_vs_966_; lean_object* v___x_967_; lean_object* v___x_968_; size_t v_sz_969_; size_t v___x_970_; lean_object* v___x_971_; 
v_vs_966_ = lean_ctor_get(v_n_932_, 0);
v___x_967_ = lean_box(0);
v___x_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
lean_ctor_set(v___x_968_, 1, v_b_933_);
v_sz_969_ = lean_array_size(v_vs_966_);
v___x_970_ = ((size_t)0ULL);
v___x_971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(v_vs_966_, v_sz_969_, v___x_970_, v___x_968_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_986_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_986_ == 0)
{
v___x_974_ = v___x_971_;
v_isShared_975_ = v_isSharedCheck_986_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_971_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_986_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v_fst_976_; 
v_fst_976_ = lean_ctor_get(v_a_972_, 0);
if (lean_obj_tag(v_fst_976_) == 0)
{
lean_object* v_snd_977_; lean_object* v___x_978_; lean_object* v___x_980_; 
v_snd_977_ = lean_ctor_get(v_a_972_, 1);
lean_inc(v_snd_977_);
lean_dec(v_a_972_);
v___x_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_978_, 0, v_snd_977_);
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 0, v___x_978_);
v___x_980_ = v___x_974_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_978_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
else
{
lean_object* v_val_982_; lean_object* v___x_984_; 
lean_inc_ref(v_fst_976_);
lean_dec(v_a_972_);
v_val_982_ = lean_ctor_get(v_fst_976_, 0);
lean_inc(v_val_982_);
lean_dec_ref_known(v_fst_976_, 1);
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 0, v_val_982_);
v___x_984_ = v___x_974_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_val_982_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
else
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
v_a_987_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v___x_971_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_971_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_a_987_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(lean_object* v_init_995_, lean_object* v_as_996_, size_t v_sz_997_, size_t v_i_998_, lean_object* v_b_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
uint8_t v___x_1003_; 
v___x_1003_ = lean_usize_dec_lt(v_i_998_, v_sz_997_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; 
v___x_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1004_, 0, v_b_999_);
return v___x_1004_;
}
else
{
lean_object* v_snd_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1039_; 
v_snd_1005_ = lean_ctor_get(v_b_999_, 1);
v_isSharedCheck_1039_ = !lean_is_exclusive(v_b_999_);
if (v_isSharedCheck_1039_ == 0)
{
lean_object* v_unused_1040_; 
v_unused_1040_ = lean_ctor_get(v_b_999_, 0);
lean_dec(v_unused_1040_);
v___x_1007_ = v_b_999_;
v_isShared_1008_ = v_isSharedCheck_1039_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_snd_1005_);
lean_dec(v_b_999_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1039_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1009_; lean_object* v_a_1010_; lean_object* v___x_1011_; 
v___x_1009_ = lean_box(0);
v_a_1010_ = lean_array_uget_borrowed(v_as_996_, v_i_998_);
lean_inc(v_snd_1005_);
v___x_1011_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_995_, v_a_1010_, v_snd_1005_, v___y_1000_, v___y_1001_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1030_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1014_ = v___x_1011_;
v_isShared_1015_ = v_isSharedCheck_1030_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_1011_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1030_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
if (lean_obj_tag(v_a_1012_) == 0)
{
lean_object* v___x_1016_; lean_object* v___x_1018_; 
v___x_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1016_, 0, v_a_1012_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 0, v___x_1016_);
v___x_1018_ = v___x_1007_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1016_);
lean_ctor_set(v_reuseFailAlloc_1022_, 1, v_snd_1005_);
v___x_1018_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
lean_object* v___x_1020_; 
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 0, v___x_1018_);
v___x_1020_ = v___x_1014_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1018_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; 
lean_del_object(v___x_1014_);
lean_dec(v_snd_1005_);
v_a_1023_ = lean_ctor_get(v_a_1012_, 0);
lean_inc(v_a_1023_);
lean_dec_ref_known(v_a_1012_, 1);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 1, v_a_1023_);
lean_ctor_set(v___x_1007_, 0, v___x_1009_);
v___x_1025_ = v___x_1007_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1009_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_a_1023_);
v___x_1025_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
size_t v___x_1026_; size_t v___x_1027_; 
v___x_1026_ = ((size_t)1ULL);
v___x_1027_ = lean_usize_add(v_i_998_, v___x_1026_);
v_i_998_ = v___x_1027_;
v_b_999_ = v___x_1025_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
lean_del_object(v___x_1007_);
lean_dec(v_snd_1005_);
v_a_1031_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_1011_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1011_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37___boxed(lean_object* v_init_1041_, lean_object* v_as_1042_, lean_object* v_sz_1043_, lean_object* v_i_1044_, lean_object* v_b_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
size_t v_sz_boxed_1049_; size_t v_i_boxed_1050_; lean_object* v_res_1051_; 
v_sz_boxed_1049_ = lean_unbox_usize(v_sz_1043_);
lean_dec(v_sz_1043_);
v_i_boxed_1050_ = lean_unbox_usize(v_i_1044_);
lean_dec(v_i_1044_);
v_res_1051_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(v_init_1041_, v_as_1042_, v_sz_boxed_1049_, v_i_boxed_1050_, v_b_1045_, v___y_1046_, v___y_1047_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec_ref(v_as_1042_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26___boxed(lean_object* v_init_1052_, lean_object* v_n_1053_, lean_object* v_b_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_1052_, v_n_1053_, v_b_1054_, v___y_1055_, v___y_1056_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec_ref(v_n_1053_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__12(lean_object* v_t_1059_, lean_object* v_init_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v_root_1064_; lean_object* v_tail_1065_; lean_object* v___x_1066_; 
v_root_1064_ = lean_ctor_get(v_t_1059_, 0);
v_tail_1065_ = lean_ctor_get(v_t_1059_, 1);
v___x_1066_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_1060_, v_root_1064_, v_init_1060_, v___y_1061_, v___y_1062_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1103_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1069_ = v___x_1066_;
v_isShared_1070_ = v_isSharedCheck_1103_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1066_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1103_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
if (lean_obj_tag(v_a_1067_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1073_; 
v_a_1071_ = lean_ctor_get(v_a_1067_, 0);
lean_inc(v_a_1071_);
lean_dec_ref_known(v_a_1067_, 1);
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 0, v_a_1071_);
v___x_1073_ = v___x_1069_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1071_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; size_t v_sz_1078_; size_t v___x_1079_; lean_object* v___x_1080_; 
lean_del_object(v___x_1069_);
v_a_1075_ = lean_ctor_get(v_a_1067_, 0);
lean_inc(v_a_1075_);
lean_dec_ref_known(v_a_1067_, 1);
v___x_1076_ = lean_box(0);
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
lean_ctor_set(v___x_1077_, 1, v_a_1075_);
v_sz_1078_ = lean_array_size(v_tail_1065_);
v___x_1079_ = ((size_t)0ULL);
v___x_1080_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(v_tail_1065_, v_sz_1078_, v___x_1079_, v___x_1077_, v___y_1061_, v___y_1062_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1094_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1083_ = v___x_1080_;
v_isShared_1084_ = v_isSharedCheck_1094_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1080_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1094_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v_fst_1085_; 
v_fst_1085_ = lean_ctor_get(v_a_1081_, 0);
if (lean_obj_tag(v_fst_1085_) == 0)
{
lean_object* v_snd_1086_; lean_object* v___x_1088_; 
v_snd_1086_ = lean_ctor_get(v_a_1081_, 1);
lean_inc(v_snd_1086_);
lean_dec(v_a_1081_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v_snd_1086_);
v___x_1088_ = v___x_1083_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_snd_1086_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
else
{
lean_object* v_val_1090_; lean_object* v___x_1092_; 
lean_inc_ref(v_fst_1085_);
lean_dec(v_a_1081_);
v_val_1090_ = lean_ctor_get(v_fst_1085_, 0);
lean_inc(v_val_1090_);
lean_dec_ref_known(v_fst_1085_, 1);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v_val_1090_);
v___x_1092_ = v___x_1083_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_val_1090_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
v_a_1095_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1080_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1080_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
}
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
v_a_1104_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1066_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1066_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__12___boxed(lean_object* v_t_1112_, lean_object* v_init_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_PersistentArray_forIn___at___00main_spec__12(v_t_1112_, v_init_1113_, v___y_1114_, v___y_1115_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec_ref(v_t_1112_);
return v_res_1117_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0(uint8_t v_suppressElabErrors_1125_, uint8_t v___x_1126_, lean_object* v___x_1127_, lean_object* v_x_1128_){
_start:
{
if (lean_obj_tag(v_x_1128_) == 1)
{
lean_object* v_pre_1129_; 
v_pre_1129_ = lean_ctor_get(v_x_1128_, 0);
switch(lean_obj_tag(v_pre_1129_))
{
case 1:
{
lean_object* v_pre_1130_; 
v_pre_1130_ = lean_ctor_get(v_pre_1129_, 0);
switch(lean_obj_tag(v_pre_1130_))
{
case 0:
{
lean_object* v_str_1131_; lean_object* v_str_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; 
v_str_1131_ = lean_ctor_get(v_x_1128_, 1);
v_str_1132_ = lean_ctor_get(v_pre_1129_, 1);
v___x_1133_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0));
v___x_1134_ = lean_string_dec_eq(v_str_1132_, v___x_1133_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___x_1135_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1));
v___x_1136_ = lean_string_dec_eq(v_str_1132_, v___x_1135_);
if (v___x_1136_ == 0)
{
return v___x_1136_;
}
else
{
lean_object* v___x_1137_; uint8_t v___x_1138_; 
v___x_1137_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2));
v___x_1138_ = lean_string_dec_eq(v_str_1131_, v___x_1137_);
if (v___x_1138_ == 0)
{
return v___x_1138_;
}
else
{
return v_suppressElabErrors_1125_;
}
}
}
else
{
lean_object* v___x_1139_; uint8_t v___x_1140_; 
v___x_1139_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3));
v___x_1140_ = lean_string_dec_eq(v_str_1131_, v___x_1139_);
if (v___x_1140_ == 0)
{
return v___x_1140_;
}
else
{
return v_suppressElabErrors_1125_;
}
}
}
case 1:
{
lean_object* v_pre_1141_; 
v_pre_1141_ = lean_ctor_get(v_pre_1130_, 0);
if (lean_obj_tag(v_pre_1141_) == 0)
{
lean_object* v_str_1142_; lean_object* v_str_1143_; lean_object* v_str_1144_; lean_object* v___x_1145_; uint8_t v___x_1146_; 
v_str_1142_ = lean_ctor_get(v_x_1128_, 1);
v_str_1143_ = lean_ctor_get(v_pre_1129_, 1);
v_str_1144_ = lean_ctor_get(v_pre_1130_, 1);
v___x_1145_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4));
v___x_1146_ = lean_string_dec_eq(v_str_1144_, v___x_1145_);
if (v___x_1146_ == 0)
{
return v___x_1146_;
}
else
{
lean_object* v___x_1147_; uint8_t v___x_1148_; 
v___x_1147_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5));
v___x_1148_ = lean_string_dec_eq(v_str_1143_, v___x_1147_);
if (v___x_1148_ == 0)
{
return v___x_1148_;
}
else
{
lean_object* v___x_1149_; uint8_t v___x_1150_; 
v___x_1149_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6));
v___x_1150_ = lean_string_dec_eq(v_str_1142_, v___x_1149_);
if (v___x_1150_ == 0)
{
return v___x_1150_;
}
else
{
return v_suppressElabErrors_1125_;
}
}
}
}
else
{
return v___x_1126_;
}
}
default: 
{
return v___x_1126_;
}
}
}
case 0:
{
lean_object* v_str_1151_; uint8_t v___x_1152_; 
v_str_1151_ = lean_ctor_get(v_x_1128_, 1);
v___x_1152_ = lean_string_dec_eq(v_str_1151_, v___x_1127_);
if (v___x_1152_ == 0)
{
return v___x_1152_;
}
else
{
return v_suppressElabErrors_1125_;
}
}
default: 
{
return v___x_1126_;
}
}
}
else
{
return v___x_1126_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___boxed(lean_object* v_suppressElabErrors_1153_, lean_object* v___x_1154_, lean_object* v___x_1155_, lean_object* v_x_1156_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1157_; uint8_t v___x_36387__boxed_1158_; uint8_t v_res_1159_; lean_object* v_r_1160_; 
v_suppressElabErrors_boxed_1157_ = lean_unbox(v_suppressElabErrors_1153_);
v___x_36387__boxed_1158_ = lean_unbox(v___x_1154_);
v_res_1159_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0(v_suppressElabErrors_boxed_1157_, v___x_36387__boxed_1158_, v___x_1155_, v_x_1156_);
lean_dec(v_x_1156_);
lean_dec_ref(v___x_1155_);
v_r_1160_ = lean_box(v_res_1159_);
return v_r_1160_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0(void){
_start:
{
lean_object* v___x_1161_; double v___x_1162_; 
v___x_1161_ = lean_unsigned_to_nat(0u);
v___x_1162_ = lean_float_of_nat(v___x_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(uint8_t v___x_1164_, lean_object* v_as_1165_, size_t v_sz_1166_, size_t v_i_1167_, lean_object* v_b_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_a_1173_; uint8_t v___x_1177_; 
v___x_1177_ = lean_usize_dec_lt(v_i_1167_, v_sz_1166_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; 
v___x_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1178_, 0, v_b_1168_);
return v___x_1178_;
}
else
{
lean_object* v_a_1179_; lean_object* v_fst_1180_; lean_object* v_snd_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1259_; 
v_a_1179_ = lean_array_uget(v_as_1165_, v_i_1167_);
v_fst_1180_ = lean_ctor_get(v_a_1179_, 0);
v_snd_1181_ = lean_ctor_get(v_a_1179_, 1);
v_isSharedCheck_1259_ = !lean_is_exclusive(v_a_1179_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1183_ = v_a_1179_;
v_isShared_1184_ = v_isSharedCheck_1259_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_snd_1181_);
lean_inc(v_fst_1180_);
lean_dec(v_a_1179_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1259_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v_fst_1185_; lean_object* v_snd_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1258_; 
v_fst_1185_ = lean_ctor_get(v_fst_1180_, 0);
v_snd_1186_ = lean_ctor_get(v_fst_1180_, 1);
v_isSharedCheck_1258_ = !lean_is_exclusive(v_fst_1180_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1188_ = v_fst_1180_;
v_isShared_1189_ = v_isSharedCheck_1258_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_snd_1186_);
lean_inc(v_fst_1185_);
lean_dec(v_fst_1180_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1258_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; double v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v_toCold_1195_; uint8_t v_suppressElabErrors_1196_; lean_object* v_fileName_1197_; lean_object* v_fileMap_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1205_; 
v___x_1190_ = lean_box(0);
v___x_1191_ = lean_box(0);
v___x_1192_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0);
v___x_1193_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1));
v___x_1194_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1194_, 0, v___x_1190_);
lean_ctor_set(v___x_1194_, 1, v___x_1191_);
lean_ctor_set(v___x_1194_, 2, v___x_1193_);
lean_ctor_set_float(v___x_1194_, sizeof(void*)*3, v___x_1192_);
lean_ctor_set_float(v___x_1194_, sizeof(void*)*3 + 8, v___x_1192_);
lean_ctor_set_uint8(v___x_1194_, sizeof(void*)*3 + 16, v___x_1177_);
v_toCold_1195_ = lean_ctor_get(v___y_1169_, 0);
v_suppressElabErrors_1196_ = lean_ctor_get_uint8(v___y_1169_, sizeof(void*)*3 + 1);
v_fileName_1197_ = lean_ctor_get(v_toCold_1195_, 0);
v_fileMap_1198_ = lean_ctor_get(v_toCold_1195_, 1);
v___x_1199_ = lean_box(0);
v___x_1200_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_1201_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_1202_ = l_Lean_MessageData_nil;
v___x_1203_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1194_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
lean_ctor_set(v___x_1203_, 2, v_snd_1181_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set_tag(v___x_1188_, 8);
lean_ctor_set(v___x_1188_, 1, v___x_1203_);
lean_ctor_set(v___x_1188_, 0, v___x_1201_);
v___x_1205_ = v___x_1188_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1201_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
uint8_t v___x_1206_; lean_object* v___x_1207_; lean_object* v___y_1209_; lean_object* v___y_1210_; 
v___x_1206_ = 0;
lean_inc_ref(v_fileMap_1198_);
lean_inc_ref(v_fileName_1197_);
v___x_1207_ = l_Lean_Elab_mkMessageCore(v_fileName_1197_, v_fileMap_1198_, v___x_1205_, v___x_1206_, v_fst_1185_, v_snd_1186_);
lean_dec(v_snd_1186_);
lean_dec(v_fst_1185_);
if (v_suppressElabErrors_1196_ == 0)
{
v___y_1209_ = v___y_1169_;
v___y_1210_ = v___y_1170_;
goto v___jp_1208_;
}
else
{
lean_object* v_data_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___f_1255_; uint8_t v___x_1256_; 
v_data_1252_ = lean_ctor_get(v___x_1207_, 4);
lean_inc(v_data_1252_);
v___x_1253_ = lean_box(v_suppressElabErrors_1196_);
v___x_1254_ = lean_box(v___x_1164_);
v___f_1255_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1255_, 0, v___x_1253_);
lean_closure_set(v___f_1255_, 1, v___x_1254_);
lean_closure_set(v___f_1255_, 2, v___x_1200_);
v___x_1256_ = l_Lean_MessageData_hasTag(v___f_1255_, v_data_1252_);
if (v___x_1256_ == 0)
{
lean_dec_ref(v___x_1207_);
lean_del_object(v___x_1183_);
v_a_1173_ = v___x_1199_;
goto v___jp_1172_;
}
else
{
v___y_1209_ = v___y_1169_;
v___y_1210_ = v___y_1170_;
goto v___jp_1208_;
}
}
v___jp_1208_:
{
lean_object* v_toCold_1211_; lean_object* v_fileName_1212_; lean_object* v_pos_1213_; lean_object* v_endPos_1214_; uint8_t v_keepFullRange_1215_; uint8_t v_severity_1216_; uint8_t v_isSilent_1217_; lean_object* v_caption_1218_; lean_object* v_data_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1251_; 
v_toCold_1211_ = lean_ctor_get(v___y_1209_, 0);
v_fileName_1212_ = lean_ctor_get(v___x_1207_, 0);
v_pos_1213_ = lean_ctor_get(v___x_1207_, 1);
v_endPos_1214_ = lean_ctor_get(v___x_1207_, 2);
v_keepFullRange_1215_ = lean_ctor_get_uint8(v___x_1207_, sizeof(void*)*5);
v_severity_1216_ = lean_ctor_get_uint8(v___x_1207_, sizeof(void*)*5 + 1);
v_isSilent_1217_ = lean_ctor_get_uint8(v___x_1207_, sizeof(void*)*5 + 2);
v_caption_1218_ = lean_ctor_get(v___x_1207_, 3);
v_data_1219_ = lean_ctor_get(v___x_1207_, 4);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1221_ = v___x_1207_;
v_isShared_1222_ = v_isSharedCheck_1251_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_data_1219_);
lean_inc(v_caption_1218_);
lean_inc(v_endPos_1214_);
lean_inc(v_pos_1213_);
lean_inc(v_fileName_1212_);
lean_dec(v___x_1207_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1251_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v_currNamespace_1223_; lean_object* v_openDecls_1224_; lean_object* v___x_1226_; 
v_currNamespace_1223_ = lean_ctor_get(v_toCold_1211_, 4);
v_openDecls_1224_ = lean_ctor_get(v_toCold_1211_, 5);
lean_inc(v_openDecls_1224_);
lean_inc(v_currNamespace_1223_);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 1, v_openDecls_1224_);
lean_ctor_set(v___x_1183_, 0, v_currNamespace_1223_);
v___x_1226_ = v___x_1183_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_currNamespace_1223_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_openDecls_1224_);
v___x_1226_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
lean_object* v___x_1227_; lean_object* v___x_1229_; 
v___x_1227_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
lean_ctor_set(v___x_1227_, 1, v_data_1219_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 4, v___x_1227_);
v___x_1229_ = v___x_1221_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_fileName_1212_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v_pos_1213_);
lean_ctor_set(v_reuseFailAlloc_1249_, 2, v_endPos_1214_);
lean_ctor_set(v_reuseFailAlloc_1249_, 3, v_caption_1218_);
lean_ctor_set(v_reuseFailAlloc_1249_, 4, v___x_1227_);
lean_ctor_set_uint8(v_reuseFailAlloc_1249_, sizeof(void*)*5, v_keepFullRange_1215_);
lean_ctor_set_uint8(v_reuseFailAlloc_1249_, sizeof(void*)*5 + 1, v_severity_1216_);
lean_ctor_set_uint8(v_reuseFailAlloc_1249_, sizeof(void*)*5 + 2, v_isSilent_1217_);
v___x_1229_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
lean_object* v___x_1230_; lean_object* v_env_1231_; lean_object* v_nextMacroScope_1232_; lean_object* v_ngen_1233_; lean_object* v_auxDeclNGen_1234_; lean_object* v_traceState_1235_; lean_object* v_cache_1236_; lean_object* v_messages_1237_; lean_object* v_infoState_1238_; lean_object* v_snapshotTasks_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1248_; 
v___x_1230_ = lean_st_ref_take(v___y_1210_);
v_env_1231_ = lean_ctor_get(v___x_1230_, 0);
v_nextMacroScope_1232_ = lean_ctor_get(v___x_1230_, 1);
v_ngen_1233_ = lean_ctor_get(v___x_1230_, 2);
v_auxDeclNGen_1234_ = lean_ctor_get(v___x_1230_, 3);
v_traceState_1235_ = lean_ctor_get(v___x_1230_, 4);
v_cache_1236_ = lean_ctor_get(v___x_1230_, 5);
v_messages_1237_ = lean_ctor_get(v___x_1230_, 6);
v_infoState_1238_ = lean_ctor_get(v___x_1230_, 7);
v_snapshotTasks_1239_ = lean_ctor_get(v___x_1230_, 8);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1241_ = v___x_1230_;
v_isShared_1242_ = v_isSharedCheck_1248_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_snapshotTasks_1239_);
lean_inc(v_infoState_1238_);
lean_inc(v_messages_1237_);
lean_inc(v_cache_1236_);
lean_inc(v_traceState_1235_);
lean_inc(v_auxDeclNGen_1234_);
lean_inc(v_ngen_1233_);
lean_inc(v_nextMacroScope_1232_);
lean_inc(v_env_1231_);
lean_dec(v___x_1230_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1248_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1243_; lean_object* v___x_1245_; 
v___x_1243_ = l_Lean_MessageLog_add(v___x_1229_, v_messages_1237_);
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 6, v___x_1243_);
v___x_1245_ = v___x_1241_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_env_1231_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v_nextMacroScope_1232_);
lean_ctor_set(v_reuseFailAlloc_1247_, 2, v_ngen_1233_);
lean_ctor_set(v_reuseFailAlloc_1247_, 3, v_auxDeclNGen_1234_);
lean_ctor_set(v_reuseFailAlloc_1247_, 4, v_traceState_1235_);
lean_ctor_set(v_reuseFailAlloc_1247_, 5, v_cache_1236_);
lean_ctor_set(v_reuseFailAlloc_1247_, 6, v___x_1243_);
lean_ctor_set(v_reuseFailAlloc_1247_, 7, v_infoState_1238_);
lean_ctor_set(v_reuseFailAlloc_1247_, 8, v_snapshotTasks_1239_);
v___x_1245_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
lean_object* v___x_1246_; 
v___x_1246_ = lean_st_ref_put(v___y_1210_, v___x_1245_);
v_a_1173_ = v___x_1199_;
goto v___jp_1172_;
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
v___jp_1172_:
{
size_t v___x_1174_; size_t v___x_1175_; 
v___x_1174_ = ((size_t)1ULL);
v___x_1175_ = lean_usize_add(v_i_1167_, v___x_1174_);
v_i_1167_ = v___x_1175_;
v_b_1168_ = v_a_1173_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___boxed(lean_object* v___x_1260_, lean_object* v_as_1261_, lean_object* v_sz_1262_, lean_object* v_i_1263_, lean_object* v_b_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
uint8_t v___x_36460__boxed_1268_; size_t v_sz_boxed_1269_; size_t v_i_boxed_1270_; lean_object* v_res_1271_; 
v___x_36460__boxed_1268_ = lean_unbox(v___x_1260_);
v_sz_boxed_1269_ = lean_unbox_usize(v_sz_1262_);
lean_dec(v_sz_1262_);
v_i_boxed_1270_ = lean_unbox_usize(v_i_1263_);
lean_dec(v_i_1263_);
v_res_1271_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(v___x_36460__boxed_1268_, v_as_1261_, v_sz_boxed_1269_, v_i_boxed_1270_, v_b_1264_, v___y_1265_, v___y_1266_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec_ref(v_as_1261_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(lean_object* v_opts_1272_, lean_object* v_opt_1273_){
_start:
{
lean_object* v_name_1274_; lean_object* v_map_1275_; lean_object* v___x_1276_; 
v_name_1274_ = lean_ctor_get(v_opt_1273_, 0);
v_map_1275_ = lean_ctor_get(v_opts_1272_, 0);
v___x_1276_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1275_, v_name_1274_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v___x_1277_; 
v___x_1277_ = lean_box(0);
return v___x_1277_;
}
else
{
lean_object* v_val_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1287_; 
v_val_1278_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1280_ = v___x_1276_;
v_isShared_1281_ = v_isSharedCheck_1287_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_val_1278_);
lean_dec(v___x_1276_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1287_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
if (lean_obj_tag(v_val_1278_) == 0)
{
lean_object* v_v_1282_; lean_object* v___x_1284_; 
v_v_1282_ = lean_ctor_get(v_val_1278_, 0);
lean_inc_ref(v_v_1282_);
lean_dec_ref_known(v_val_1278_, 1);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 0, v_v_1282_);
v___x_1284_ = v___x_1280_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_v_1282_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
else
{
lean_object* v___x_1286_; 
lean_del_object(v___x_1280_);
lean_dec(v_val_1278_);
v___x_1286_ = lean_box(0);
return v___x_1286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15___boxed(lean_object* v_opts_1288_, lean_object* v_opt_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(v_opts_1288_, v_opt_1289_);
lean_dec_ref(v_opt_1289_);
lean_dec_ref(v_opts_1288_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(lean_object* v_a_1291_, lean_object* v_fallback_1292_, lean_object* v_x_1293_){
_start:
{
if (lean_obj_tag(v_x_1293_) == 0)
{
lean_inc(v_fallback_1292_);
return v_fallback_1292_;
}
else
{
lean_object* v_key_1294_; lean_object* v_value_1295_; lean_object* v_tail_1296_; lean_object* v_fst_1297_; lean_object* v_snd_1298_; lean_object* v_fst_1299_; lean_object* v_snd_1300_; uint8_t v_decide_1301_; 
v_key_1294_ = lean_ctor_get(v_x_1293_, 0);
v_value_1295_ = lean_ctor_get(v_x_1293_, 1);
v_tail_1296_ = lean_ctor_get(v_x_1293_, 2);
v_fst_1297_ = lean_ctor_get(v_key_1294_, 0);
v_snd_1298_ = lean_ctor_get(v_key_1294_, 1);
v_fst_1299_ = lean_ctor_get(v_a_1291_, 0);
v_snd_1300_ = lean_ctor_get(v_a_1291_, 1);
v_decide_1301_ = lean_nat_dec_eq(v_fst_1297_, v_fst_1299_);
if (v_decide_1301_ == 0)
{
v_x_1293_ = v_tail_1296_;
goto _start;
}
else
{
uint8_t v_decide_1303_; 
v_decide_1303_ = lean_nat_dec_eq(v_snd_1298_, v_snd_1300_);
if (v_decide_1303_ == 0)
{
v_x_1293_ = v_tail_1296_;
goto _start;
}
else
{
lean_inc(v_value_1295_);
return v_value_1295_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg___boxed(lean_object* v_a_1305_, lean_object* v_fallback_1306_, lean_object* v_x_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_1305_, v_fallback_1306_, v_x_1307_);
lean_dec(v_x_1307_);
lean_dec(v_fallback_1306_);
lean_dec_ref(v_a_1305_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(lean_object* v_m_1309_, lean_object* v_a_1310_, lean_object* v_fallback_1311_){
_start:
{
lean_object* v_buckets_1312_; lean_object* v_fst_1313_; lean_object* v_snd_1314_; lean_object* v___x_1315_; uint64_t v___x_1316_; uint64_t v___x_1317_; uint64_t v___x_1318_; uint64_t v___x_1319_; uint64_t v___x_1320_; uint64_t v_fold_1321_; uint64_t v___x_1322_; uint64_t v___x_1323_; uint64_t v___x_1324_; size_t v___x_1325_; size_t v___x_1326_; size_t v___x_1327_; size_t v___x_1328_; size_t v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v_buckets_1312_ = lean_ctor_get(v_m_1309_, 1);
v_fst_1313_ = lean_ctor_get(v_a_1310_, 0);
v_snd_1314_ = lean_ctor_get(v_a_1310_, 1);
v___x_1315_ = lean_array_get_size(v_buckets_1312_);
v___x_1316_ = l_String_instHashableRaw_hash(v_fst_1313_);
v___x_1317_ = l_String_instHashableRaw_hash(v_snd_1314_);
v___x_1318_ = lean_uint64_mix_hash(v___x_1316_, v___x_1317_);
v___x_1319_ = 32ULL;
v___x_1320_ = lean_uint64_shift_right(v___x_1318_, v___x_1319_);
v_fold_1321_ = lean_uint64_xor(v___x_1318_, v___x_1320_);
v___x_1322_ = 16ULL;
v___x_1323_ = lean_uint64_shift_right(v_fold_1321_, v___x_1322_);
v___x_1324_ = lean_uint64_xor(v_fold_1321_, v___x_1323_);
v___x_1325_ = lean_uint64_to_usize(v___x_1324_);
v___x_1326_ = lean_usize_of_nat(v___x_1315_);
v___x_1327_ = ((size_t)1ULL);
v___x_1328_ = lean_usize_sub(v___x_1326_, v___x_1327_);
v___x_1329_ = lean_usize_land(v___x_1325_, v___x_1328_);
v___x_1330_ = lean_array_uget_borrowed(v_buckets_1312_, v___x_1329_);
v___x_1331_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_1310_, v_fallback_1311_, v___x_1330_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg___boxed(lean_object* v_m_1332_, lean_object* v_a_1333_, lean_object* v_fallback_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_m_1332_, v_a_1333_, v_fallback_1334_);
lean_dec(v_fallback_1334_);
lean_dec_ref(v_a_1333_);
lean_dec_ref(v_m_1332_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(lean_object* v_x_1336_, lean_object* v_x_1337_){
_start:
{
if (lean_obj_tag(v_x_1337_) == 0)
{
return v_x_1336_;
}
else
{
lean_object* v_key_1338_; lean_object* v_value_1339_; lean_object* v_tail_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1367_; 
v_key_1338_ = lean_ctor_get(v_x_1337_, 0);
v_value_1339_ = lean_ctor_get(v_x_1337_, 1);
v_tail_1340_ = lean_ctor_get(v_x_1337_, 2);
v_isSharedCheck_1367_ = !lean_is_exclusive(v_x_1337_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1342_ = v_x_1337_;
v_isShared_1343_ = v_isSharedCheck_1367_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_tail_1340_);
lean_inc(v_value_1339_);
lean_inc(v_key_1338_);
lean_dec(v_x_1337_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1367_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v_fst_1344_; lean_object* v_snd_1345_; lean_object* v___x_1346_; uint64_t v___x_1347_; uint64_t v___x_1348_; uint64_t v___x_1349_; uint64_t v___x_1350_; uint64_t v___x_1351_; uint64_t v_fold_1352_; uint64_t v___x_1353_; uint64_t v___x_1354_; uint64_t v___x_1355_; size_t v___x_1356_; size_t v___x_1357_; size_t v___x_1358_; size_t v___x_1359_; size_t v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1363_; 
v_fst_1344_ = lean_ctor_get(v_key_1338_, 0);
v_snd_1345_ = lean_ctor_get(v_key_1338_, 1);
v___x_1346_ = lean_array_get_size(v_x_1336_);
v___x_1347_ = l_String_instHashableRaw_hash(v_fst_1344_);
v___x_1348_ = l_String_instHashableRaw_hash(v_snd_1345_);
v___x_1349_ = lean_uint64_mix_hash(v___x_1347_, v___x_1348_);
v___x_1350_ = 32ULL;
v___x_1351_ = lean_uint64_shift_right(v___x_1349_, v___x_1350_);
v_fold_1352_ = lean_uint64_xor(v___x_1349_, v___x_1351_);
v___x_1353_ = 16ULL;
v___x_1354_ = lean_uint64_shift_right(v_fold_1352_, v___x_1353_);
v___x_1355_ = lean_uint64_xor(v_fold_1352_, v___x_1354_);
v___x_1356_ = lean_uint64_to_usize(v___x_1355_);
v___x_1357_ = lean_usize_of_nat(v___x_1346_);
v___x_1358_ = ((size_t)1ULL);
v___x_1359_ = lean_usize_sub(v___x_1357_, v___x_1358_);
v___x_1360_ = lean_usize_land(v___x_1356_, v___x_1359_);
v___x_1361_ = lean_array_uget_borrowed(v_x_1336_, v___x_1360_);
lean_inc(v___x_1361_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 2, v___x_1361_);
v___x_1363_ = v___x_1342_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_key_1338_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_value_1339_);
lean_ctor_set(v_reuseFailAlloc_1366_, 2, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
lean_object* v___x_1364_; 
v___x_1364_ = lean_array_uset(v_x_1336_, v___x_1360_, v___x_1363_);
v_x_1336_ = v___x_1364_;
v_x_1337_ = v_tail_1340_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(lean_object* v_i_1368_, lean_object* v_source_1369_, lean_object* v_target_1370_){
_start:
{
lean_object* v___x_1371_; uint8_t v___x_1372_; 
v___x_1371_ = lean_array_get_size(v_source_1369_);
v___x_1372_ = lean_nat_dec_lt(v_i_1368_, v___x_1371_);
if (v___x_1372_ == 0)
{
lean_dec_ref(v_source_1369_);
lean_dec(v_i_1368_);
return v_target_1370_;
}
else
{
lean_object* v_es_1373_; lean_object* v___x_1374_; lean_object* v_source_1375_; lean_object* v_target_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v_es_1373_ = lean_array_fget(v_source_1369_, v_i_1368_);
v___x_1374_ = lean_box(0);
v_source_1375_ = lean_array_fset(v_source_1369_, v_i_1368_, v___x_1374_);
v_target_1376_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(v_target_1370_, v_es_1373_);
v___x_1377_ = lean_unsigned_to_nat(1u);
v___x_1378_ = lean_nat_add(v_i_1368_, v___x_1377_);
lean_dec(v_i_1368_);
v_i_1368_ = v___x_1378_;
v_source_1369_ = v_source_1375_;
v_target_1370_ = v_target_1376_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(lean_object* v_data_1380_){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v_nbuckets_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1381_ = lean_array_get_size(v_data_1380_);
v___x_1382_ = lean_unsigned_to_nat(2u);
v_nbuckets_1383_ = lean_nat_mul(v___x_1381_, v___x_1382_);
v___x_1384_ = lean_unsigned_to_nat(0u);
v___x_1385_ = lean_box(0);
v___x_1386_ = lean_mk_array(v_nbuckets_1383_, v___x_1385_);
v___x_1387_ = lean_array_propagate_mark(v_data_1380_, v___x_1386_);
v___x_1388_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(v___x_1384_, v_data_1380_, v___x_1387_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(lean_object* v_a_1389_, lean_object* v_b_1390_, lean_object* v_x_1391_){
_start:
{
if (lean_obj_tag(v_x_1391_) == 0)
{
lean_dec(v_b_1390_);
lean_dec_ref(v_a_1389_);
return v_x_1391_;
}
else
{
lean_object* v_key_1392_; lean_object* v_value_1393_; lean_object* v_tail_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1410_; 
v_key_1392_ = lean_ctor_get(v_x_1391_, 0);
v_value_1393_ = lean_ctor_get(v_x_1391_, 1);
v_tail_1394_ = lean_ctor_get(v_x_1391_, 2);
v_isSharedCheck_1410_ = !lean_is_exclusive(v_x_1391_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1396_ = v_x_1391_;
v_isShared_1397_ = v_isSharedCheck_1410_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_tail_1394_);
lean_inc(v_value_1393_);
lean_inc(v_key_1392_);
lean_dec(v_x_1391_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1410_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v_fst_1403_; lean_object* v_snd_1404_; lean_object* v_fst_1405_; lean_object* v_snd_1406_; uint8_t v_decide_1407_; 
v_fst_1403_ = lean_ctor_get(v_key_1392_, 0);
v_snd_1404_ = lean_ctor_get(v_key_1392_, 1);
v_fst_1405_ = lean_ctor_get(v_a_1389_, 0);
v_snd_1406_ = lean_ctor_get(v_a_1389_, 1);
v_decide_1407_ = lean_nat_dec_eq(v_fst_1403_, v_fst_1405_);
if (v_decide_1407_ == 0)
{
goto v___jp_1398_;
}
else
{
uint8_t v_decide_1408_; 
v_decide_1408_ = lean_nat_dec_eq(v_snd_1404_, v_snd_1406_);
if (v_decide_1408_ == 0)
{
goto v___jp_1398_;
}
else
{
lean_object* v___x_1409_; 
lean_del_object(v___x_1396_);
lean_dec(v_value_1393_);
lean_dec(v_key_1392_);
v___x_1409_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1409_, 0, v_a_1389_);
lean_ctor_set(v___x_1409_, 1, v_b_1390_);
lean_ctor_set(v___x_1409_, 2, v_tail_1394_);
return v___x_1409_;
}
}
v___jp_1398_:
{
lean_object* v___x_1399_; lean_object* v___x_1401_; 
v___x_1399_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_1389_, v_b_1390_, v_tail_1394_);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 2, v___x_1399_);
v___x_1401_ = v___x_1396_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_key_1392_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v_value_1393_);
lean_ctor_set(v_reuseFailAlloc_1402_, 2, v___x_1399_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(lean_object* v_a_1411_, lean_object* v_x_1412_){
_start:
{
if (lean_obj_tag(v_x_1412_) == 0)
{
uint8_t v___x_1413_; 
v___x_1413_ = 0;
return v___x_1413_;
}
else
{
lean_object* v_key_1414_; lean_object* v_tail_1415_; lean_object* v_fst_1416_; lean_object* v_snd_1417_; lean_object* v_fst_1418_; lean_object* v_snd_1419_; uint8_t v_decide_1420_; 
v_key_1414_ = lean_ctor_get(v_x_1412_, 0);
v_tail_1415_ = lean_ctor_get(v_x_1412_, 2);
v_fst_1416_ = lean_ctor_get(v_key_1414_, 0);
v_snd_1417_ = lean_ctor_get(v_key_1414_, 1);
v_fst_1418_ = lean_ctor_get(v_a_1411_, 0);
v_snd_1419_ = lean_ctor_get(v_a_1411_, 1);
v_decide_1420_ = lean_nat_dec_eq(v_fst_1416_, v_fst_1418_);
if (v_decide_1420_ == 0)
{
v_x_1412_ = v_tail_1415_;
goto _start;
}
else
{
uint8_t v_decide_1422_; 
v_decide_1422_ = lean_nat_dec_eq(v_snd_1417_, v_snd_1419_);
if (v_decide_1422_ == 0)
{
v_x_1412_ = v_tail_1415_;
goto _start;
}
else
{
return v_decide_1422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg___boxed(lean_object* v_a_1424_, lean_object* v_x_1425_){
_start:
{
uint8_t v_res_1426_; lean_object* v_r_1427_; 
v_res_1426_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_1424_, v_x_1425_);
lean_dec(v_x_1425_);
lean_dec_ref(v_a_1424_);
v_r_1427_ = lean_box(v_res_1426_);
return v_r_1427_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(lean_object* v_m_1428_, lean_object* v_a_1429_, lean_object* v_b_1430_){
_start:
{
lean_object* v_size_1431_; lean_object* v_buckets_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1479_; 
v_size_1431_ = lean_ctor_get(v_m_1428_, 0);
v_buckets_1432_ = lean_ctor_get(v_m_1428_, 1);
v_isSharedCheck_1479_ = !lean_is_exclusive(v_m_1428_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1434_ = v_m_1428_;
v_isShared_1435_ = v_isSharedCheck_1479_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_buckets_1432_);
lean_inc(v_size_1431_);
lean_dec(v_m_1428_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1479_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v_fst_1436_; lean_object* v_snd_1437_; lean_object* v___x_1438_; uint64_t v___x_1439_; uint64_t v___x_1440_; uint64_t v___x_1441_; uint64_t v___x_1442_; uint64_t v___x_1443_; uint64_t v_fold_1444_; uint64_t v___x_1445_; uint64_t v___x_1446_; uint64_t v___x_1447_; size_t v___x_1448_; size_t v___x_1449_; size_t v___x_1450_; size_t v___x_1451_; size_t v___x_1452_; lean_object* v_bkt_1453_; uint8_t v___x_1454_; 
v_fst_1436_ = lean_ctor_get(v_a_1429_, 0);
v_snd_1437_ = lean_ctor_get(v_a_1429_, 1);
v___x_1438_ = lean_array_get_size(v_buckets_1432_);
v___x_1439_ = l_String_instHashableRaw_hash(v_fst_1436_);
v___x_1440_ = l_String_instHashableRaw_hash(v_snd_1437_);
v___x_1441_ = lean_uint64_mix_hash(v___x_1439_, v___x_1440_);
v___x_1442_ = 32ULL;
v___x_1443_ = lean_uint64_shift_right(v___x_1441_, v___x_1442_);
v_fold_1444_ = lean_uint64_xor(v___x_1441_, v___x_1443_);
v___x_1445_ = 16ULL;
v___x_1446_ = lean_uint64_shift_right(v_fold_1444_, v___x_1445_);
v___x_1447_ = lean_uint64_xor(v_fold_1444_, v___x_1446_);
v___x_1448_ = lean_uint64_to_usize(v___x_1447_);
v___x_1449_ = lean_usize_of_nat(v___x_1438_);
v___x_1450_ = ((size_t)1ULL);
v___x_1451_ = lean_usize_sub(v___x_1449_, v___x_1450_);
v___x_1452_ = lean_usize_land(v___x_1448_, v___x_1451_);
v_bkt_1453_ = lean_array_uget_borrowed(v_buckets_1432_, v___x_1452_);
v___x_1454_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_1429_, v_bkt_1453_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; lean_object* v_size_x27_1456_; lean_object* v___x_1457_; lean_object* v_buckets_x27_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; uint8_t v___x_1464_; 
v___x_1455_ = lean_unsigned_to_nat(1u);
v_size_x27_1456_ = lean_nat_add(v_size_1431_, v___x_1455_);
lean_dec(v_size_1431_);
lean_inc(v_bkt_1453_);
v___x_1457_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1457_, 0, v_a_1429_);
lean_ctor_set(v___x_1457_, 1, v_b_1430_);
lean_ctor_set(v___x_1457_, 2, v_bkt_1453_);
v_buckets_x27_1458_ = lean_array_uset(v_buckets_1432_, v___x_1452_, v___x_1457_);
v___x_1459_ = lean_unsigned_to_nat(4u);
v___x_1460_ = lean_nat_mul(v_size_x27_1456_, v___x_1459_);
v___x_1461_ = lean_unsigned_to_nat(3u);
v___x_1462_ = lean_nat_div(v___x_1460_, v___x_1461_);
lean_dec(v___x_1460_);
v___x_1463_ = lean_array_get_size(v_buckets_x27_1458_);
v___x_1464_ = lean_nat_dec_le(v___x_1462_, v___x_1463_);
lean_dec(v___x_1462_);
if (v___x_1464_ == 0)
{
lean_object* v_val_1465_; lean_object* v___x_1467_; 
v_val_1465_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(v_buckets_x27_1458_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 1, v_val_1465_);
lean_ctor_set(v___x_1434_, 0, v_size_x27_1456_);
v___x_1467_ = v___x_1434_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_size_x27_1456_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_val_1465_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
else
{
lean_object* v___x_1470_; 
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 1, v_buckets_x27_1458_);
lean_ctor_set(v___x_1434_, 0, v_size_x27_1456_);
v___x_1470_ = v___x_1434_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_size_x27_1456_);
lean_ctor_set(v_reuseFailAlloc_1471_, 1, v_buckets_x27_1458_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
else
{
lean_object* v___x_1472_; lean_object* v_buckets_x27_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1477_; 
lean_inc(v_bkt_1453_);
v___x_1472_ = lean_box(0);
v_buckets_x27_1473_ = lean_array_uset(v_buckets_1432_, v___x_1452_, v___x_1472_);
v___x_1474_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_1429_, v_b_1430_, v_bkt_1453_);
v___x_1475_ = lean_array_uset(v_buckets_x27_1473_, v___x_1452_, v___x_1474_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 1, v___x_1475_);
v___x_1477_ = v___x_1434_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_size_1431_);
lean_ctor_set(v_reuseFailAlloc_1478_, 1, v___x_1475_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(uint8_t v___x_1482_, lean_object* v_as_1483_, size_t v_sz_1484_, size_t v_i_1485_, lean_object* v_b_1486_, lean_object* v___y_1487_){
_start:
{
uint8_t v___x_1489_; 
v___x_1489_ = lean_usize_dec_lt(v_i_1485_, v_sz_1484_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; 
v___x_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1490_, 0, v_b_1486_);
return v___x_1490_;
}
else
{
lean_object* v_snd_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1528_; 
v_snd_1491_ = lean_ctor_get(v_b_1486_, 1);
v_isSharedCheck_1528_ = !lean_is_exclusive(v_b_1486_);
if (v_isSharedCheck_1528_ == 0)
{
lean_object* v_unused_1529_; 
v_unused_1529_ = lean_ctor_get(v_b_1486_, 0);
lean_dec(v_unused_1529_);
v___x_1493_ = v_b_1486_;
v_isShared_1494_ = v_isSharedCheck_1528_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_snd_1491_);
lean_dec(v_b_1486_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1528_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v_ref_1495_; lean_object* v_a_1496_; lean_object* v_ref_1497_; lean_object* v_msg_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1527_; 
v_ref_1495_ = lean_ctor_get(v___y_1487_, 2);
v_a_1496_ = lean_array_uget(v_as_1483_, v_i_1485_);
v_ref_1497_ = lean_ctor_get(v_a_1496_, 0);
v_msg_1498_ = lean_ctor_get(v_a_1496_, 1);
v_isSharedCheck_1527_ = !lean_is_exclusive(v_a_1496_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1500_ = v_a_1496_;
v_isShared_1501_ = v_isSharedCheck_1527_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_msg_1498_);
lean_inc(v_ref_1497_);
lean_dec(v_a_1496_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1527_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1502_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v_ref_1519_; lean_object* v___y_1521_; lean_object* v___x_1524_; 
v___x_1502_ = lean_box(0);
v_ref_1519_ = l_Lean_replaceRef(v_ref_1497_, v_ref_1495_);
lean_dec(v_ref_1497_);
v___x_1524_ = l_Lean_Syntax_getPos_x3f(v_ref_1519_, v___x_1482_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v___x_1525_; 
v___x_1525_ = lean_unsigned_to_nat(0u);
v___y_1521_ = v___x_1525_;
goto v___jp_1520_;
}
else
{
lean_object* v_val_1526_; 
v_val_1526_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_val_1526_);
lean_dec_ref_known(v___x_1524_, 1);
v___y_1521_ = v_val_1526_;
goto v___jp_1520_;
}
v___jp_1503_:
{
lean_object* v___x_1507_; 
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 1, v___y_1505_);
lean_ctor_set(v___x_1493_, 0, v___y_1504_);
v___x_1507_ = v___x_1493_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___y_1504_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v___y_1505_);
v___x_1507_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v_pos2traces_1511_; lean_object* v___x_1513_; 
v___x_1508_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1509_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1491_, v___x_1507_, v___x_1508_);
v___x_1510_ = lean_array_push(v___x_1509_, v_msg_1498_);
v_pos2traces_1511_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1491_, v___x_1507_, v___x_1510_);
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 1, v_pos2traces_1511_);
lean_ctor_set(v___x_1500_, 0, v___x_1502_);
v___x_1513_ = v___x_1500_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1502_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v_pos2traces_1511_);
v___x_1513_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
size_t v___x_1514_; size_t v___x_1515_; 
v___x_1514_ = ((size_t)1ULL);
v___x_1515_ = lean_usize_add(v_i_1485_, v___x_1514_);
v_i_1485_ = v___x_1515_;
v_b_1486_ = v___x_1513_;
goto _start;
}
}
}
v___jp_1520_:
{
lean_object* v___x_1522_; 
v___x_1522_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1519_, v___x_1482_);
lean_dec(v_ref_1519_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_inc(v___y_1521_);
v___y_1504_ = v___y_1521_;
v___y_1505_ = v___y_1521_;
goto v___jp_1503_;
}
else
{
lean_object* v_val_1523_; 
v_val_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_val_1523_);
lean_dec_ref_known(v___x_1522_, 1);
v___y_1504_ = v___y_1521_;
v___y_1505_ = v_val_1523_;
goto v___jp_1503_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___boxed(lean_object* v___x_1530_, lean_object* v_as_1531_, lean_object* v_sz_1532_, lean_object* v_i_1533_, lean_object* v_b_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
uint8_t v___x_36931__boxed_1537_; size_t v_sz_boxed_1538_; size_t v_i_boxed_1539_; lean_object* v_res_1540_; 
v___x_36931__boxed_1537_ = lean_unbox(v___x_1530_);
v_sz_boxed_1538_ = lean_unbox_usize(v_sz_1532_);
lean_dec(v_sz_1532_);
v_i_boxed_1539_ = lean_unbox_usize(v_i_1533_);
lean_dec(v_i_1533_);
v_res_1540_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_36931__boxed_1537_, v_as_1531_, v_sz_boxed_1538_, v_i_boxed_1539_, v_b_1534_, v___y_1535_);
lean_dec_ref(v___y_1535_);
lean_dec_ref(v_as_1531_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(uint8_t v___x_1541_, lean_object* v_as_1542_, size_t v_sz_1543_, size_t v_i_1544_, lean_object* v_b_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
uint8_t v___x_1549_; 
v___x_1549_ = lean_usize_dec_lt(v_i_1544_, v_sz_1543_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1550_; 
v___x_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1550_, 0, v_b_1545_);
return v___x_1550_;
}
else
{
lean_object* v_snd_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1588_; 
v_snd_1551_ = lean_ctor_get(v_b_1545_, 1);
v_isSharedCheck_1588_ = !lean_is_exclusive(v_b_1545_);
if (v_isSharedCheck_1588_ == 0)
{
lean_object* v_unused_1589_; 
v_unused_1589_ = lean_ctor_get(v_b_1545_, 0);
lean_dec(v_unused_1589_);
v___x_1553_ = v_b_1545_;
v_isShared_1554_ = v_isSharedCheck_1588_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_snd_1551_);
lean_dec(v_b_1545_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1588_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v_ref_1555_; lean_object* v_a_1556_; lean_object* v_ref_1557_; lean_object* v_msg_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1587_; 
v_ref_1555_ = lean_ctor_get(v___y_1546_, 2);
v_a_1556_ = lean_array_uget(v_as_1542_, v_i_1544_);
v_ref_1557_ = lean_ctor_get(v_a_1556_, 0);
v_msg_1558_ = lean_ctor_get(v_a_1556_, 1);
v_isSharedCheck_1587_ = !lean_is_exclusive(v_a_1556_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1560_ = v_a_1556_;
v_isShared_1561_ = v_isSharedCheck_1587_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_msg_1558_);
lean_inc(v_ref_1557_);
lean_dec(v_a_1556_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1587_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1562_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v_ref_1579_; lean_object* v___y_1581_; lean_object* v___x_1584_; 
v___x_1562_ = lean_box(0);
v_ref_1579_ = l_Lean_replaceRef(v_ref_1557_, v_ref_1555_);
lean_dec(v_ref_1557_);
v___x_1584_ = l_Lean_Syntax_getPos_x3f(v_ref_1579_, v___x_1541_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v___x_1585_; 
v___x_1585_ = lean_unsigned_to_nat(0u);
v___y_1581_ = v___x_1585_;
goto v___jp_1580_;
}
else
{
lean_object* v_val_1586_; 
v_val_1586_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_val_1586_);
lean_dec_ref_known(v___x_1584_, 1);
v___y_1581_ = v_val_1586_;
goto v___jp_1580_;
}
v___jp_1563_:
{
lean_object* v___x_1567_; 
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 1, v___y_1565_);
lean_ctor_set(v___x_1553_, 0, v___y_1564_);
v___x_1567_ = v___x_1553_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___y_1564_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v___y_1565_);
v___x_1567_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v_pos2traces_1571_; lean_object* v___x_1573_; 
v___x_1568_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1569_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1551_, v___x_1567_, v___x_1568_);
v___x_1570_ = lean_array_push(v___x_1569_, v_msg_1558_);
v_pos2traces_1571_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1551_, v___x_1567_, v___x_1570_);
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 1, v_pos2traces_1571_);
lean_ctor_set(v___x_1560_, 0, v___x_1562_);
v___x_1573_ = v___x_1560_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1562_);
lean_ctor_set(v_reuseFailAlloc_1577_, 1, v_pos2traces_1571_);
v___x_1573_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
size_t v___x_1574_; size_t v___x_1575_; lean_object* v___x_1576_; 
v___x_1574_ = ((size_t)1ULL);
v___x_1575_ = lean_usize_add(v_i_1544_, v___x_1574_);
v___x_1576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_1541_, v_as_1542_, v_sz_1543_, v___x_1575_, v___x_1573_, v___y_1546_);
return v___x_1576_;
}
}
}
v___jp_1580_:
{
lean_object* v___x_1582_; 
v___x_1582_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1579_, v___x_1541_);
lean_dec(v_ref_1579_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_inc(v___y_1581_);
v___y_1564_ = v___y_1581_;
v___y_1565_ = v___y_1581_;
goto v___jp_1563_;
}
else
{
lean_object* v_val_1583_; 
v_val_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_val_1583_);
lean_dec_ref_known(v___x_1582_, 1);
v___y_1564_ = v___y_1581_;
v___y_1565_ = v_val_1583_;
goto v___jp_1563_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40___boxed(lean_object* v___x_1590_, lean_object* v_as_1591_, lean_object* v_sz_1592_, lean_object* v_i_1593_, lean_object* v_b_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
uint8_t v___x_37012__boxed_1598_; size_t v_sz_boxed_1599_; size_t v_i_boxed_1600_; lean_object* v_res_1601_; 
v___x_37012__boxed_1598_ = lean_unbox(v___x_1590_);
v_sz_boxed_1599_ = lean_unbox_usize(v_sz_1592_);
lean_dec(v_sz_1592_);
v_i_boxed_1600_ = lean_unbox_usize(v_i_1593_);
lean_dec(v_i_1593_);
v_res_1601_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(v___x_37012__boxed_1598_, v_as_1591_, v_sz_boxed_1599_, v_i_boxed_1600_, v_b_1594_, v___y_1595_, v___y_1596_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec_ref(v_as_1591_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(lean_object* v_init_1602_, uint8_t v___x_1603_, lean_object* v_n_1604_, lean_object* v_b_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
if (lean_obj_tag(v_n_1604_) == 0)
{
lean_object* v_cs_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; size_t v_sz_1612_; size_t v___x_1613_; lean_object* v___x_1614_; 
v_cs_1609_ = lean_ctor_get(v_n_1604_, 0);
v___x_1610_ = lean_box(0);
v___x_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1610_);
lean_ctor_set(v___x_1611_, 1, v_b_1605_);
v_sz_1612_ = lean_array_size(v_cs_1609_);
v___x_1613_ = ((size_t)0ULL);
v___x_1614_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(v_init_1602_, v___x_1603_, v_cs_1609_, v_sz_1612_, v___x_1613_, v___x_1611_, v___y_1606_, v___y_1607_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1629_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1617_ = v___x_1614_;
v_isShared_1618_ = v_isSharedCheck_1629_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1614_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1629_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v_fst_1619_; 
v_fst_1619_ = lean_ctor_get(v_a_1615_, 0);
if (lean_obj_tag(v_fst_1619_) == 0)
{
lean_object* v_snd_1620_; lean_object* v___x_1621_; lean_object* v___x_1623_; 
v_snd_1620_ = lean_ctor_get(v_a_1615_, 1);
lean_inc(v_snd_1620_);
lean_dec(v_a_1615_);
v___x_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1621_, 0, v_snd_1620_);
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 0, v___x_1621_);
v___x_1623_ = v___x_1617_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1621_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
else
{
lean_object* v_val_1625_; lean_object* v___x_1627_; 
lean_inc_ref(v_fst_1619_);
lean_dec(v_a_1615_);
v_val_1625_ = lean_ctor_get(v_fst_1619_, 0);
lean_inc(v_val_1625_);
lean_dec_ref_known(v_fst_1619_, 1);
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 0, v_val_1625_);
v___x_1627_ = v___x_1617_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_val_1625_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
else
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
v_a_1630_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1614_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1614_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
else
{
lean_object* v_vs_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; size_t v_sz_1641_; size_t v___x_1642_; lean_object* v___x_1643_; 
v_vs_1638_ = lean_ctor_get(v_n_1604_, 0);
v___x_1639_ = lean_box(0);
v___x_1640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
lean_ctor_set(v___x_1640_, 1, v_b_1605_);
v_sz_1641_ = lean_array_size(v_vs_1638_);
v___x_1642_ = ((size_t)0ULL);
v___x_1643_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(v___x_1603_, v_vs_1638_, v_sz_1641_, v___x_1642_, v___x_1640_, v___y_1606_, v___y_1607_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1658_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1646_ = v___x_1643_;
v_isShared_1647_ = v_isSharedCheck_1658_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1643_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1658_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v_fst_1648_; 
v_fst_1648_ = lean_ctor_get(v_a_1644_, 0);
if (lean_obj_tag(v_fst_1648_) == 0)
{
lean_object* v_snd_1649_; lean_object* v___x_1650_; lean_object* v___x_1652_; 
v_snd_1649_ = lean_ctor_get(v_a_1644_, 1);
lean_inc(v_snd_1649_);
lean_dec(v_a_1644_);
v___x_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1650_, 0, v_snd_1649_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 0, v___x_1650_);
v___x_1652_ = v___x_1646_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1650_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
else
{
lean_object* v_val_1654_; lean_object* v___x_1656_; 
lean_inc_ref(v_fst_1648_);
lean_dec(v_a_1644_);
v_val_1654_ = lean_ctor_get(v_fst_1648_, 0);
lean_inc(v_val_1654_);
lean_dec_ref_known(v_fst_1648_, 1);
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 0, v_val_1654_);
v___x_1656_ = v___x_1646_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_val_1654_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
v_a_1659_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1643_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1643_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1659_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(lean_object* v_init_1667_, uint8_t v___x_1668_, lean_object* v_as_1669_, size_t v_sz_1670_, size_t v_i_1671_, lean_object* v_b_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
uint8_t v___x_1676_; 
v___x_1676_ = lean_usize_dec_lt(v_i_1671_, v_sz_1670_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; 
v___x_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1677_, 0, v_b_1672_);
return v___x_1677_;
}
else
{
lean_object* v_snd_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1712_; 
v_snd_1678_ = lean_ctor_get(v_b_1672_, 1);
v_isSharedCheck_1712_ = !lean_is_exclusive(v_b_1672_);
if (v_isSharedCheck_1712_ == 0)
{
lean_object* v_unused_1713_; 
v_unused_1713_ = lean_ctor_get(v_b_1672_, 0);
lean_dec(v_unused_1713_);
v___x_1680_ = v_b_1672_;
v_isShared_1681_ = v_isSharedCheck_1712_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_snd_1678_);
lean_dec(v_b_1672_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1712_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1682_; lean_object* v_a_1683_; lean_object* v___x_1684_; 
v___x_1682_ = lean_box(0);
v_a_1683_ = lean_array_uget_borrowed(v_as_1669_, v_i_1671_);
lean_inc(v_snd_1678_);
v___x_1684_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1667_, v___x_1668_, v_a_1683_, v_snd_1678_, v___y_1673_, v___y_1674_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1703_; 
v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1687_ = v___x_1684_;
v_isShared_1688_ = v_isSharedCheck_1703_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1684_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1703_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
if (lean_obj_tag(v_a_1685_) == 0)
{
lean_object* v___x_1689_; lean_object* v___x_1691_; 
v___x_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1689_, 0, v_a_1685_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 0, v___x_1689_);
v___x_1691_ = v___x_1680_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v___x_1689_);
lean_ctor_set(v_reuseFailAlloc_1695_, 1, v_snd_1678_);
v___x_1691_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
lean_object* v___x_1693_; 
if (v_isShared_1688_ == 0)
{
lean_ctor_set(v___x_1687_, 0, v___x_1691_);
v___x_1693_ = v___x_1687_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1691_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
else
{
lean_object* v_a_1696_; lean_object* v___x_1698_; 
lean_del_object(v___x_1687_);
lean_dec(v_snd_1678_);
v_a_1696_ = lean_ctor_get(v_a_1685_, 0);
lean_inc(v_a_1696_);
lean_dec_ref_known(v_a_1685_, 1);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 1, v_a_1696_);
lean_ctor_set(v___x_1680_, 0, v___x_1682_);
v___x_1698_ = v___x_1680_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1682_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v_a_1696_);
v___x_1698_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
size_t v___x_1699_; size_t v___x_1700_; 
v___x_1699_ = ((size_t)1ULL);
v___x_1700_ = lean_usize_add(v_i_1671_, v___x_1699_);
v_i_1671_ = v___x_1700_;
v_b_1672_ = v___x_1698_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1711_; 
lean_del_object(v___x_1680_);
lean_dec(v_snd_1678_);
v_a_1704_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1706_ = v___x_1684_;
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v___x_1684_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_a_1704_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39___boxed(lean_object* v_init_1714_, lean_object* v___x_1715_, lean_object* v_as_1716_, lean_object* v_sz_1717_, lean_object* v_i_1718_, lean_object* v_b_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
uint8_t v___x_37093__boxed_1723_; size_t v_sz_boxed_1724_; size_t v_i_boxed_1725_; lean_object* v_res_1726_; 
v___x_37093__boxed_1723_ = lean_unbox(v___x_1715_);
v_sz_boxed_1724_ = lean_unbox_usize(v_sz_1717_);
lean_dec(v_sz_1717_);
v_i_boxed_1725_ = lean_unbox_usize(v_i_1718_);
lean_dec(v_i_1718_);
v_res_1726_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(v_init_1714_, v___x_37093__boxed_1723_, v_as_1716_, v_sz_boxed_1724_, v_i_boxed_1725_, v_b_1719_, v___y_1720_, v___y_1721_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec_ref(v_as_1716_);
lean_dec_ref(v_init_1714_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27___boxed(lean_object* v_init_1727_, lean_object* v___x_1728_, lean_object* v_n_1729_, lean_object* v_b_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
uint8_t v___x_37113__boxed_1734_; lean_object* v_res_1735_; 
v___x_37113__boxed_1734_ = lean_unbox(v___x_1728_);
v_res_1735_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1727_, v___x_37113__boxed_1734_, v_n_1729_, v_b_1730_, v___y_1731_, v___y_1732_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec_ref(v_n_1729_);
lean_dec_ref(v_init_1727_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(uint8_t v___x_1736_, lean_object* v_as_1737_, size_t v_sz_1738_, size_t v_i_1739_, lean_object* v_b_1740_, lean_object* v___y_1741_){
_start:
{
uint8_t v___x_1743_; 
v___x_1743_ = lean_usize_dec_lt(v_i_1739_, v_sz_1738_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1744_; 
v___x_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1744_, 0, v_b_1740_);
return v___x_1744_;
}
else
{
lean_object* v_snd_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1782_; 
v_snd_1745_ = lean_ctor_get(v_b_1740_, 1);
v_isSharedCheck_1782_ = !lean_is_exclusive(v_b_1740_);
if (v_isSharedCheck_1782_ == 0)
{
lean_object* v_unused_1783_; 
v_unused_1783_ = lean_ctor_get(v_b_1740_, 0);
lean_dec(v_unused_1783_);
v___x_1747_ = v_b_1740_;
v_isShared_1748_ = v_isSharedCheck_1782_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_snd_1745_);
lean_dec(v_b_1740_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1782_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v_ref_1749_; lean_object* v_a_1750_; lean_object* v_ref_1751_; lean_object* v_msg_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1781_; 
v_ref_1749_ = lean_ctor_get(v___y_1741_, 2);
v_a_1750_ = lean_array_uget(v_as_1737_, v_i_1739_);
v_ref_1751_ = lean_ctor_get(v_a_1750_, 0);
v_msg_1752_ = lean_ctor_get(v_a_1750_, 1);
v_isSharedCheck_1781_ = !lean_is_exclusive(v_a_1750_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1754_ = v_a_1750_;
v_isShared_1755_ = v_isSharedCheck_1781_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_msg_1752_);
lean_inc(v_ref_1751_);
lean_dec(v_a_1750_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1781_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1756_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v_ref_1773_; lean_object* v___y_1775_; lean_object* v___x_1778_; 
v___x_1756_ = lean_box(0);
v_ref_1773_ = l_Lean_replaceRef(v_ref_1751_, v_ref_1749_);
lean_dec(v_ref_1751_);
v___x_1778_ = l_Lean_Syntax_getPos_x3f(v_ref_1773_, v___x_1736_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v___x_1779_; 
v___x_1779_ = lean_unsigned_to_nat(0u);
v___y_1775_ = v___x_1779_;
goto v___jp_1774_;
}
else
{
lean_object* v_val_1780_; 
v_val_1780_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_val_1780_);
lean_dec_ref_known(v___x_1778_, 1);
v___y_1775_ = v_val_1780_;
goto v___jp_1774_;
}
v___jp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 1, v___y_1759_);
lean_ctor_set(v___x_1747_, 0, v___y_1758_);
v___x_1761_ = v___x_1747_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___y_1758_);
lean_ctor_set(v_reuseFailAlloc_1772_, 1, v___y_1759_);
v___x_1761_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v_pos2traces_1765_; lean_object* v___x_1767_; 
v___x_1762_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1763_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1745_, v___x_1761_, v___x_1762_);
v___x_1764_ = lean_array_push(v___x_1763_, v_msg_1752_);
v_pos2traces_1765_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1745_, v___x_1761_, v___x_1764_);
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 1, v_pos2traces_1765_);
lean_ctor_set(v___x_1754_, 0, v___x_1756_);
v___x_1767_ = v___x_1754_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1756_);
lean_ctor_set(v_reuseFailAlloc_1771_, 1, v_pos2traces_1765_);
v___x_1767_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
size_t v___x_1768_; size_t v___x_1769_; 
v___x_1768_ = ((size_t)1ULL);
v___x_1769_ = lean_usize_add(v_i_1739_, v___x_1768_);
v_i_1739_ = v___x_1769_;
v_b_1740_ = v___x_1767_;
goto _start;
}
}
}
v___jp_1774_:
{
lean_object* v___x_1776_; 
v___x_1776_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1773_, v___x_1736_);
lean_dec(v_ref_1773_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_inc(v___y_1775_);
v___y_1758_ = v___y_1775_;
v___y_1759_ = v___y_1775_;
goto v___jp_1757_;
}
else
{
lean_object* v_val_1777_; 
v_val_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_val_1777_);
lean_dec_ref_known(v___x_1776_, 1);
v___y_1758_ = v___y_1775_;
v___y_1759_ = v_val_1777_;
goto v___jp_1757_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg___boxed(lean_object* v___x_1784_, lean_object* v_as_1785_, lean_object* v_sz_1786_, lean_object* v_i_1787_, lean_object* v_b_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
uint8_t v___x_37296__boxed_1791_; size_t v_sz_boxed_1792_; size_t v_i_boxed_1793_; lean_object* v_res_1794_; 
v___x_37296__boxed_1791_ = lean_unbox(v___x_1784_);
v_sz_boxed_1792_ = lean_unbox_usize(v_sz_1786_);
lean_dec(v_sz_1786_);
v_i_boxed_1793_ = lean_unbox_usize(v_i_1787_);
lean_dec(v_i_1787_);
v_res_1794_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_37296__boxed_1791_, v_as_1785_, v_sz_boxed_1792_, v_i_boxed_1793_, v_b_1788_, v___y_1789_);
lean_dec_ref(v___y_1789_);
lean_dec_ref(v_as_1785_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(uint8_t v___x_1795_, lean_object* v_as_1796_, size_t v_sz_1797_, size_t v_i_1798_, lean_object* v_b_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
uint8_t v___x_1803_; 
v___x_1803_ = lean_usize_dec_lt(v_i_1798_, v_sz_1797_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; 
v___x_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1804_, 0, v_b_1799_);
return v___x_1804_;
}
else
{
lean_object* v_snd_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1842_; 
v_snd_1805_ = lean_ctor_get(v_b_1799_, 1);
v_isSharedCheck_1842_ = !lean_is_exclusive(v_b_1799_);
if (v_isSharedCheck_1842_ == 0)
{
lean_object* v_unused_1843_; 
v_unused_1843_ = lean_ctor_get(v_b_1799_, 0);
lean_dec(v_unused_1843_);
v___x_1807_ = v_b_1799_;
v_isShared_1808_ = v_isSharedCheck_1842_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_snd_1805_);
lean_dec(v_b_1799_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1842_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v_ref_1809_; lean_object* v_a_1810_; lean_object* v_ref_1811_; lean_object* v_msg_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1841_; 
v_ref_1809_ = lean_ctor_get(v___y_1800_, 2);
v_a_1810_ = lean_array_uget(v_as_1796_, v_i_1798_);
v_ref_1811_ = lean_ctor_get(v_a_1810_, 0);
v_msg_1812_ = lean_ctor_get(v_a_1810_, 1);
v_isSharedCheck_1841_ = !lean_is_exclusive(v_a_1810_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1814_ = v_a_1810_;
v_isShared_1815_ = v_isSharedCheck_1841_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_msg_1812_);
lean_inc(v_ref_1811_);
lean_dec(v_a_1810_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1841_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1816_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v_ref_1833_; lean_object* v___y_1835_; lean_object* v___x_1838_; 
v___x_1816_ = lean_box(0);
v_ref_1833_ = l_Lean_replaceRef(v_ref_1811_, v_ref_1809_);
lean_dec(v_ref_1811_);
v___x_1838_ = l_Lean_Syntax_getPos_x3f(v_ref_1833_, v___x_1795_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v___x_1839_; 
v___x_1839_ = lean_unsigned_to_nat(0u);
v___y_1835_ = v___x_1839_;
goto v___jp_1834_;
}
else
{
lean_object* v_val_1840_; 
v_val_1840_ = lean_ctor_get(v___x_1838_, 0);
lean_inc(v_val_1840_);
lean_dec_ref_known(v___x_1838_, 1);
v___y_1835_ = v_val_1840_;
goto v___jp_1834_;
}
v___jp_1817_:
{
lean_object* v___x_1821_; 
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 1, v___y_1819_);
lean_ctor_set(v___x_1807_, 0, v___y_1818_);
v___x_1821_ = v___x_1807_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___y_1818_);
lean_ctor_set(v_reuseFailAlloc_1832_, 1, v___y_1819_);
v___x_1821_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v_pos2traces_1825_; lean_object* v___x_1827_; 
v___x_1822_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1823_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1805_, v___x_1821_, v___x_1822_);
v___x_1824_ = lean_array_push(v___x_1823_, v_msg_1812_);
v_pos2traces_1825_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1805_, v___x_1821_, v___x_1824_);
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 1, v_pos2traces_1825_);
lean_ctor_set(v___x_1814_, 0, v___x_1816_);
v___x_1827_ = v___x_1814_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v___x_1816_);
lean_ctor_set(v_reuseFailAlloc_1831_, 1, v_pos2traces_1825_);
v___x_1827_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
size_t v___x_1828_; size_t v___x_1829_; lean_object* v___x_1830_; 
v___x_1828_ = ((size_t)1ULL);
v___x_1829_ = lean_usize_add(v_i_1798_, v___x_1828_);
v___x_1830_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_1795_, v_as_1796_, v_sz_1797_, v___x_1829_, v___x_1827_, v___y_1800_);
return v___x_1830_;
}
}
}
v___jp_1834_:
{
lean_object* v___x_1836_; 
v___x_1836_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1833_, v___x_1795_);
lean_dec(v_ref_1833_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_inc(v___y_1835_);
v___y_1818_ = v___y_1835_;
v___y_1819_ = v___y_1835_;
goto v___jp_1817_;
}
else
{
lean_object* v_val_1837_; 
v_val_1837_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_val_1837_);
lean_dec_ref_known(v___x_1836_, 1);
v___y_1818_ = v___y_1835_;
v___y_1819_ = v_val_1837_;
goto v___jp_1817_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28___boxed(lean_object* v___x_1844_, lean_object* v_as_1845_, lean_object* v_sz_1846_, lean_object* v_i_1847_, lean_object* v_b_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
uint8_t v___x_37376__boxed_1852_; size_t v_sz_boxed_1853_; size_t v_i_boxed_1854_; lean_object* v_res_1855_; 
v___x_37376__boxed_1852_ = lean_unbox(v___x_1844_);
v_sz_boxed_1853_ = lean_unbox_usize(v_sz_1846_);
lean_dec(v_sz_1846_);
v_i_boxed_1854_ = lean_unbox_usize(v_i_1847_);
lean_dec(v_i_1847_);
v_res_1855_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(v___x_37376__boxed_1852_, v_as_1845_, v_sz_boxed_1853_, v_i_boxed_1854_, v_b_1848_, v___y_1849_, v___y_1850_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec_ref(v_as_1845_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(uint8_t v___x_1856_, lean_object* v_t_1857_, lean_object* v_init_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v_root_1862_; lean_object* v_tail_1863_; lean_object* v___x_1864_; 
v_root_1862_ = lean_ctor_get(v_t_1857_, 0);
v_tail_1863_ = lean_ctor_get(v_t_1857_, 1);
lean_inc_ref(v_init_1858_);
v___x_1864_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1858_, v___x_1856_, v_root_1862_, v_init_1858_, v___y_1859_, v___y_1860_);
lean_dec_ref(v_init_1858_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1901_; 
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1867_ = v___x_1864_;
v_isShared_1868_ = v_isSharedCheck_1901_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1864_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1901_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
if (lean_obj_tag(v_a_1865_) == 0)
{
lean_object* v_a_1869_; lean_object* v___x_1871_; 
v_a_1869_ = lean_ctor_get(v_a_1865_, 0);
lean_inc(v_a_1869_);
lean_dec_ref_known(v_a_1865_, 1);
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 0, v_a_1869_);
v___x_1871_ = v___x_1867_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1869_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
else
{
lean_object* v_a_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; size_t v_sz_1876_; size_t v___x_1877_; lean_object* v___x_1878_; 
lean_del_object(v___x_1867_);
v_a_1873_ = lean_ctor_get(v_a_1865_, 0);
lean_inc(v_a_1873_);
lean_dec_ref_known(v_a_1865_, 1);
v___x_1874_ = lean_box(0);
v___x_1875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
lean_ctor_set(v___x_1875_, 1, v_a_1873_);
v_sz_1876_ = lean_array_size(v_tail_1863_);
v___x_1877_ = ((size_t)0ULL);
v___x_1878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(v___x_1856_, v_tail_1863_, v_sz_1876_, v___x_1877_, v___x_1875_, v___y_1859_, v___y_1860_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1892_; 
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1881_ = v___x_1878_;
v_isShared_1882_ = v_isSharedCheck_1892_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1878_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1892_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v_fst_1883_; 
v_fst_1883_ = lean_ctor_get(v_a_1879_, 0);
if (lean_obj_tag(v_fst_1883_) == 0)
{
lean_object* v_snd_1884_; lean_object* v___x_1886_; 
v_snd_1884_ = lean_ctor_get(v_a_1879_, 1);
lean_inc(v_snd_1884_);
lean_dec(v_a_1879_);
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 0, v_snd_1884_);
v___x_1886_ = v___x_1881_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_snd_1884_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
else
{
lean_object* v_val_1888_; lean_object* v___x_1890_; 
lean_inc_ref(v_fst_1883_);
lean_dec(v_a_1879_);
v_val_1888_ = lean_ctor_get(v_fst_1883_, 0);
lean_inc(v_val_1888_);
lean_dec_ref_known(v_fst_1883_, 1);
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 0, v_val_1888_);
v___x_1890_ = v___x_1881_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_val_1888_);
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
else
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
v_a_1893_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___x_1878_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1878_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1893_);
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
else
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
v_a_1902_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___x_1864_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1864_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19___boxed(lean_object* v___x_1910_, lean_object* v_t_1911_, lean_object* v_init_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
uint8_t v___x_37457__boxed_1916_; lean_object* v_res_1917_; 
v___x_37457__boxed_1916_ = lean_unbox(v___x_1910_);
v_res_1917_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(v___x_37457__boxed_1916_, v_t_1911_, v_init_1912_, v___y_1913_, v___y_1914_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec_ref(v_t_1911_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(lean_object* v_x_1918_, lean_object* v_x_1919_){
_start:
{
if (lean_obj_tag(v_x_1919_) == 0)
{
return v_x_1918_;
}
else
{
lean_object* v_key_1920_; lean_object* v_value_1921_; lean_object* v_tail_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v_key_1920_ = lean_ctor_get(v_x_1919_, 0);
v_value_1921_ = lean_ctor_get(v_x_1919_, 1);
v_tail_1922_ = lean_ctor_get(v_x_1919_, 2);
lean_inc(v_value_1921_);
lean_inc(v_key_1920_);
v___x_1923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1923_, 0, v_key_1920_);
lean_ctor_set(v___x_1923_, 1, v_value_1921_);
v___x_1924_ = lean_array_push(v_x_1918_, v___x_1923_);
v_x_1918_ = v___x_1924_;
v_x_1919_ = v_tail_1922_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22___boxed(lean_object* v_x_1926_, lean_object* v_x_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(v_x_1926_, v_x_1927_);
lean_dec(v_x_1927_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(lean_object* v_as_1929_, size_t v_i_1930_, size_t v_stop_1931_, lean_object* v_b_1932_){
_start:
{
uint8_t v___x_1933_; 
v___x_1933_ = lean_usize_dec_eq(v_i_1930_, v_stop_1931_);
if (v___x_1933_ == 0)
{
lean_object* v___x_1934_; lean_object* v___x_1935_; size_t v___x_1936_; size_t v___x_1937_; 
v___x_1934_ = lean_array_uget_borrowed(v_as_1929_, v_i_1930_);
v___x_1935_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(v_b_1932_, v___x_1934_);
v___x_1936_ = ((size_t)1ULL);
v___x_1937_ = lean_usize_add(v_i_1930_, v___x_1936_);
v_i_1930_ = v___x_1937_;
v_b_1932_ = v___x_1935_;
goto _start;
}
else
{
return v_b_1932_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23___boxed(lean_object* v_as_1939_, lean_object* v_i_1940_, lean_object* v_stop_1941_, lean_object* v_b_1942_){
_start:
{
size_t v_i_boxed_1943_; size_t v_stop_boxed_1944_; lean_object* v_res_1945_; 
v_i_boxed_1943_ = lean_unbox_usize(v_i_1940_);
lean_dec(v_i_1940_);
v_stop_boxed_1944_ = lean_unbox_usize(v_stop_1941_);
lean_dec(v_stop_1941_);
v_res_1945_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_as_1939_, v_i_boxed_1943_, v_stop_boxed_1944_, v_b_1942_);
lean_dec_ref(v_as_1939_);
return v_res_1945_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0(void){
_start:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1946_ = lean_unsigned_to_nat(32u);
v___x_1947_ = lean_mk_empty_array_with_capacity(v___x_1946_);
v___x_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1947_);
return v___x_1948_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1(void){
_start:
{
size_t v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1949_ = ((size_t)5ULL);
v___x_1950_ = lean_unsigned_to_nat(0u);
v___x_1951_ = lean_unsigned_to_nat(32u);
v___x_1952_ = lean_mk_empty_array_with_capacity(v___x_1951_);
v___x_1953_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0);
v___x_1954_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1954_, 0, v___x_1953_);
lean_ctor_set(v___x_1954_, 1, v___x_1952_);
lean_ctor_set(v___x_1954_, 2, v___x_1950_);
lean_ctor_set(v___x_1954_, 3, v___x_1950_);
lean_ctor_set_usize(v___x_1954_, 4, v___x_1949_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(lean_object* v___y_1955_){
_start:
{
lean_object* v___x_1957_; lean_object* v_traceState_1958_; lean_object* v_traces_1959_; lean_object* v___x_1960_; lean_object* v_traceState_1961_; lean_object* v_env_1962_; lean_object* v_nextMacroScope_1963_; lean_object* v_ngen_1964_; lean_object* v_auxDeclNGen_1965_; lean_object* v_cache_1966_; lean_object* v_messages_1967_; lean_object* v_infoState_1968_; lean_object* v_snapshotTasks_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1988_; 
v___x_1957_ = lean_st_ref_get(v___y_1955_);
v_traceState_1958_ = lean_ctor_get(v___x_1957_, 4);
lean_inc_ref(v_traceState_1958_);
lean_dec(v___x_1957_);
v_traces_1959_ = lean_ctor_get(v_traceState_1958_, 0);
lean_inc_ref(v_traces_1959_);
lean_dec_ref(v_traceState_1958_);
v___x_1960_ = lean_st_ref_take(v___y_1955_);
v_traceState_1961_ = lean_ctor_get(v___x_1960_, 4);
v_env_1962_ = lean_ctor_get(v___x_1960_, 0);
v_nextMacroScope_1963_ = lean_ctor_get(v___x_1960_, 1);
v_ngen_1964_ = lean_ctor_get(v___x_1960_, 2);
v_auxDeclNGen_1965_ = lean_ctor_get(v___x_1960_, 3);
v_cache_1966_ = lean_ctor_get(v___x_1960_, 5);
v_messages_1967_ = lean_ctor_get(v___x_1960_, 6);
v_infoState_1968_ = lean_ctor_get(v___x_1960_, 7);
v_snapshotTasks_1969_ = lean_ctor_get(v___x_1960_, 8);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1971_ = v___x_1960_;
v_isShared_1972_ = v_isSharedCheck_1988_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_snapshotTasks_1969_);
lean_inc(v_infoState_1968_);
lean_inc(v_messages_1967_);
lean_inc(v_cache_1966_);
lean_inc(v_traceState_1961_);
lean_inc(v_auxDeclNGen_1965_);
lean_inc(v_ngen_1964_);
lean_inc(v_nextMacroScope_1963_);
lean_inc(v_env_1962_);
lean_dec(v___x_1960_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1988_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
uint64_t v_tid_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1986_; 
v_tid_1973_ = lean_ctor_get_uint64(v_traceState_1961_, sizeof(void*)*1);
v_isSharedCheck_1986_ = !lean_is_exclusive(v_traceState_1961_);
if (v_isSharedCheck_1986_ == 0)
{
lean_object* v_unused_1987_; 
v_unused_1987_ = lean_ctor_get(v_traceState_1961_, 0);
lean_dec(v_unused_1987_);
v___x_1975_ = v_traceState_1961_;
v_isShared_1976_ = v_isSharedCheck_1986_;
goto v_resetjp_1974_;
}
else
{
lean_dec(v_traceState_1961_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1986_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1977_; lean_object* v___x_1979_; 
v___x_1977_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 0, v___x_1977_);
v___x_1979_ = v___x_1975_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v___x_1977_);
lean_ctor_set_uint64(v_reuseFailAlloc_1985_, sizeof(void*)*1, v_tid_1973_);
v___x_1979_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v___x_1981_; 
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 4, v___x_1979_);
v___x_1981_ = v___x_1971_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_env_1962_);
lean_ctor_set(v_reuseFailAlloc_1984_, 1, v_nextMacroScope_1963_);
lean_ctor_set(v_reuseFailAlloc_1984_, 2, v_ngen_1964_);
lean_ctor_set(v_reuseFailAlloc_1984_, 3, v_auxDeclNGen_1965_);
lean_ctor_set(v_reuseFailAlloc_1984_, 4, v___x_1979_);
lean_ctor_set(v_reuseFailAlloc_1984_, 5, v_cache_1966_);
lean_ctor_set(v_reuseFailAlloc_1984_, 6, v_messages_1967_);
lean_ctor_set(v_reuseFailAlloc_1984_, 7, v_infoState_1968_);
lean_ctor_set(v_reuseFailAlloc_1984_, 8, v_snapshotTasks_1969_);
v___x_1981_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1982_ = lean_st_ref_put(v___y_1955_, v___x_1981_);
v___x_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1983_, 0, v_traces_1959_);
return v___x_1983_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___boxed(lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_1989_);
lean_dec(v___y_1989_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(lean_object* v_hi_1992_, lean_object* v_pivot_1993_, lean_object* v_as_1994_, lean_object* v_i_1995_, lean_object* v_k_1996_){
_start:
{
uint8_t v___x_1997_; 
v___x_1997_ = lean_nat_dec_lt(v_k_1996_, v_hi_1992_);
if (v___x_1997_ == 0)
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
lean_dec(v_k_1996_);
v___x_1998_ = lean_array_fswap(v_as_1994_, v_i_1995_, v_hi_1992_);
v___x_1999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1999_, 0, v_i_1995_);
lean_ctor_set(v___x_1999_, 1, v___x_1998_);
return v___x_1999_;
}
else
{
lean_object* v___x_2000_; lean_object* v_fst_2001_; lean_object* v_fst_2002_; lean_object* v_fst_2003_; lean_object* v_fst_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; uint8_t v___x_2007_; 
v___x_2000_ = lean_array_fget_borrowed(v_as_1994_, v_k_1996_);
v_fst_2001_ = lean_ctor_get(v___x_2000_, 0);
v_fst_2002_ = lean_ctor_get(v_pivot_1993_, 0);
v_fst_2003_ = lean_ctor_get(v_fst_2001_, 0);
v_fst_2004_ = lean_ctor_get(v_fst_2002_, 0);
v___x_2005_ = lean_unsigned_to_nat(1u);
v___x_2006_ = lean_nat_add(v_fst_2003_, v___x_2005_);
v___x_2007_ = lean_nat_dec_le(v___x_2006_, v_fst_2004_);
lean_dec(v___x_2006_);
if (v___x_2007_ == 0)
{
lean_object* v___x_2008_; 
v___x_2008_ = lean_nat_add(v_k_1996_, v___x_2005_);
lean_dec(v_k_1996_);
v_k_1996_ = v___x_2008_;
goto _start;
}
else
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2010_ = lean_array_fswap(v_as_1994_, v_i_1995_, v_k_1996_);
v___x_2011_ = lean_nat_add(v_i_1995_, v___x_2005_);
lean_dec(v_i_1995_);
v___x_2012_ = lean_nat_add(v_k_1996_, v___x_2005_);
lean_dec(v_k_1996_);
v_as_1994_ = v___x_2010_;
v_i_1995_ = v___x_2011_;
v_k_1996_ = v___x_2012_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg___boxed(lean_object* v_hi_2014_, lean_object* v_pivot_2015_, lean_object* v_as_2016_, lean_object* v_i_2017_, lean_object* v_k_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_2014_, v_pivot_2015_, v_as_2016_, v_i_2017_, v_k_2018_);
lean_dec_ref(v_pivot_2015_);
lean_dec(v_hi_2014_);
return v_res_2019_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(lean_object* v_x_2020_, lean_object* v_x_2021_){
_start:
{
lean_object* v_fst_2022_; lean_object* v_fst_2023_; lean_object* v_fst_2024_; lean_object* v_fst_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; uint8_t v___x_2028_; 
v_fst_2022_ = lean_ctor_get(v_x_2020_, 0);
v_fst_2023_ = lean_ctor_get(v_x_2021_, 0);
v_fst_2024_ = lean_ctor_get(v_fst_2022_, 0);
v_fst_2025_ = lean_ctor_get(v_fst_2023_, 0);
v___x_2026_ = lean_unsigned_to_nat(1u);
v___x_2027_ = lean_nat_add(v_fst_2024_, v___x_2026_);
v___x_2028_ = lean_nat_dec_le(v___x_2027_, v_fst_2025_);
lean_dec(v___x_2027_);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0___boxed(lean_object* v_x_2029_, lean_object* v_x_2030_){
_start:
{
uint8_t v_res_2031_; lean_object* v_r_2032_; 
v_res_2031_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v_x_2029_, v_x_2030_);
lean_dec_ref(v_x_2030_);
lean_dec_ref(v_x_2029_);
v_r_2032_ = lean_box(v_res_2031_);
return v_r_2032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(lean_object* v_n_2033_, lean_object* v_as_2034_, lean_object* v_lo_2035_, lean_object* v_hi_2036_){
_start:
{
lean_object* v___y_2038_; uint8_t v___x_2048_; 
v___x_2048_ = lean_nat_dec_lt(v_lo_2035_, v_hi_2036_);
if (v___x_2048_ == 0)
{
lean_dec(v_lo_2035_);
return v_as_2034_;
}
else
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v_mid_2051_; lean_object* v___y_2053_; lean_object* v___y_2059_; lean_object* v___x_2064_; lean_object* v___x_2065_; uint8_t v___x_2066_; 
v___x_2049_ = lean_nat_add(v_lo_2035_, v_hi_2036_);
v___x_2050_ = lean_unsigned_to_nat(1u);
v_mid_2051_ = lean_nat_shiftr(v___x_2049_, v___x_2050_);
lean_dec(v___x_2049_);
v___x_2064_ = lean_array_fget_borrowed(v_as_2034_, v_mid_2051_);
v___x_2065_ = lean_array_fget_borrowed(v_as_2034_, v_lo_2035_);
v___x_2066_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2064_, v___x_2065_);
if (v___x_2066_ == 0)
{
v___y_2059_ = v_as_2034_;
goto v___jp_2058_;
}
else
{
lean_object* v___x_2067_; 
v___x_2067_ = lean_array_fswap(v_as_2034_, v_lo_2035_, v_mid_2051_);
v___y_2059_ = v___x_2067_;
goto v___jp_2058_;
}
v___jp_2052_:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; uint8_t v___x_2056_; 
v___x_2054_ = lean_array_fget_borrowed(v___y_2053_, v_mid_2051_);
v___x_2055_ = lean_array_fget_borrowed(v___y_2053_, v_hi_2036_);
v___x_2056_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2054_, v___x_2055_);
if (v___x_2056_ == 0)
{
lean_dec(v_mid_2051_);
v___y_2038_ = v___y_2053_;
goto v___jp_2037_;
}
else
{
lean_object* v___x_2057_; 
v___x_2057_ = lean_array_fswap(v___y_2053_, v_mid_2051_, v_hi_2036_);
lean_dec(v_mid_2051_);
v___y_2038_ = v___x_2057_;
goto v___jp_2037_;
}
}
v___jp_2058_:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; uint8_t v___x_2062_; 
v___x_2060_ = lean_array_fget_borrowed(v___y_2059_, v_hi_2036_);
v___x_2061_ = lean_array_fget_borrowed(v___y_2059_, v_lo_2035_);
v___x_2062_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2060_, v___x_2061_);
if (v___x_2062_ == 0)
{
v___y_2053_ = v___y_2059_;
goto v___jp_2052_;
}
else
{
lean_object* v___x_2063_; 
v___x_2063_ = lean_array_fswap(v___y_2059_, v_lo_2035_, v_hi_2036_);
v___y_2053_ = v___x_2063_;
goto v___jp_2052_;
}
}
}
v___jp_2037_:
{
lean_object* v_pivot_2039_; lean_object* v___x_2040_; lean_object* v_fst_2041_; lean_object* v_snd_2042_; uint8_t v___x_2043_; 
v_pivot_2039_ = lean_array_fget(v___y_2038_, v_hi_2036_);
lean_inc_n(v_lo_2035_, 2);
v___x_2040_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_2036_, v_pivot_2039_, v___y_2038_, v_lo_2035_, v_lo_2035_);
lean_dec(v_pivot_2039_);
v_fst_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_fst_2041_);
v_snd_2042_ = lean_ctor_get(v___x_2040_, 1);
lean_inc(v_snd_2042_);
lean_dec_ref(v___x_2040_);
v___x_2043_ = lean_nat_dec_le(v_hi_2036_, v_fst_2041_);
if (v___x_2043_ == 0)
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2044_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_2033_, v_snd_2042_, v_lo_2035_, v_fst_2041_);
v___x_2045_ = lean_unsigned_to_nat(1u);
v___x_2046_ = lean_nat_add(v_fst_2041_, v___x_2045_);
lean_dec(v_fst_2041_);
v_as_2034_ = v___x_2044_;
v_lo_2035_ = v___x_2046_;
goto _start;
}
else
{
lean_dec(v_fst_2041_);
lean_dec(v_lo_2035_);
return v_snd_2042_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___boxed(lean_object* v_n_2068_, lean_object* v_as_2069_, lean_object* v_lo_2070_, lean_object* v_hi_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_2068_, v_as_2069_, v_lo_2070_, v_hi_2071_);
lean_dec(v_hi_2071_);
lean_dec(v_n_2068_);
return v_res_2072_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0(void){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2073_ = lean_box(0);
v___x_2074_ = lean_unsigned_to_nat(16u);
v___x_2075_ = lean_mk_array(v___x_2074_, v___x_2073_);
return v___x_2075_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1(void){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v_pos2traces_2078_; 
v___x_2076_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0, &l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0);
v___x_2077_ = lean_unsigned_to_nat(0u);
v_pos2traces_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos2traces_2078_, 0, v___x_2077_);
lean_ctor_set(v_pos2traces_2078_, 1, v___x_2076_);
return v_pos2traces_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10(lean_object* v___y_2079_, lean_object* v___y_2080_){
_start:
{
lean_object* v_toCold_2085_; lean_object* v_options_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v_toCold_2085_ = lean_ctor_get(v___y_2079_, 0);
v_options_2086_ = lean_ctor_get(v_toCold_2085_, 2);
v___x_2087_ = l_Lean_trace_profiler_output;
v___x_2088_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(v_options_2086_, v___x_2087_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v___x_2089_; uint8_t v___x_2090_; 
v___x_2089_ = l_Lean_trace_profiler_serve;
v___x_2090_ = l_Lean_Option_get___at___00main_spec__8(v_options_2086_, v___x_2089_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2154_; 
v___x_2091_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_2080_);
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2094_ = v___x_2091_;
v_isShared_2095_ = v_isSharedCheck_2154_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2091_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2154_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
uint8_t v___x_2096_; 
v___x_2096_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_2092_);
if (v___x_2096_ == 0)
{
lean_object* v___x_2097_; lean_object* v_pos2traces_2098_; lean_object* v___x_2099_; 
lean_del_object(v___x_2094_);
v___x_2097_ = lean_unsigned_to_nat(0u);
v_pos2traces_2098_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1, &l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1);
v___x_2099_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(v___x_2096_, v_a_2092_, v_pos2traces_2098_, v___y_2079_, v___y_2080_);
lean_dec(v_a_2092_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v___y_2102_; lean_object* v___y_2116_; lean_object* v___y_2117_; lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v___y_2122_; lean_object* v___y_2123_; lean_object* v___y_2124_; lean_object* v___y_2125_; lean_object* v___y_2128_; lean_object* v_size_2134_; lean_object* v_buckets_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; uint8_t v___x_2138_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_a_2100_);
lean_dec_ref_known(v___x_2099_, 1);
v_size_2134_ = lean_ctor_get(v_a_2100_, 0);
lean_inc(v_size_2134_);
v_buckets_2135_ = lean_ctor_get(v_a_2100_, 1);
lean_inc_ref(v_buckets_2135_);
lean_dec(v_a_2100_);
v___x_2136_ = lean_mk_empty_array_with_capacity(v_size_2134_);
lean_dec(v_size_2134_);
v___x_2137_ = lean_array_get_size(v_buckets_2135_);
v___x_2138_ = lean_nat_dec_lt(v___x_2097_, v___x_2137_);
if (v___x_2138_ == 0)
{
lean_dec_ref(v_buckets_2135_);
v___y_2128_ = v___x_2136_;
goto v___jp_2127_;
}
else
{
size_t v___x_2139_; size_t v___x_2140_; lean_object* v___x_2141_; 
v___x_2139_ = ((size_t)0ULL);
v___x_2140_ = lean_usize_of_nat(v___x_2137_);
v___x_2141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_buckets_2135_, v___x_2139_, v___x_2140_, v___x_2136_);
lean_dec_ref(v_buckets_2135_);
v___y_2128_ = v___x_2141_;
goto v___jp_2127_;
}
v___jp_2101_:
{
lean_object* v___x_2103_; size_t v_sz_2104_; size_t v___x_2105_; lean_object* v___x_2106_; 
v___x_2103_ = lean_box(0);
v_sz_2104_ = lean_array_size(v___y_2102_);
v___x_2105_ = ((size_t)0ULL);
v___x_2106_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(v___x_2090_, v___y_2102_, v_sz_2104_, v___x_2105_, v___x_2103_, v___y_2079_, v___y_2080_);
lean_dec_ref(v___y_2102_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2113_ == 0)
{
lean_object* v_unused_2114_; 
v_unused_2114_ = lean_ctor_get(v___x_2106_, 0);
lean_dec(v_unused_2114_);
v___x_2108_ = v___x_2106_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_dec(v___x_2106_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 0, v___x_2103_);
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v___x_2103_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
else
{
return v___x_2106_;
}
}
v___jp_2115_:
{
lean_object* v___x_2120_; 
v___x_2120_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
lean_dec(v___y_2119_);
lean_dec(v___y_2116_);
v___y_2102_ = v___x_2120_;
goto v___jp_2101_;
}
v___jp_2121_:
{
uint8_t v___x_2126_; 
v___x_2126_ = lean_nat_dec_le(v___y_2125_, v___y_2124_);
if (v___x_2126_ == 0)
{
lean_dec(v___y_2124_);
lean_inc(v___y_2125_);
v___y_2116_ = v___y_2122_;
v___y_2117_ = v___y_2123_;
v___y_2118_ = v___y_2125_;
v___y_2119_ = v___y_2125_;
goto v___jp_2115_;
}
else
{
v___y_2116_ = v___y_2122_;
v___y_2117_ = v___y_2123_;
v___y_2118_ = v___y_2125_;
v___y_2119_ = v___y_2124_;
goto v___jp_2115_;
}
}
v___jp_2127_:
{
lean_object* v___x_2129_; uint8_t v___x_2130_; 
v___x_2129_ = lean_array_get_size(v___y_2128_);
v___x_2130_ = lean_nat_dec_eq(v___x_2129_, v___x_2097_);
if (v___x_2130_ == 0)
{
lean_object* v___x_2131_; lean_object* v___x_2132_; uint8_t v___x_2133_; 
v___x_2131_ = lean_unsigned_to_nat(1u);
v___x_2132_ = lean_nat_sub(v___x_2129_, v___x_2131_);
v___x_2133_ = lean_nat_dec_le(v___x_2097_, v___x_2132_);
if (v___x_2133_ == 0)
{
lean_inc(v___x_2132_);
v___y_2122_ = v___x_2129_;
v___y_2123_ = v___y_2128_;
v___y_2124_ = v___x_2132_;
v___y_2125_ = v___x_2132_;
goto v___jp_2121_;
}
else
{
v___y_2122_ = v___x_2129_;
v___y_2123_ = v___y_2128_;
v___y_2124_ = v___x_2132_;
v___y_2125_ = v___x_2097_;
goto v___jp_2121_;
}
}
else
{
v___y_2102_ = v___y_2128_;
goto v___jp_2101_;
}
}
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
v_a_2142_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2099_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2099_);
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
else
{
lean_object* v___x_2150_; lean_object* v___x_2152_; 
lean_dec(v_a_2092_);
v___x_2150_ = lean_box(0);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v___x_2150_);
v___x_2152_ = v___x_2094_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 1, 0);
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
else
{
goto v___jp_2082_;
}
}
else
{
lean_dec_ref_known(v___x_2088_, 1);
goto v___jp_2082_;
}
v___jp_2082_:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2083_ = lean_box(0);
v___x_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
return v___x_2084_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10___boxed(lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_){
_start:
{
lean_object* v_res_2158_; 
v_res_2158_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2155_, v___y_2156_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(lean_object* v_as_2159_, size_t v_sz_2160_, size_t v_i_2161_, lean_object* v_b_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
uint8_t v___x_2166_; 
v___x_2166_ = lean_usize_dec_lt(v_i_2161_, v_sz_2160_);
if (v___x_2166_ == 0)
{
lean_object* v___x_2167_; 
v___x_2167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2167_, 0, v_b_2162_);
return v___x_2167_;
}
else
{
lean_object* v_toCold_2168_; lean_object* v_options_2169_; lean_object* v___x_2170_; lean_object* v_a_2171_; lean_object* v___x_2172_; 
v_toCold_2168_ = lean_ctor_get(v___y_2163_, 0);
v_options_2169_ = lean_ctor_get(v_toCold_2168_, 2);
v___x_2170_ = lean_box(0);
v_a_2171_ = lean_array_uget_borrowed(v_as_2159_, v_i_2161_);
lean_inc_ref(v_options_2169_);
lean_inc(v_a_2171_);
v___x_2172_ = l_Lean_Compiler_LCNF_resumeCompilation(v_a_2171_, v_options_2169_, v___y_2163_, v___y_2164_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v___x_2173_; 
lean_dec_ref_known(v___x_2172_, 1);
v___x_2173_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2163_, v___y_2164_);
if (lean_obj_tag(v___x_2173_) == 0)
{
size_t v___x_2174_; size_t v___x_2175_; 
lean_dec_ref_known(v___x_2173_, 1);
v___x_2174_ = ((size_t)1ULL);
v___x_2175_ = lean_usize_add(v_i_2161_, v___x_2174_);
v_i_2161_ = v___x_2175_;
v_b_2162_ = v___x_2170_;
goto _start;
}
else
{
return v___x_2173_;
}
}
else
{
lean_object* v_a_2177_; lean_object* v___x_2178_; 
v_a_2177_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_a_2177_);
lean_dec_ref_known(v___x_2172_, 1);
v___x_2178_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2163_, v___y_2164_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2185_; 
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2185_ == 0)
{
lean_object* v_unused_2186_; 
v_unused_2186_ = lean_ctor_get(v___x_2178_, 0);
lean_dec(v_unused_2186_);
v___x_2180_ = v___x_2178_;
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
else
{
lean_dec(v___x_2178_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2183_; 
if (v_isShared_2181_ == 0)
{
lean_ctor_set_tag(v___x_2180_, 1);
lean_ctor_set(v___x_2180_, 0, v_a_2177_);
v___x_2183_ = v___x_2180_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_a_2177_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
else
{
lean_dec(v_a_2177_);
return v___x_2178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11___boxed(lean_object* v_as_2187_, lean_object* v_sz_2188_, lean_object* v_i_2189_, lean_object* v_b_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
size_t v_sz_boxed_2194_; size_t v_i_boxed_2195_; lean_object* v_res_2196_; 
v_sz_boxed_2194_ = lean_unbox_usize(v_sz_2188_);
lean_dec(v_sz_2188_);
v_i_boxed_2195_ = lean_unbox_usize(v_i_2189_);
lean_dec(v_i_2189_);
v_res_2196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(v_as_2187_, v_sz_boxed_2194_, v_i_boxed_2195_, v_b_2190_, v___y_2191_, v___y_2192_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec_ref(v_as_2187_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(lean_object* v_as_2197_, size_t v_sz_2198_, size_t v_i_2199_, lean_object* v_b_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
uint8_t v___x_2204_; 
v___x_2204_ = lean_usize_dec_lt(v_i_2199_, v_sz_2198_);
if (v___x_2204_ == 0)
{
lean_object* v___x_2205_; 
v___x_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2205_, 0, v_b_2200_);
return v___x_2205_;
}
else
{
lean_object* v_a_2206_; lean_object* v_declNames_2207_; lean_object* v___x_2208_; size_t v_sz_2209_; size_t v___x_2210_; lean_object* v___x_2211_; 
v_a_2206_ = lean_array_uget_borrowed(v_as_2197_, v_i_2199_);
v_declNames_2207_ = lean_ctor_get(v_a_2206_, 0);
v___x_2208_ = lean_box(0);
v_sz_2209_ = lean_array_size(v_declNames_2207_);
v___x_2210_ = ((size_t)0ULL);
v___x_2211_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(v_declNames_2207_, v_sz_2209_, v___x_2210_, v___x_2208_, v___y_2201_, v___y_2202_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_object* v___x_2212_; 
lean_dec_ref_known(v___x_2211_, 1);
v___x_2212_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v___y_2202_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v_a_2213_; lean_object* v_unreported_2214_; lean_object* v___x_2215_; 
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
lean_inc(v_a_2213_);
lean_dec_ref_known(v___x_2212_, 1);
v_unreported_2214_ = lean_ctor_get(v_a_2213_, 1);
lean_inc_ref(v_unreported_2214_);
lean_dec(v_a_2213_);
v___x_2215_ = l_Lean_PersistentArray_forIn___at___00main_spec__12(v_unreported_2214_, v___x_2208_, v___y_2201_, v___y_2202_);
lean_dec_ref(v_unreported_2214_);
if (lean_obj_tag(v___x_2215_) == 0)
{
size_t v___x_2216_; size_t v___x_2217_; 
lean_dec_ref_known(v___x_2215_, 1);
v___x_2216_ = ((size_t)1ULL);
v___x_2217_ = lean_usize_add(v_i_2199_, v___x_2216_);
v_i_2199_ = v___x_2217_;
v_b_2200_ = v___x_2208_;
goto _start;
}
else
{
return v___x_2215_;
}
}
else
{
lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2226_; 
v_a_2219_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2221_ = v___x_2212_;
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___x_2212_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2224_; 
if (v_isShared_2222_ == 0)
{
v___x_2224_ = v___x_2221_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_a_2219_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
}
else
{
return v___x_2211_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13___boxed(lean_object* v_as_2227_, lean_object* v_sz_2228_, lean_object* v_i_2229_, lean_object* v_b_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
size_t v_sz_boxed_2234_; size_t v_i_boxed_2235_; lean_object* v_res_2236_; 
v_sz_boxed_2234_ = lean_unbox_usize(v_sz_2228_);
lean_dec(v_sz_2228_);
v_i_boxed_2235_ = lean_unbox_usize(v_i_2229_);
lean_dec(v_i_2229_);
v_res_2236_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(v_as_2227_, v_sz_boxed_2234_, v_i_boxed_2235_, v_b_2230_, v___y_2231_, v___y_2232_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec_ref(v_as_2227_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(lean_object* v_as_2237_, size_t v_i_2238_, size_t v_stop_2239_, lean_object* v_b_2240_){
_start:
{
uint8_t v___x_2241_; 
v___x_2241_ = lean_usize_dec_eq(v_i_2238_, v_stop_2239_);
if (v___x_2241_ == 0)
{
lean_object* v___x_2242_; lean_object* v_name_2243_; lean_object* v___x_2244_; size_t v___x_2245_; size_t v___x_2246_; 
v___x_2242_ = lean_array_uget_borrowed(v_as_2237_, v_i_2238_);
v_name_2243_ = lean_ctor_get(v___x_2242_, 0);
lean_inc(v_name_2243_);
v___x_2244_ = l_Lean_Compiler_LCNF_setDeclPublic(v_b_2240_, v_name_2243_);
v___x_2245_ = ((size_t)1ULL);
v___x_2246_ = lean_usize_add(v_i_2238_, v___x_2245_);
v_i_2238_ = v___x_2246_;
v_b_2240_ = v___x_2244_;
goto _start;
}
else
{
return v_b_2240_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___boxed(lean_object* v_as_2248_, lean_object* v_i_2249_, lean_object* v_stop_2250_, lean_object* v_b_2251_){
_start:
{
size_t v_i_boxed_2252_; size_t v_stop_boxed_2253_; lean_object* v_res_2254_; 
v_i_boxed_2252_ = lean_unbox_usize(v_i_2249_);
lean_dec(v_i_2249_);
v_stop_boxed_2253_ = lean_unbox_usize(v_stop_2250_);
lean_dec(v_stop_2250_);
v_res_2254_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v_as_2248_, v_i_boxed_2252_, v_stop_boxed_2253_, v_b_2251_);
lean_dec_ref(v_as_2248_);
return v_res_2254_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0(uint8_t v_suppressElabErrors_2255_, uint8_t v___y_2256_, lean_object* v_x_2257_){
_start:
{
if (lean_obj_tag(v_x_2257_) == 1)
{
lean_object* v_pre_2258_; 
v_pre_2258_ = lean_ctor_get(v_x_2257_, 0);
switch(lean_obj_tag(v_pre_2258_))
{
case 1:
{
lean_object* v_pre_2259_; 
v_pre_2259_ = lean_ctor_get(v_pre_2258_, 0);
switch(lean_obj_tag(v_pre_2259_))
{
case 0:
{
lean_object* v_str_2260_; lean_object* v_str_2261_; lean_object* v___x_2262_; uint8_t v___x_2263_; 
v_str_2260_ = lean_ctor_get(v_x_2257_, 1);
v_str_2261_ = lean_ctor_get(v_pre_2258_, 1);
v___x_2262_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0));
v___x_2263_ = lean_string_dec_eq(v_str_2261_, v___x_2262_);
if (v___x_2263_ == 0)
{
lean_object* v___x_2264_; uint8_t v___x_2265_; 
v___x_2264_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1));
v___x_2265_ = lean_string_dec_eq(v_str_2261_, v___x_2264_);
if (v___x_2265_ == 0)
{
return v___x_2265_;
}
else
{
lean_object* v___x_2266_; uint8_t v___x_2267_; 
v___x_2266_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2));
v___x_2267_ = lean_string_dec_eq(v_str_2260_, v___x_2266_);
if (v___x_2267_ == 0)
{
return v___x_2267_;
}
else
{
return v_suppressElabErrors_2255_;
}
}
}
else
{
lean_object* v___x_2268_; uint8_t v___x_2269_; 
v___x_2268_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3));
v___x_2269_ = lean_string_dec_eq(v_str_2260_, v___x_2268_);
if (v___x_2269_ == 0)
{
return v___x_2269_;
}
else
{
return v_suppressElabErrors_2255_;
}
}
}
case 1:
{
lean_object* v_pre_2270_; 
v_pre_2270_ = lean_ctor_get(v_pre_2259_, 0);
if (lean_obj_tag(v_pre_2270_) == 0)
{
lean_object* v_str_2271_; lean_object* v_str_2272_; lean_object* v_str_2273_; lean_object* v___x_2274_; uint8_t v___x_2275_; 
v_str_2271_ = lean_ctor_get(v_x_2257_, 1);
v_str_2272_ = lean_ctor_get(v_pre_2258_, 1);
v_str_2273_ = lean_ctor_get(v_pre_2259_, 1);
v___x_2274_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4));
v___x_2275_ = lean_string_dec_eq(v_str_2273_, v___x_2274_);
if (v___x_2275_ == 0)
{
return v___x_2275_;
}
else
{
lean_object* v___x_2276_; uint8_t v___x_2277_; 
v___x_2276_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5));
v___x_2277_ = lean_string_dec_eq(v_str_2272_, v___x_2276_);
if (v___x_2277_ == 0)
{
return v___x_2277_;
}
else
{
lean_object* v___x_2278_; uint8_t v___x_2279_; 
v___x_2278_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6));
v___x_2279_ = lean_string_dec_eq(v_str_2271_, v___x_2278_);
if (v___x_2279_ == 0)
{
return v___x_2279_;
}
else
{
return v_suppressElabErrors_2255_;
}
}
}
}
else
{
return v___y_2256_;
}
}
default: 
{
return v___y_2256_;
}
}
}
case 0:
{
lean_object* v_str_2280_; lean_object* v___x_2281_; uint8_t v___x_2282_; 
v_str_2280_ = lean_ctor_get(v_x_2257_, 1);
v___x_2281_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_2282_ = lean_string_dec_eq(v_str_2280_, v___x_2281_);
if (v___x_2282_ == 0)
{
return v___x_2282_;
}
else
{
return v_suppressElabErrors_2255_;
}
}
default: 
{
return v___y_2256_;
}
}
}
else
{
return v___y_2256_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0___boxed(lean_object* v_suppressElabErrors_2283_, lean_object* v___y_2284_, lean_object* v_x_2285_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2286_; uint8_t v___y_38057__boxed_2287_; uint8_t v_res_2288_; lean_object* v_r_2289_; 
v_suppressElabErrors_boxed_2286_ = lean_unbox(v_suppressElabErrors_2283_);
v___y_38057__boxed_2287_ = lean_unbox(v___y_2284_);
v_res_2288_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0(v_suppressElabErrors_boxed_2286_, v___y_38057__boxed_2287_, v_x_2285_);
lean_dec(v_x_2285_);
v_r_2289_ = lean_box(v_res_2288_);
return v_r_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(lean_object* v_ref_2290_, lean_object* v_msgData_2291_, uint8_t v_severity_2292_, uint8_t v_isSilent_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2300_; lean_object* v___y_2301_; lean_object* v___y_2302_; uint8_t v___y_2303_; uint8_t v___y_2304_; lean_object* v_currNamespace_2305_; lean_object* v_openDecls_2306_; lean_object* v___y_2307_; lean_object* v___y_2333_; lean_object* v___y_2334_; lean_object* v___y_2335_; lean_object* v___y_2336_; uint8_t v___y_2337_; lean_object* v___y_2338_; lean_object* v___y_2339_; uint8_t v___y_2340_; uint8_t v___y_2341_; lean_object* v___y_2342_; lean_object* v___y_2360_; lean_object* v___y_2361_; lean_object* v___y_2362_; lean_object* v___y_2363_; lean_object* v___y_2364_; uint8_t v___y_2365_; lean_object* v___y_2366_; uint8_t v___y_2367_; uint8_t v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2377_; uint8_t v___y_2378_; lean_object* v___y_2379_; uint8_t v___y_2380_; uint8_t v___y_2381_; uint8_t v___x_2386_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2393_; uint8_t v___y_2394_; uint8_t v___y_2395_; uint8_t v___y_2396_; uint8_t v___y_2398_; uint8_t v___x_2416_; 
v___x_2386_ = 2;
v___x_2416_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2292_, v___x_2386_);
if (v___x_2416_ == 0)
{
v___y_2398_ = v___x_2416_;
goto v___jp_2397_;
}
else
{
uint8_t v___x_2417_; 
lean_inc_ref(v_msgData_2291_);
v___x_2417_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2291_);
v___y_2398_ = v___x_2417_;
goto v___jp_2397_;
}
v___jp_2297_:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v_env_2312_; lean_object* v_nextMacroScope_2313_; lean_object* v_ngen_2314_; lean_object* v_auxDeclNGen_2315_; lean_object* v_traceState_2316_; lean_object* v_cache_2317_; lean_object* v_messages_2318_; lean_object* v_infoState_2319_; lean_object* v_snapshotTasks_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2331_; 
lean_inc(v_openDecls_2306_);
lean_inc(v_currNamespace_2305_);
v___x_2308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2308_, 0, v_currNamespace_2305_);
lean_ctor_set(v___x_2308_, 1, v_openDecls_2306_);
v___x_2309_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2308_);
lean_ctor_set(v___x_2309_, 1, v___y_2302_);
lean_inc_ref(v___y_2300_);
lean_inc_ref(v___y_2298_);
v___x_2310_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2310_, 0, v___y_2298_);
lean_ctor_set(v___x_2310_, 1, v___y_2301_);
lean_ctor_set(v___x_2310_, 2, v___y_2299_);
lean_ctor_set(v___x_2310_, 3, v___y_2300_);
lean_ctor_set(v___x_2310_, 4, v___x_2309_);
lean_ctor_set_uint8(v___x_2310_, sizeof(void*)*5, v___y_2304_);
lean_ctor_set_uint8(v___x_2310_, sizeof(void*)*5 + 1, v___y_2303_);
lean_ctor_set_uint8(v___x_2310_, sizeof(void*)*5 + 2, v_isSilent_2293_);
v___x_2311_ = lean_st_ref_take(v___y_2307_);
v_env_2312_ = lean_ctor_get(v___x_2311_, 0);
v_nextMacroScope_2313_ = lean_ctor_get(v___x_2311_, 1);
v_ngen_2314_ = lean_ctor_get(v___x_2311_, 2);
v_auxDeclNGen_2315_ = lean_ctor_get(v___x_2311_, 3);
v_traceState_2316_ = lean_ctor_get(v___x_2311_, 4);
v_cache_2317_ = lean_ctor_get(v___x_2311_, 5);
v_messages_2318_ = lean_ctor_get(v___x_2311_, 6);
v_infoState_2319_ = lean_ctor_get(v___x_2311_, 7);
v_snapshotTasks_2320_ = lean_ctor_get(v___x_2311_, 8);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2322_ = v___x_2311_;
v_isShared_2323_ = v_isSharedCheck_2331_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_snapshotTasks_2320_);
lean_inc(v_infoState_2319_);
lean_inc(v_messages_2318_);
lean_inc(v_cache_2317_);
lean_inc(v_traceState_2316_);
lean_inc(v_auxDeclNGen_2315_);
lean_inc(v_ngen_2314_);
lean_inc(v_nextMacroScope_2313_);
lean_inc(v_env_2312_);
lean_dec(v___x_2311_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2331_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2327_; 
v___x_2324_ = lean_box(0);
v___x_2325_ = l_Lean_MessageLog_add(v___x_2310_, v_messages_2318_);
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 6, v___x_2325_);
v___x_2327_ = v___x_2322_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_env_2312_);
lean_ctor_set(v_reuseFailAlloc_2330_, 1, v_nextMacroScope_2313_);
lean_ctor_set(v_reuseFailAlloc_2330_, 2, v_ngen_2314_);
lean_ctor_set(v_reuseFailAlloc_2330_, 3, v_auxDeclNGen_2315_);
lean_ctor_set(v_reuseFailAlloc_2330_, 4, v_traceState_2316_);
lean_ctor_set(v_reuseFailAlloc_2330_, 5, v_cache_2317_);
lean_ctor_set(v_reuseFailAlloc_2330_, 6, v___x_2325_);
lean_ctor_set(v_reuseFailAlloc_2330_, 7, v_infoState_2319_);
lean_ctor_set(v_reuseFailAlloc_2330_, 8, v_snapshotTasks_2320_);
v___x_2327_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2328_ = lean_st_ref_put(v___y_2307_, v___x_2327_);
v___x_2329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2324_);
return v___x_2329_;
}
}
}
v___jp_2332_:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2358_; 
v___x_2343_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2291_);
v___x_2344_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(v___x_2343_, v___y_2294_, v___y_2295_);
v_a_2345_ = lean_ctor_get(v___x_2344_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2347_ = v___x_2344_;
v_isShared_2348_ = v_isSharedCheck_2358_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2344_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2358_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
lean_inc_ref_n(v___y_2338_, 2);
v___x_2349_ = l_Lean_FileMap_toPosition(v___y_2338_, v___y_2339_);
lean_dec(v___y_2339_);
v___x_2350_ = l_Lean_FileMap_toPosition(v___y_2338_, v___y_2342_);
lean_dec(v___y_2342_);
v___x_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2350_);
v___x_2352_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1));
if (v___y_2337_ == 0)
{
lean_del_object(v___x_2347_);
lean_dec_ref(v___y_2334_);
v___y_2298_ = v___y_2336_;
v___y_2299_ = v___x_2351_;
v___y_2300_ = v___x_2352_;
v___y_2301_ = v___x_2349_;
v___y_2302_ = v_a_2345_;
v___y_2303_ = v___y_2340_;
v___y_2304_ = v___y_2341_;
v_currNamespace_2305_ = v___y_2335_;
v_openDecls_2306_ = v___y_2333_;
v___y_2307_ = v___y_2295_;
goto v___jp_2297_;
}
else
{
uint8_t v___x_2353_; 
lean_inc(v_a_2345_);
v___x_2353_ = l_Lean_MessageData_hasTag(v___y_2334_, v_a_2345_);
if (v___x_2353_ == 0)
{
lean_object* v___x_2354_; lean_object* v___x_2356_; 
lean_dec_ref_known(v___x_2351_, 1);
lean_dec_ref(v___x_2349_);
lean_dec(v_a_2345_);
v___x_2354_ = lean_box(0);
if (v_isShared_2348_ == 0)
{
lean_ctor_set(v___x_2347_, 0, v___x_2354_);
v___x_2356_ = v___x_2347_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2354_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
else
{
lean_del_object(v___x_2347_);
v___y_2298_ = v___y_2336_;
v___y_2299_ = v___x_2351_;
v___y_2300_ = v___x_2352_;
v___y_2301_ = v___x_2349_;
v___y_2302_ = v_a_2345_;
v___y_2303_ = v___y_2340_;
v___y_2304_ = v___y_2341_;
v_currNamespace_2305_ = v___y_2335_;
v_openDecls_2306_ = v___y_2333_;
v___y_2307_ = v___y_2295_;
goto v___jp_2297_;
}
}
}
}
v___jp_2359_:
{
lean_object* v___x_2370_; 
v___x_2370_ = l_Lean_Syntax_getTailPos_x3f(v___y_2364_, v___y_2368_);
lean_dec(v___y_2364_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_inc(v___y_2369_);
v___y_2333_ = v___y_2360_;
v___y_2334_ = v___y_2361_;
v___y_2335_ = v___y_2362_;
v___y_2336_ = v___y_2363_;
v___y_2337_ = v___y_2365_;
v___y_2338_ = v___y_2366_;
v___y_2339_ = v___y_2369_;
v___y_2340_ = v___y_2367_;
v___y_2341_ = v___y_2368_;
v___y_2342_ = v___y_2369_;
goto v___jp_2332_;
}
else
{
lean_object* v_val_2371_; 
v_val_2371_ = lean_ctor_get(v___x_2370_, 0);
lean_inc(v_val_2371_);
lean_dec_ref_known(v___x_2370_, 1);
v___y_2333_ = v___y_2360_;
v___y_2334_ = v___y_2361_;
v___y_2335_ = v___y_2362_;
v___y_2336_ = v___y_2363_;
v___y_2337_ = v___y_2365_;
v___y_2338_ = v___y_2366_;
v___y_2339_ = v___y_2369_;
v___y_2340_ = v___y_2367_;
v___y_2341_ = v___y_2368_;
v___y_2342_ = v_val_2371_;
goto v___jp_2332_;
}
}
v___jp_2372_:
{
lean_object* v_ref_2382_; lean_object* v___x_2383_; 
v_ref_2382_ = l_Lean_replaceRef(v_ref_2290_, v___y_2377_);
v___x_2383_ = l_Lean_Syntax_getPos_x3f(v_ref_2382_, v___y_2380_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v___x_2384_; 
v___x_2384_ = lean_unsigned_to_nat(0u);
v___y_2360_ = v___y_2373_;
v___y_2361_ = v___y_2374_;
v___y_2362_ = v___y_2375_;
v___y_2363_ = v___y_2376_;
v___y_2364_ = v_ref_2382_;
v___y_2365_ = v___y_2378_;
v___y_2366_ = v___y_2379_;
v___y_2367_ = v___y_2381_;
v___y_2368_ = v___y_2380_;
v___y_2369_ = v___x_2384_;
goto v___jp_2359_;
}
else
{
lean_object* v_val_2385_; 
v_val_2385_ = lean_ctor_get(v___x_2383_, 0);
lean_inc(v_val_2385_);
lean_dec_ref_known(v___x_2383_, 1);
v___y_2360_ = v___y_2373_;
v___y_2361_ = v___y_2374_;
v___y_2362_ = v___y_2375_;
v___y_2363_ = v___y_2376_;
v___y_2364_ = v_ref_2382_;
v___y_2365_ = v___y_2378_;
v___y_2366_ = v___y_2379_;
v___y_2367_ = v___y_2381_;
v___y_2368_ = v___y_2380_;
v___y_2369_ = v_val_2385_;
goto v___jp_2359_;
}
}
v___jp_2387_:
{
if (v___y_2396_ == 0)
{
v___y_2373_ = v___y_2389_;
v___y_2374_ = v___y_2390_;
v___y_2375_ = v___y_2392_;
v___y_2376_ = v___y_2388_;
v___y_2377_ = v___y_2393_;
v___y_2378_ = v___y_2394_;
v___y_2379_ = v___y_2391_;
v___y_2380_ = v___y_2395_;
v___y_2381_ = v_severity_2292_;
goto v___jp_2372_;
}
else
{
v___y_2373_ = v___y_2389_;
v___y_2374_ = v___y_2390_;
v___y_2375_ = v___y_2392_;
v___y_2376_ = v___y_2388_;
v___y_2377_ = v___y_2393_;
v___y_2378_ = v___y_2394_;
v___y_2379_ = v___y_2391_;
v___y_2380_ = v___y_2395_;
v___y_2381_ = v___x_2386_;
goto v___jp_2372_;
}
}
v___jp_2397_:
{
if (v___y_2398_ == 0)
{
lean_object* v_toCold_2399_; lean_object* v_ref_2400_; uint8_t v_suppressElabErrors_2401_; lean_object* v_fileName_2402_; lean_object* v_fileMap_2403_; lean_object* v_options_2404_; lean_object* v_currNamespace_2405_; lean_object* v_openDecls_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___f_2409_; uint8_t v___x_2410_; uint8_t v___x_2411_; 
v_toCold_2399_ = lean_ctor_get(v___y_2294_, 0);
v_ref_2400_ = lean_ctor_get(v___y_2294_, 2);
v_suppressElabErrors_2401_ = lean_ctor_get_uint8(v___y_2294_, sizeof(void*)*3 + 1);
v_fileName_2402_ = lean_ctor_get(v_toCold_2399_, 0);
v_fileMap_2403_ = lean_ctor_get(v_toCold_2399_, 1);
v_options_2404_ = lean_ctor_get(v_toCold_2399_, 2);
v_currNamespace_2405_ = lean_ctor_get(v_toCold_2399_, 4);
v_openDecls_2406_ = lean_ctor_get(v_toCold_2399_, 5);
v___x_2407_ = lean_box(v_suppressElabErrors_2401_);
v___x_2408_ = lean_box(v___y_2398_);
v___f_2409_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2409_, 0, v___x_2407_);
lean_closure_set(v___f_2409_, 1, v___x_2408_);
v___x_2410_ = 1;
v___x_2411_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2292_, v___x_2410_);
if (v___x_2411_ == 0)
{
v___y_2388_ = v_fileName_2402_;
v___y_2389_ = v_openDecls_2406_;
v___y_2390_ = v___f_2409_;
v___y_2391_ = v_fileMap_2403_;
v___y_2392_ = v_currNamespace_2405_;
v___y_2393_ = v_ref_2400_;
v___y_2394_ = v_suppressElabErrors_2401_;
v___y_2395_ = v___y_2398_;
v___y_2396_ = v___x_2411_;
goto v___jp_2387_;
}
else
{
lean_object* v___x_2412_; uint8_t v___x_2413_; 
v___x_2412_ = l_Lean_warningAsError;
v___x_2413_ = l_Lean_Option_get___at___00main_spec__8(v_options_2404_, v___x_2412_);
v___y_2388_ = v_fileName_2402_;
v___y_2389_ = v_openDecls_2406_;
v___y_2390_ = v___f_2409_;
v___y_2391_ = v_fileMap_2403_;
v___y_2392_ = v_currNamespace_2405_;
v___y_2393_ = v_ref_2400_;
v___y_2394_ = v_suppressElabErrors_2401_;
v___y_2395_ = v___y_2398_;
v___y_2396_ = v___x_2413_;
goto v___jp_2387_;
}
}
else
{
lean_object* v___x_2414_; lean_object* v___x_2415_; 
lean_dec_ref(v_msgData_2291_);
v___x_2414_ = lean_box(0);
v___x_2415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2414_);
return v___x_2415_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___boxed(lean_object* v_ref_2418_, lean_object* v_msgData_2419_, lean_object* v_severity_2420_, lean_object* v_isSilent_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_){
_start:
{
uint8_t v_severity_boxed_2425_; uint8_t v_isSilent_boxed_2426_; lean_object* v_res_2427_; 
v_severity_boxed_2425_ = lean_unbox(v_severity_2420_);
v_isSilent_boxed_2426_ = lean_unbox(v_isSilent_2421_);
v_res_2427_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(v_ref_2418_, v_msgData_2419_, v_severity_boxed_2425_, v_isSilent_boxed_2426_, v___y_2422_, v___y_2423_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec(v_ref_2418_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(lean_object* v_msgData_2428_, uint8_t v_severity_2429_, uint8_t v_isSilent_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v_ref_2434_; lean_object* v___x_2435_; 
v_ref_2434_ = lean_ctor_get(v___y_2431_, 2);
v___x_2435_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(v_ref_2434_, v_msgData_2428_, v_severity_2429_, v_isSilent_2430_, v___y_2431_, v___y_2432_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30___boxed(lean_object* v_msgData_2436_, lean_object* v_severity_2437_, lean_object* v_isSilent_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
uint8_t v_severity_boxed_2442_; uint8_t v_isSilent_boxed_2443_; lean_object* v_res_2444_; 
v_severity_boxed_2442_ = lean_unbox(v_severity_2437_);
v_isSilent_boxed_2443_ = lean_unbox(v_isSilent_2438_);
v_res_2444_ = l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(v_msgData_2436_, v_severity_boxed_2442_, v_isSilent_boxed_2443_, v___y_2439_, v___y_2440_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__14(lean_object* v_msgData_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
uint8_t v___x_2449_; uint8_t v___x_2450_; lean_object* v___x_2451_; 
v___x_2449_ = 2;
v___x_2450_ = 0;
v___x_2451_ = l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(v_msgData_2445_, v___x_2449_, v___x_2450_, v___y_2446_, v___y_2447_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__14___boxed(lean_object* v_msgData_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_Lean_logError___at___00main_spec__14(v_msgData_2452_, v___y_2453_, v___y_2454_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(lean_object* v_x2_2457_, lean_object* v_as_2458_, size_t v_i_2459_, size_t v_stop_2460_, lean_object* v_b_2461_){
_start:
{
uint8_t v___x_2462_; 
v___x_2462_ = lean_usize_dec_eq(v_i_2459_, v_stop_2460_);
if (v___x_2462_ == 0)
{
lean_object* v___x_2463_; lean_object* v___x_2464_; size_t v___x_2465_; size_t v___x_2466_; 
v___x_2463_ = lean_array_uget_borrowed(v_as_2458_, v_i_2459_);
lean_inc_ref(v_x2_2457_);
lean_inc(v___x_2463_);
v___x_2464_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2463_, v_x2_2457_, v_b_2461_);
v___x_2465_ = ((size_t)1ULL);
v___x_2466_ = lean_usize_add(v_i_2459_, v___x_2465_);
v_i_2459_ = v___x_2466_;
v_b_2461_ = v___x_2464_;
goto _start;
}
else
{
lean_dec_ref(v_x2_2457_);
return v_b_2461_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2___boxed(lean_object* v_x2_2468_, lean_object* v_as_2469_, lean_object* v_i_2470_, lean_object* v_stop_2471_, lean_object* v_b_2472_){
_start:
{
size_t v_i_boxed_2473_; size_t v_stop_boxed_2474_; lean_object* v_res_2475_; 
v_i_boxed_2473_ = lean_unbox_usize(v_i_2470_);
lean_dec(v_i_2470_);
v_stop_boxed_2474_ = lean_unbox_usize(v_stop_2471_);
lean_dec(v_stop_2471_);
v_res_2475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v_x2_2468_, v_as_2469_, v_i_boxed_2473_, v_stop_boxed_2474_, v_b_2472_);
lean_dec_ref(v_as_2469_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(lean_object* v_as_2476_, size_t v_i_2477_, size_t v_stop_2478_, lean_object* v_b_2479_){
_start:
{
lean_object* v___y_2481_; uint8_t v___x_2485_; 
v___x_2485_ = lean_usize_dec_eq(v_i_2477_, v_stop_2478_);
if (v___x_2485_ == 0)
{
lean_object* v___x_2486_; lean_object* v_declNames_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; uint8_t v___x_2490_; 
v___x_2486_ = lean_array_uget_borrowed(v_as_2476_, v_i_2477_);
v_declNames_2487_ = lean_ctor_get(v___x_2486_, 0);
v___x_2488_ = lean_unsigned_to_nat(0u);
v___x_2489_ = lean_array_get_size(v_declNames_2487_);
v___x_2490_ = lean_nat_dec_lt(v___x_2488_, v___x_2489_);
if (v___x_2490_ == 0)
{
v___y_2481_ = v_b_2479_;
goto v___jp_2480_;
}
else
{
uint8_t v___x_2491_; 
v___x_2491_ = lean_nat_dec_le(v___x_2489_, v___x_2489_);
if (v___x_2491_ == 0)
{
if (v___x_2490_ == 0)
{
v___y_2481_ = v_b_2479_;
goto v___jp_2480_;
}
else
{
size_t v___x_2492_; size_t v___x_2493_; lean_object* v___x_2494_; 
v___x_2492_ = ((size_t)0ULL);
v___x_2493_ = lean_usize_of_nat(v___x_2489_);
lean_inc(v___x_2486_);
v___x_2494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_2486_, v_declNames_2487_, v___x_2492_, v___x_2493_, v_b_2479_);
v___y_2481_ = v___x_2494_;
goto v___jp_2480_;
}
}
else
{
size_t v___x_2495_; size_t v___x_2496_; lean_object* v___x_2497_; 
v___x_2495_ = ((size_t)0ULL);
v___x_2496_ = lean_usize_of_nat(v___x_2489_);
lean_inc(v___x_2486_);
v___x_2497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_2486_, v_declNames_2487_, v___x_2495_, v___x_2496_, v_b_2479_);
v___y_2481_ = v___x_2497_;
goto v___jp_2480_;
}
}
}
else
{
return v_b_2479_;
}
v___jp_2480_:
{
size_t v___x_2482_; size_t v___x_2483_; 
v___x_2482_ = ((size_t)1ULL);
v___x_2483_ = lean_usize_add(v_i_2477_, v___x_2482_);
v_i_2477_ = v___x_2483_;
v_b_2479_ = v___y_2481_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___boxed(lean_object* v_as_2498_, lean_object* v_i_2499_, lean_object* v_stop_2500_, lean_object* v_b_2501_){
_start:
{
size_t v_i_boxed_2502_; size_t v_stop_boxed_2503_; lean_object* v_res_2504_; 
v_i_boxed_2502_ = lean_unbox_usize(v_i_2499_);
lean_dec(v_i_2499_);
v_stop_boxed_2503_ = lean_unbox_usize(v_stop_2500_);
lean_dec(v_stop_2500_);
v_res_2504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v_as_2498_, v_i_boxed_2502_, v_stop_boxed_2503_, v_b_2501_);
lean_dec_ref(v_as_2498_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(lean_object* v_a_2505_, lean_object* v_as_2506_, size_t v_i_2507_, size_t v_stop_2508_, lean_object* v_b_2509_){
_start:
{
lean_object* v___y_2511_; uint8_t v___x_2515_; 
v___x_2515_ = lean_usize_dec_eq(v_i_2507_, v_stop_2508_);
if (v___x_2515_ == 0)
{
lean_object* v___x_2516_; lean_object* v_name_2517_; uint8_t v___x_2518_; 
v___x_2516_ = lean_array_uget_borrowed(v_as_2506_, v_i_2507_);
v_name_2517_ = lean_ctor_get(v___x_2516_, 0);
lean_inc(v_name_2517_);
lean_inc_ref(v_a_2505_);
v___x_2518_ = l_Lean_isExtern(v_a_2505_, v_name_2517_);
if (v___x_2518_ == 0)
{
v___y_2511_ = v_b_2509_;
goto v___jp_2510_;
}
else
{
lean_object* v___x_2519_; 
lean_inc(v___x_2516_);
v___x_2519_ = lean_array_push(v_b_2509_, v___x_2516_);
v___y_2511_ = v___x_2519_;
goto v___jp_2510_;
}
}
else
{
lean_dec_ref(v_a_2505_);
return v_b_2509_;
}
v___jp_2510_:
{
size_t v___x_2512_; size_t v___x_2513_; 
v___x_2512_ = ((size_t)1ULL);
v___x_2513_ = lean_usize_add(v_i_2507_, v___x_2512_);
v_i_2507_ = v___x_2513_;
v_b_2509_ = v___y_2511_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19___boxed(lean_object* v_a_2520_, lean_object* v_as_2521_, lean_object* v_i_2522_, lean_object* v_stop_2523_, lean_object* v_b_2524_){
_start:
{
size_t v_i_boxed_2525_; size_t v_stop_boxed_2526_; lean_object* v_res_2527_; 
v_i_boxed_2525_ = lean_unbox_usize(v_i_2522_);
lean_dec(v_i_2522_);
v_stop_boxed_2526_ = lean_unbox_usize(v_stop_2523_);
lean_dec(v_stop_2523_);
v_res_2527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_2520_, v_as_2521_, v_i_boxed_2525_, v_stop_boxed_2526_, v_b_2524_);
lean_dec_ref(v_as_2521_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(lean_object* v_as_2528_, size_t v_sz_2529_, size_t v_i_2530_, lean_object* v_b_2531_){
_start:
{
uint8_t v___x_2533_; 
v___x_2533_ = lean_usize_dec_lt(v_i_2530_, v_sz_2529_);
if (v___x_2533_ == 0)
{
lean_object* v___x_2534_; 
v___x_2534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2534_, 0, v_b_2531_);
return v___x_2534_;
}
else
{
uint8_t v___x_2535_; lean_object* v_a_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; 
lean_dec_ref(v_b_2531_);
v___x_2535_ = 0;
v_a_2536_ = lean_array_uget_borrowed(v_as_2528_, v_i_2530_);
lean_inc(v_a_2536_);
v___x_2537_ = l_Lean_Message_toString(v_a_2536_, v___x_2535_);
v___x_2538_ = l_IO_eprintln___at___00main_spec__6(v___x_2537_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v___x_2539_; size_t v___x_2540_; size_t v___x_2541_; 
lean_dec_ref_known(v___x_2538_, 1);
v___x_2539_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_2540_ = ((size_t)1ULL);
v___x_2541_ = lean_usize_add(v_i_2530_, v___x_2540_);
v_i_2530_ = v___x_2541_;
v_b_2531_ = v___x_2539_;
goto _start;
}
else
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
v_a_2543_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v___x_2538_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2538_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2548_; 
if (v_isShared_2546_ == 0)
{
v___x_2548_ = v___x_2545_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27___boxed(lean_object* v_as_2551_, lean_object* v_sz_2552_, lean_object* v_i_2553_, lean_object* v_b_2554_, lean_object* v___y_2555_){
_start:
{
size_t v_sz_boxed_2556_; size_t v_i_boxed_2557_; lean_object* v_res_2558_; 
v_sz_boxed_2556_ = lean_unbox_usize(v_sz_2552_);
lean_dec(v_sz_2552_);
v_i_boxed_2557_ = lean_unbox_usize(v_i_2553_);
lean_dec(v_i_2553_);
v_res_2558_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(v_as_2551_, v_sz_boxed_2556_, v_i_boxed_2557_, v_b_2554_);
lean_dec_ref(v_as_2551_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(lean_object* v_as_2559_, size_t v_sz_2560_, size_t v_i_2561_, lean_object* v_b_2562_){
_start:
{
uint8_t v___x_2564_; 
v___x_2564_ = lean_usize_dec_lt(v_i_2561_, v_sz_2560_);
if (v___x_2564_ == 0)
{
lean_object* v___x_2565_; 
v___x_2565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2565_, 0, v_b_2562_);
return v___x_2565_;
}
else
{
uint8_t v___x_2566_; lean_object* v_a_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
lean_dec_ref(v_b_2562_);
v___x_2566_ = 0;
v_a_2567_ = lean_array_uget_borrowed(v_as_2559_, v_i_2561_);
lean_inc(v_a_2567_);
v___x_2568_ = l_Lean_Message_toString(v_a_2567_, v___x_2566_);
v___x_2569_ = l_IO_eprintln___at___00main_spec__6(v___x_2568_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v___x_2570_; size_t v___x_2571_; size_t v___x_2572_; lean_object* v___x_2573_; 
lean_dec_ref_known(v___x_2569_, 1);
v___x_2570_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_2571_ = ((size_t)1ULL);
v___x_2572_ = lean_usize_add(v_i_2561_, v___x_2571_);
v___x_2573_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(v_as_2559_, v_sz_2560_, v___x_2572_, v___x_2570_);
return v___x_2573_;
}
else
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
v_a_2574_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v___x_2569_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2569_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2574_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14___boxed(lean_object* v_as_2582_, lean_object* v_sz_2583_, lean_object* v_i_2584_, lean_object* v_b_2585_, lean_object* v___y_2586_){
_start:
{
size_t v_sz_boxed_2587_; size_t v_i_boxed_2588_; lean_object* v_res_2589_; 
v_sz_boxed_2587_ = lean_unbox_usize(v_sz_2583_);
lean_dec(v_sz_2583_);
v_i_boxed_2588_ = lean_unbox_usize(v_i_2584_);
lean_dec(v_i_2584_);
v_res_2589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(v_as_2582_, v_sz_boxed_2587_, v_i_boxed_2588_, v_b_2585_);
lean_dec_ref(v_as_2582_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(lean_object* v_init_2590_, lean_object* v_n_2591_, lean_object* v_b_2592_){
_start:
{
if (lean_obj_tag(v_n_2591_) == 0)
{
lean_object* v_cs_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; size_t v_sz_2597_; size_t v___x_2598_; lean_object* v___x_2599_; 
v_cs_2594_ = lean_ctor_get(v_n_2591_, 0);
v___x_2595_ = lean_box(0);
v___x_2596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2595_);
lean_ctor_set(v___x_2596_, 1, v_b_2592_);
v_sz_2597_ = lean_array_size(v_cs_2594_);
v___x_2598_ = ((size_t)0ULL);
v___x_2599_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_init_2590_, v_cs_2594_, v_sz_2597_, v___x_2598_, v___x_2596_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2614_; 
v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2602_ = v___x_2599_;
v_isShared_2603_ = v_isSharedCheck_2614_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2599_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2614_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v_fst_2604_; 
v_fst_2604_ = lean_ctor_get(v_a_2600_, 0);
if (lean_obj_tag(v_fst_2604_) == 0)
{
lean_object* v_snd_2605_; lean_object* v___x_2606_; lean_object* v___x_2608_; 
v_snd_2605_ = lean_ctor_get(v_a_2600_, 1);
lean_inc(v_snd_2605_);
lean_dec(v_a_2600_);
v___x_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2606_, 0, v_snd_2605_);
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 0, v___x_2606_);
v___x_2608_ = v___x_2602_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v___x_2606_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
else
{
lean_object* v_val_2610_; lean_object* v___x_2612_; 
lean_inc_ref(v_fst_2604_);
lean_dec(v_a_2600_);
v_val_2610_ = lean_ctor_get(v_fst_2604_, 0);
lean_inc(v_val_2610_);
lean_dec_ref_known(v_fst_2604_, 1);
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 0, v_val_2610_);
v___x_2612_ = v___x_2602_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_val_2610_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
else
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
v_a_2615_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2599_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2599_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2618_ == 0)
{
v___x_2620_ = v___x_2617_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2615_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
else
{
lean_object* v_vs_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; size_t v_sz_2626_; size_t v___x_2627_; lean_object* v___x_2628_; 
v_vs_2623_ = lean_ctor_get(v_n_2591_, 0);
v___x_2624_ = lean_box(0);
v___x_2625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2624_);
lean_ctor_set(v___x_2625_, 1, v_b_2592_);
v_sz_2626_ = lean_array_size(v_vs_2623_);
v___x_2627_ = ((size_t)0ULL);
v___x_2628_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(v_vs_2623_, v_sz_2626_, v___x_2627_, v___x_2625_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2643_; 
v_a_2629_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2631_ = v___x_2628_;
v_isShared_2632_ = v_isSharedCheck_2643_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2628_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2643_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v_fst_2633_; 
v_fst_2633_ = lean_ctor_get(v_a_2629_, 0);
if (lean_obj_tag(v_fst_2633_) == 0)
{
lean_object* v_snd_2634_; lean_object* v___x_2635_; lean_object* v___x_2637_; 
v_snd_2634_ = lean_ctor_get(v_a_2629_, 1);
lean_inc(v_snd_2634_);
lean_dec(v_a_2629_);
v___x_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2635_, 0, v_snd_2634_);
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 0, v___x_2635_);
v___x_2637_ = v___x_2631_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v___x_2635_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
else
{
lean_object* v_val_2639_; lean_object* v___x_2641_; 
lean_inc_ref(v_fst_2633_);
lean_dec(v_a_2629_);
v_val_2639_ = lean_ctor_get(v_fst_2633_, 0);
lean_inc(v_val_2639_);
lean_dec_ref_known(v_fst_2633_, 1);
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 0, v_val_2639_);
v___x_2641_ = v___x_2631_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_val_2639_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
v_a_2644_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2628_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2628_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(lean_object* v_init_2652_, lean_object* v_as_2653_, size_t v_sz_2654_, size_t v_i_2655_, lean_object* v_b_2656_){
_start:
{
uint8_t v___x_2658_; 
v___x_2658_ = lean_usize_dec_lt(v_i_2655_, v_sz_2654_);
if (v___x_2658_ == 0)
{
lean_object* v___x_2659_; 
v___x_2659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2659_, 0, v_b_2656_);
return v___x_2659_;
}
else
{
lean_object* v_snd_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2694_; 
v_snd_2660_ = lean_ctor_get(v_b_2656_, 1);
v_isSharedCheck_2694_ = !lean_is_exclusive(v_b_2656_);
if (v_isSharedCheck_2694_ == 0)
{
lean_object* v_unused_2695_; 
v_unused_2695_ = lean_ctor_get(v_b_2656_, 0);
lean_dec(v_unused_2695_);
v___x_2662_ = v_b_2656_;
v_isShared_2663_ = v_isSharedCheck_2694_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_snd_2660_);
lean_dec(v_b_2656_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2694_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2664_; lean_object* v_a_2665_; lean_object* v___x_2666_; 
v___x_2664_ = lean_box(0);
v_a_2665_ = lean_array_uget_borrowed(v_as_2653_, v_i_2655_);
lean_inc(v_snd_2660_);
v___x_2666_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2652_, v_a_2665_, v_snd_2660_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2685_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2669_ = v___x_2666_;
v_isShared_2670_ = v_isSharedCheck_2685_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2666_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2685_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
if (lean_obj_tag(v_a_2667_) == 0)
{
lean_object* v___x_2671_; lean_object* v___x_2673_; 
v___x_2671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2671_, 0, v_a_2667_);
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 0, v___x_2671_);
v___x_2673_ = v___x_2662_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2671_);
lean_ctor_set(v_reuseFailAlloc_2677_, 1, v_snd_2660_);
v___x_2673_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
lean_object* v___x_2675_; 
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 0, v___x_2673_);
v___x_2675_ = v___x_2669_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v___x_2673_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
else
{
lean_object* v_a_2678_; lean_object* v___x_2680_; 
lean_del_object(v___x_2669_);
lean_dec(v_snd_2660_);
v_a_2678_ = lean_ctor_get(v_a_2667_, 0);
lean_inc(v_a_2678_);
lean_dec_ref_known(v_a_2667_, 1);
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 1, v_a_2678_);
lean_ctor_set(v___x_2662_, 0, v___x_2664_);
v___x_2680_ = v___x_2662_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2664_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v_a_2678_);
v___x_2680_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
size_t v___x_2681_; size_t v___x_2682_; 
v___x_2681_ = ((size_t)1ULL);
v___x_2682_ = lean_usize_add(v_i_2655_, v___x_2681_);
v_i_2655_ = v___x_2682_;
v_b_2656_ = v___x_2680_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
lean_del_object(v___x_2662_);
lean_dec(v_snd_2660_);
v_a_2686_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2688_ = v___x_2666_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2666_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2686_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13___boxed(lean_object* v_init_2696_, lean_object* v_as_2697_, lean_object* v_sz_2698_, lean_object* v_i_2699_, lean_object* v_b_2700_, lean_object* v___y_2701_){
_start:
{
size_t v_sz_boxed_2702_; size_t v_i_boxed_2703_; lean_object* v_res_2704_; 
v_sz_boxed_2702_ = lean_unbox_usize(v_sz_2698_);
lean_dec(v_sz_2698_);
v_i_boxed_2703_ = lean_unbox_usize(v_i_2699_);
lean_dec(v_i_2699_);
v_res_2704_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_init_2696_, v_as_2697_, v_sz_boxed_2702_, v_i_boxed_2703_, v_b_2700_);
lean_dec_ref(v_as_2697_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10___boxed(lean_object* v_init_2705_, lean_object* v_n_2706_, lean_object* v_b_2707_, lean_object* v___y_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2705_, v_n_2706_, v_b_2707_);
lean_dec_ref(v_n_2706_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(lean_object* v_as_2710_, size_t v_sz_2711_, size_t v_i_2712_, lean_object* v_b_2713_){
_start:
{
uint8_t v___x_2715_; 
v___x_2715_ = lean_usize_dec_lt(v_i_2712_, v_sz_2711_);
if (v___x_2715_ == 0)
{
lean_object* v___x_2716_; 
v___x_2716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2716_, 0, v_b_2713_);
return v___x_2716_;
}
else
{
uint8_t v___x_2717_; lean_object* v_a_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
lean_dec_ref(v_b_2713_);
v___x_2717_ = 0;
v_a_2718_ = lean_array_uget_borrowed(v_as_2710_, v_i_2712_);
lean_inc(v_a_2718_);
v___x_2719_ = l_Lean_Message_toString(v_a_2718_, v___x_2717_);
v___x_2720_ = l_IO_eprintln___at___00main_spec__6(v___x_2719_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_object* v___x_2721_; size_t v___x_2722_; size_t v___x_2723_; 
lean_dec_ref_known(v___x_2720_, 1);
v___x_2721_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_2722_ = ((size_t)1ULL);
v___x_2723_ = lean_usize_add(v_i_2712_, v___x_2722_);
v_i_2712_ = v___x_2723_;
v_b_2713_ = v___x_2721_;
goto _start;
}
else
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
v_a_2725_ = lean_ctor_get(v___x_2720_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2727_ = v___x_2720_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2720_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2725_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16___boxed(lean_object* v_as_2733_, lean_object* v_sz_2734_, lean_object* v_i_2735_, lean_object* v_b_2736_, lean_object* v___y_2737_){
_start:
{
size_t v_sz_boxed_2738_; size_t v_i_boxed_2739_; lean_object* v_res_2740_; 
v_sz_boxed_2738_ = lean_unbox_usize(v_sz_2734_);
lean_dec(v_sz_2734_);
v_i_boxed_2739_ = lean_unbox_usize(v_i_2735_);
lean_dec(v_i_2735_);
v_res_2740_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(v_as_2733_, v_sz_boxed_2738_, v_i_boxed_2739_, v_b_2736_);
lean_dec_ref(v_as_2733_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(lean_object* v_as_2741_, size_t v_sz_2742_, size_t v_i_2743_, lean_object* v_b_2744_){
_start:
{
uint8_t v___x_2746_; 
v___x_2746_ = lean_usize_dec_lt(v_i_2743_, v_sz_2742_);
if (v___x_2746_ == 0)
{
lean_object* v___x_2747_; 
v___x_2747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2747_, 0, v_b_2744_);
return v___x_2747_;
}
else
{
uint8_t v___x_2748_; lean_object* v_a_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
lean_dec_ref(v_b_2744_);
v___x_2748_ = 0;
v_a_2749_ = lean_array_uget_borrowed(v_as_2741_, v_i_2743_);
lean_inc(v_a_2749_);
v___x_2750_ = l_Lean_Message_toString(v_a_2749_, v___x_2748_);
v___x_2751_ = l_IO_eprintln___at___00main_spec__6(v___x_2750_);
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_object* v___x_2752_; size_t v___x_2753_; size_t v___x_2754_; lean_object* v___x_2755_; 
lean_dec_ref_known(v___x_2751_, 1);
v___x_2752_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_2753_ = ((size_t)1ULL);
v___x_2754_ = lean_usize_add(v_i_2743_, v___x_2753_);
v___x_2755_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(v_as_2741_, v_sz_2742_, v___x_2754_, v___x_2752_);
return v___x_2755_;
}
else
{
lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2763_; 
v_a_2756_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2758_ = v___x_2751_;
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2751_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2761_; 
if (v_isShared_2759_ == 0)
{
v___x_2761_ = v___x_2758_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_a_2756_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11___boxed(lean_object* v_as_2764_, lean_object* v_sz_2765_, lean_object* v_i_2766_, lean_object* v_b_2767_, lean_object* v___y_2768_){
_start:
{
size_t v_sz_boxed_2769_; size_t v_i_boxed_2770_; lean_object* v_res_2771_; 
v_sz_boxed_2769_ = lean_unbox_usize(v_sz_2765_);
lean_dec(v_sz_2765_);
v_i_boxed_2770_ = lean_unbox_usize(v_i_2766_);
lean_dec(v_i_2766_);
v_res_2771_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_as_2764_, v_sz_boxed_2769_, v_i_boxed_2770_, v_b_2767_);
lean_dec_ref(v_as_2764_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7(lean_object* v_t_2772_, lean_object* v_init_2773_){
_start:
{
lean_object* v_root_2775_; lean_object* v_tail_2776_; lean_object* v___x_2777_; 
v_root_2775_ = lean_ctor_get(v_t_2772_, 0);
v_tail_2776_ = lean_ctor_get(v_t_2772_, 1);
v___x_2777_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2773_, v_root_2775_, v_init_2773_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2814_; 
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2780_ = v___x_2777_;
v_isShared_2781_ = v_isSharedCheck_2814_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v___x_2777_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2814_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
if (lean_obj_tag(v_a_2778_) == 0)
{
lean_object* v_a_2782_; lean_object* v___x_2784_; 
v_a_2782_ = lean_ctor_get(v_a_2778_, 0);
lean_inc(v_a_2782_);
lean_dec_ref_known(v_a_2778_, 1);
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 0, v_a_2782_);
v___x_2784_ = v___x_2780_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2782_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
else
{
lean_object* v_a_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; size_t v_sz_2789_; size_t v___x_2790_; lean_object* v___x_2791_; 
lean_del_object(v___x_2780_);
v_a_2786_ = lean_ctor_get(v_a_2778_, 0);
lean_inc(v_a_2786_);
lean_dec_ref_known(v_a_2778_, 1);
v___x_2787_ = lean_box(0);
v___x_2788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2788_, 0, v___x_2787_);
lean_ctor_set(v___x_2788_, 1, v_a_2786_);
v_sz_2789_ = lean_array_size(v_tail_2776_);
v___x_2790_ = ((size_t)0ULL);
v___x_2791_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_tail_2776_, v_sz_2789_, v___x_2790_, v___x_2788_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2805_; 
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2794_ = v___x_2791_;
v_isShared_2795_ = v_isSharedCheck_2805_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2791_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2805_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v_fst_2796_; 
v_fst_2796_ = lean_ctor_get(v_a_2792_, 0);
if (lean_obj_tag(v_fst_2796_) == 0)
{
lean_object* v_snd_2797_; lean_object* v___x_2799_; 
v_snd_2797_ = lean_ctor_get(v_a_2792_, 1);
lean_inc(v_snd_2797_);
lean_dec(v_a_2792_);
if (v_isShared_2795_ == 0)
{
lean_ctor_set(v___x_2794_, 0, v_snd_2797_);
v___x_2799_ = v___x_2794_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_snd_2797_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
else
{
lean_object* v_val_2801_; lean_object* v___x_2803_; 
lean_inc_ref(v_fst_2796_);
lean_dec(v_a_2792_);
v_val_2801_ = lean_ctor_get(v_fst_2796_, 0);
lean_inc(v_val_2801_);
lean_dec_ref_known(v_fst_2796_, 1);
if (v_isShared_2795_ == 0)
{
lean_ctor_set(v___x_2794_, 0, v_val_2801_);
v___x_2803_ = v___x_2794_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_val_2801_);
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
else
{
lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2813_; 
v_a_2806_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2808_ = v___x_2791_;
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v___x_2791_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2811_; 
if (v_isShared_2809_ == 0)
{
v___x_2811_ = v___x_2808_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_a_2806_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
}
}
}
}
else
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2822_; 
v_a_2815_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2817_ = v___x_2777_;
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2777_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2822_;
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
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2815_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7___boxed(lean_object* v_t_2823_, lean_object* v_init_2824_, lean_object* v___y_2825_){
_start:
{
lean_object* v_res_2826_; 
v_res_2826_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_t_2823_, v_init_2824_);
lean_dec_ref(v_t_2823_);
return v_res_2826_;
}
}
static lean_object* _init_l_main___closed__1(void){
_start:
{
lean_object* v___x_2828_; 
v___x_2828_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg();
return v___x_2828_;
}
}
static lean_object* _init_l_main___closed__2(void){
_start:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2829_ = l_Lean_instInhabitedClassState_default;
v___x_2830_ = lean_box(0);
v___x_2831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2830_);
lean_ctor_set(v___x_2831_, 1, v___x_2829_);
return v___x_2831_;
}
}
static lean_object* _init_l_main___closed__3(void){
_start:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2832_ = l_Lean_Meta_Match_Extension_instInhabitedState;
v___x_2833_ = lean_box(0);
v___x_2834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2834_, 0, v___x_2833_);
lean_ctor_set(v___x_2834_, 1, v___x_2832_);
return v___x_2834_;
}
}
static lean_object* _init_l_main___closed__4(void){
_start:
{
lean_object* v___x_2835_; 
v___x_2835_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v___x_2835_;
}
}
static lean_object* _init_l_main___closed__5(void){
_start:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2836_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_2837_ = lean_box(0);
v___x_2838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2837_);
lean_ctor_set(v___x_2838_, 1, v___x_2836_);
return v___x_2838_;
}
}
static lean_object* _init_l_main___closed__6(void){
_start:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2839_ = lean_obj_once(&l_main___closed__5, &l_main___closed__5_once, _init_l_main___closed__5);
v___x_2840_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2839_);
return v___x_2840_;
}
}
static lean_object* _init_l_main___closed__7(void){
_start:
{
lean_object* v___x_2841_; 
v___x_2841_ = l_Array_instInhabited___redArg();
return v___x_2841_;
}
}
static lean_object* _init_l_main___closed__13(void){
_start:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; 
v___x_2850_ = l_Lean_Options_empty;
v___x_2851_ = l_Lean_Core_getMaxHeartbeats(v___x_2850_);
return v___x_2851_;
}
}
static lean_object* _init_l_main___closed__18(void){
_start:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2856_ = ((lean_object*)(l_main___closed__17));
v___x_2857_ = lean_unsigned_to_nat(27u);
v___x_2858_ = lean_unsigned_to_nat(149u);
v___x_2859_ = ((lean_object*)(l_main___closed__16));
v___x_2860_ = ((lean_object*)(l_main___closed__15));
v___x_2861_ = l_mkPanicMessageWithDecl(v___x_2860_, v___x_2859_, v___x_2858_, v___x_2857_, v___x_2856_);
return v___x_2861_;
}
}
static lean_object* _init_l_main___closed__20(void){
_start:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2863_ = ((lean_object*)(l_main___closed__17));
v___x_2864_ = lean_unsigned_to_nat(51u);
v___x_2865_ = lean_unsigned_to_nat(122u);
v___x_2866_ = ((lean_object*)(l_main___closed__16));
v___x_2867_ = ((lean_object*)(l_main___closed__15));
v___x_2868_ = l_mkPanicMessageWithDecl(v___x_2867_, v___x_2866_, v___x_2865_, v___x_2864_, v___x_2863_);
return v___x_2868_;
}
}
static lean_object* _init_l_main___closed__21(void){
_start:
{
lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; 
v___x_2869_ = lean_unsigned_to_nat(1u);
v___x_2870_ = l_Lean_firstFrontendMacroScope;
v___x_2871_ = lean_nat_add(v___x_2870_, v___x_2869_);
return v___x_2871_;
}
}
static lean_object* _init_l_main___closed__25(void){
_start:
{
lean_object* v___x_2878_; uint64_t v___x_2879_; lean_object* v___x_2880_; 
v___x_2878_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2879_ = 0ULL;
v___x_2880_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2880_, 0, v___x_2878_);
lean_ctor_set_uint64(v___x_2880_, sizeof(void*)*1, v___x_2879_);
return v___x_2880_;
}
}
static lean_object* _init_l_main___closed__26(void){
_start:
{
lean_object* v___x_2881_; 
v___x_2881_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2881_;
}
}
static lean_object* _init_l_main___closed__27(void){
_start:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2882_ = lean_obj_once(&l_main___closed__26, &l_main___closed__26_once, _init_l_main___closed__26);
v___x_2883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2883_, 0, v___x_2882_);
return v___x_2883_;
}
}
static lean_object* _init_l_main___closed__28(void){
_start:
{
lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2884_ = lean_obj_once(&l_main___closed__27, &l_main___closed__27_once, _init_l_main___closed__27);
v___x_2885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2884_);
lean_ctor_set(v___x_2885_, 1, v___x_2884_);
return v___x_2885_;
}
}
static lean_object* _init_l_main___closed__29(void){
_start:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; 
v___x_2886_ = l_Lean_NameSet_empty;
v___x_2887_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2888_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2887_);
lean_ctor_set(v___x_2888_, 1, v___x_2887_);
lean_ctor_set(v___x_2888_, 2, v___x_2886_);
return v___x_2888_;
}
}
static lean_object* _init_l_main___closed__30(void){
_start:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; uint8_t v___x_2891_; lean_object* v___x_2892_; 
v___x_2889_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2890_ = lean_obj_once(&l_main___closed__27, &l_main___closed__27_once, _init_l_main___closed__27);
v___x_2891_ = 1;
v___x_2892_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2892_, 0, v___x_2890_);
lean_ctor_set(v___x_2892_, 1, v___x_2890_);
lean_ctor_set(v___x_2892_, 2, v___x_2889_);
lean_ctor_set_uint8(v___x_2892_, sizeof(void*)*3, v___x_2891_);
return v___x_2892_;
}
}
static uint8_t _init_l_main___closed__35(void){
_start:
{
uint8_t v___x_2899_; uint8_t v___x_2900_; uint8_t v___x_2901_; 
v___x_2899_ = 2;
v___x_2900_ = 0;
v___x_2901_ = l_Lean_instOrdOLeanLevel_ord(v___x_2900_, v___x_2899_);
return v___x_2901_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_2902_; lean_object* v___x_2903_; 
v___x_2902_ = 1;
v___x_2903_ = lean_box_uint32(v___x_2902_);
return v___x_2903_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_2904_; lean_object* v___x_2905_; 
v___x_2904_ = 0;
v___x_2905_ = lean_box_uint32(v___x_2904_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_2906_){
_start:
{
if (lean_obj_tag(v_args_2906_) == 1)
{
lean_object* v_tail_2931_; 
v_tail_2931_ = lean_ctor_get(v_args_2906_, 1);
lean_inc(v_tail_2931_);
if (lean_obj_tag(v_tail_2931_) == 1)
{
lean_object* v_tail_2932_; 
v_tail_2932_ = lean_ctor_get(v_tail_2931_, 1);
lean_inc(v_tail_2932_);
if (lean_obj_tag(v_tail_2932_) == 1)
{
lean_object* v_head_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_3581_; 
v_head_2933_ = lean_ctor_get(v_args_2906_, 0);
v_isSharedCheck_3581_ = !lean_is_exclusive(v_args_2906_);
if (v_isSharedCheck_3581_ == 0)
{
lean_object* v_unused_3582_; 
v_unused_3582_ = lean_ctor_get(v_args_2906_, 1);
lean_dec(v_unused_3582_);
v___x_2935_ = v_args_2906_;
v_isShared_2936_ = v_isSharedCheck_3581_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_head_2933_);
lean_dec(v_args_2906_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_3581_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v_head_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_3579_; 
v_head_2937_ = lean_ctor_get(v_tail_2931_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v_tail_2931_);
if (v_isSharedCheck_3579_ == 0)
{
lean_object* v_unused_3580_; 
v_unused_3580_ = lean_ctor_get(v_tail_2931_, 1);
lean_dec(v_unused_3580_);
v___x_2939_ = v_tail_2931_;
v_isShared_2940_ = v_isSharedCheck_3579_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_head_2937_);
lean_dec(v_tail_2931_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_3579_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v_head_2941_; lean_object* v_tail_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_3578_; 
v_head_2941_ = lean_ctor_get(v_tail_2932_, 0);
v_tail_2942_ = lean_ctor_get(v_tail_2932_, 1);
v_isSharedCheck_3578_ = !lean_is_exclusive(v_tail_2932_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_2944_ = v_tail_2932_;
v_isShared_2945_ = v_isSharedCheck_3578_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_tail_2942_);
lean_inc(v_head_2941_);
lean_dec(v_tail_2932_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_3578_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2946_ = lean_obj_once(&l_main___closed__1, &l_main___closed__1_once, _init_l_main___closed__1);
v___x_2947_ = lean_box(0);
v___x_2948_ = lean_obj_once(&l_main___closed__2, &l_main___closed__2_once, _init_l_main___closed__2);
v___x_2949_ = lean_obj_once(&l_main___closed__3, &l_main___closed__3_once, _init_l_main___closed__3);
v___x_2950_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_2951_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_2952_ = lean_obj_once(&l_main___closed__7, &l_main___closed__7_once, _init_l_main___closed__7);
v___x_2953_ = lean_box(1);
v___x_2954_ = ((lean_object*)(l_main___closed__8));
v___x_2955_ = l_Lean_ModuleSetup_load(v_head_2933_);
lean_dec(v_head_2933_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_a_2956_; lean_object* v_name_2957_; lean_object* v_importArts_2958_; lean_object* v_options_2959_; uint8_t v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2964_; 
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
lean_inc(v_a_2956_);
lean_dec_ref_known(v___x_2955_, 1);
v_name_2957_ = lean_ctor_get(v_a_2956_, 0);
lean_inc(v_name_2957_);
v_importArts_2958_ = lean_ctor_get(v_a_2956_, 3);
lean_inc(v_importArts_2958_);
v_options_2959_ = lean_ctor_get(v_a_2956_, 6);
lean_inc(v_options_2959_);
lean_dec(v_a_2956_);
v___x_2960_ = 0;
v___x_2961_ = l_Lean_LeanOptions_toOptions(v_options_2959_);
v___x_2962_ = lean_box(v___x_2960_);
if (v_isShared_2945_ == 0)
{
lean_ctor_set_tag(v___x_2944_, 0);
lean_ctor_set(v___x_2944_, 1, v___x_2961_);
lean_ctor_set(v___x_2944_, 0, v___x_2962_);
v___x_2964_ = v___x_2944_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v___x_2962_);
lean_ctor_set(v_reuseFailAlloc_3569_, 1, v___x_2961_);
v___x_2964_ = v_reuseFailAlloc_3569_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
lean_object* v___x_2965_; 
v___x_2965_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_tail_2942_, v___x_2964_);
lean_dec(v_tail_2942_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v_a_2966_; lean_object* v_fst_2967_; lean_object* v_snd_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_3560_; 
v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
lean_inc(v_a_2966_);
lean_dec_ref_known(v___x_2965_, 1);
v_fst_2967_ = lean_ctor_get(v_a_2966_, 0);
v_snd_2968_ = lean_ctor_get(v_a_2966_, 1);
v_isSharedCheck_3560_ = !lean_is_exclusive(v_a_2966_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_2970_ = v_a_2966_;
v_isShared_2971_ = v_isSharedCheck_3560_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_snd_2968_);
lean_inc(v_fst_2967_);
lean_dec(v_a_2966_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_3560_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2972_; uint8_t v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; uint8_t v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; uint8_t v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v_nextMacroScope_3139_; lean_object* v_ngen_3140_; lean_object* v_auxDeclNGen_3141_; lean_object* v_traceState_3142_; lean_object* v_messages_3143_; lean_object* v_infoState_3144_; lean_object* v_snapshotTasks_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; uint8_t v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; uint8_t v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; uint8_t v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; uint8_t v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; uint8_t v___y_3272_; lean_object* v___x_3292_; 
v___x_2972_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_2973_ = 1;
v___x_2974_ = l_Lean_Option_set___at___00Lean_Environment_realizeConst_spec__0(v_snd_2968_, v___x_2972_, v___x_2973_);
v___x_2975_ = l_Lean_maxHeartbeats;
v___x_2976_ = lean_unsigned_to_nat(0u);
v___x_2977_ = l_Lean_Option_set___at___00main_spec__3(v___x_2974_, v___x_2975_, v___x_2976_);
v___x_3292_ = lean_init_search_path();
if (lean_obj_tag(v___x_3292_) == 0)
{
lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; uint8_t v___x_3298_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3427_; lean_object* v___y_3428_; lean_object* v___y_3429_; lean_object* v___y_3430_; lean_object* v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; uint8_t v___x_3455_; uint8_t v___y_3457_; uint8_t v___x_3551_; 
lean_dec_ref_known(v___x_3292_, 1);
v___x_3293_ = ((lean_object*)(l_main___closed__19));
lean_inc(v_name_2957_);
v___x_3294_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_3294_, 0, v_name_2957_);
lean_ctor_set_uint8(v___x_3294_, sizeof(void*)*1, v___x_2973_);
lean_ctor_set_uint8(v___x_3294_, sizeof(void*)*1 + 1, v___x_2973_);
lean_ctor_set_uint8(v___x_3294_, sizeof(void*)*1 + 2, v___x_2960_);
v___x_3295_ = lean_unsigned_to_nat(1u);
v___x_3296_ = lean_mk_empty_array_with_capacity(v___x_3295_);
v___x_3297_ = lean_array_push(v___x_3296_, v___x_3294_);
v___x_3298_ = 0;
v___x_3455_ = 2;
v___x_3551_ = lean_uint8_once(&l_main___closed__35, &l_main___closed__35_once, _init_l_main___closed__35);
if (v___x_3551_ == 0)
{
v___y_3457_ = v___x_2973_;
goto v___jp_3456_;
}
else
{
v___y_3457_ = v___x_2960_;
goto v___jp_3456_;
}
v___jp_3299_:
{
lean_object* v___x_3308_; 
if (v_isShared_2936_ == 0)
{
lean_ctor_set_tag(v___x_2935_, 0);
lean_ctor_set(v___x_2935_, 1, v___y_3306_);
lean_ctor_set(v___x_2935_, 0, v___y_3305_);
v___x_3308_ = v___x_2935_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v___y_3305_);
lean_ctor_set(v_reuseFailAlloc_3404_, 1, v___y_3306_);
v___x_3308_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v_moduleData_3312_; lean_object* v___x_3313_; uint8_t v___x_3314_; 
v___x_3309_ = lean_box(0);
lean_inc_ref(v___y_3301_);
v___x_3310_ = l_Lean_EnvExtension_setState___redArg(v___y_3301_, v___y_3304_, v___x_3308_, v___x_3309_);
v___x_3311_ = l_Lean_Environment_header(v___x_3310_);
v_moduleData_3312_ = lean_ctor_get(v___x_3311_, 6);
lean_inc_ref(v_moduleData_3312_);
lean_dec_ref(v___x_3311_);
v___x_3313_ = lean_array_get_size(v_moduleData_3312_);
v___x_3314_ = lean_nat_dec_lt(v___y_3303_, v___x_3313_);
if (v___x_3314_ == 0)
{
lean_object* v___x_3315_; lean_object* v___x_3316_; 
lean_dec_ref(v_moduleData_3312_);
lean_dec_ref(v___x_3310_);
lean_dec(v___y_3303_);
lean_dec(v___y_3302_);
lean_dec(v___y_3300_);
lean_dec_ref(v___x_2977_);
lean_del_object(v___x_2970_);
lean_dec(v_fst_2967_);
lean_dec(v_name_2957_);
lean_dec(v_head_2941_);
lean_del_object(v___x_2939_);
lean_dec(v_head_2937_);
v___x_3315_ = lean_obj_once(&l_main___closed__20, &l_main___closed__20_once, _init_l_main___closed__20);
v___x_3316_ = l_panic___at___00main_spec__5(v___x_3315_);
return v___x_3316_;
}
else
{
lean_object* v_base_3317_; lean_object* v_private_3318_; lean_object* v_header_3319_; lean_object* v_serverBaseExts_3320_; lean_object* v_checked_3321_; lean_object* v_asyncConstsMap_3322_; lean_object* v_asyncCtx_x3f_3323_; lean_object* v_importRealizationCtx_x3f_3324_; lean_object* v_localRealizationCtxMap_3325_; lean_object* v_allRealizations_3326_; uint8_t v_isExporting_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3402_; 
v_base_3317_ = lean_ctor_get(v___x_3310_, 0);
lean_inc_ref(v_base_3317_);
v_private_3318_ = lean_ctor_get(v_base_3317_, 0);
lean_inc(v_private_3318_);
v_header_3319_ = lean_ctor_get(v_private_3318_, 5);
lean_inc_ref(v_header_3319_);
v_serverBaseExts_3320_ = lean_ctor_get(v___x_3310_, 1);
v_checked_3321_ = lean_ctor_get(v___x_3310_, 2);
v_asyncConstsMap_3322_ = lean_ctor_get(v___x_3310_, 3);
v_asyncCtx_x3f_3323_ = lean_ctor_get(v___x_3310_, 4);
v_importRealizationCtx_x3f_3324_ = lean_ctor_get(v___x_3310_, 5);
v_localRealizationCtxMap_3325_ = lean_ctor_get(v___x_3310_, 6);
v_allRealizations_3326_ = lean_ctor_get(v___x_3310_, 7);
v_isExporting_3327_ = lean_ctor_get_uint8(v___x_3310_, sizeof(void*)*8);
v_isSharedCheck_3402_ = !lean_is_exclusive(v___x_3310_);
if (v_isSharedCheck_3402_ == 0)
{
lean_object* v_unused_3403_; 
v_unused_3403_ = lean_ctor_get(v___x_3310_, 0);
lean_dec(v_unused_3403_);
v___x_3329_ = v___x_3310_;
v_isShared_3330_ = v_isSharedCheck_3402_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_allRealizations_3326_);
lean_inc(v_localRealizationCtxMap_3325_);
lean_inc(v_importRealizationCtx_x3f_3324_);
lean_inc(v_asyncCtx_x3f_3323_);
lean_inc(v_asyncConstsMap_3322_);
lean_inc(v_checked_3321_);
lean_inc(v_serverBaseExts_3320_);
lean_dec(v___x_3310_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3402_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v_public_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3400_; 
v_public_3331_ = lean_ctor_get(v_base_3317_, 1);
v_isSharedCheck_3400_ = !lean_is_exclusive(v_base_3317_);
if (v_isSharedCheck_3400_ == 0)
{
lean_object* v_unused_3401_; 
v_unused_3401_ = lean_ctor_get(v_base_3317_, 0);
lean_dec(v_unused_3401_);
v___x_3333_ = v_base_3317_;
v_isShared_3334_ = v_isSharedCheck_3400_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_public_3331_);
lean_dec(v_base_3317_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3400_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v_constants_3335_; uint8_t v_quotInit_3336_; lean_object* v_diagnostics_3337_; lean_object* v_const2ModIdx_3338_; lean_object* v_extensions_3339_; lean_object* v_irBaseExts_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3398_; 
v_constants_3335_ = lean_ctor_get(v_private_3318_, 0);
v_quotInit_3336_ = lean_ctor_get_uint8(v_private_3318_, sizeof(void*)*6);
v_diagnostics_3337_ = lean_ctor_get(v_private_3318_, 1);
v_const2ModIdx_3338_ = lean_ctor_get(v_private_3318_, 2);
v_extensions_3339_ = lean_ctor_get(v_private_3318_, 3);
v_irBaseExts_3340_ = lean_ctor_get(v_private_3318_, 4);
v_isSharedCheck_3398_ = !lean_is_exclusive(v_private_3318_);
if (v_isSharedCheck_3398_ == 0)
{
lean_object* v_unused_3399_; 
v_unused_3399_ = lean_ctor_get(v_private_3318_, 5);
lean_dec(v_unused_3399_);
v___x_3342_ = v_private_3318_;
v_isShared_3343_ = v_isSharedCheck_3398_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_irBaseExts_3340_);
lean_inc(v_extensions_3339_);
lean_inc(v_const2ModIdx_3338_);
lean_inc(v_diagnostics_3337_);
lean_inc(v_constants_3335_);
lean_dec(v_private_3318_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3398_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
uint32_t v_trustLevel_3344_; lean_object* v_mainModule_3345_; uint8_t v_isModule_3346_; lean_object* v_regions_3347_; lean_object* v_modules_3348_; lean_object* v_moduleName2Idx_3349_; lean_object* v_importAllModules_3350_; lean_object* v_moduleData_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3396_; 
v_trustLevel_3344_ = lean_ctor_get_uint32(v_header_3319_, sizeof(void*)*7);
v_mainModule_3345_ = lean_ctor_get(v_header_3319_, 0);
v_isModule_3346_ = lean_ctor_get_uint8(v_header_3319_, sizeof(void*)*7 + 4);
v_regions_3347_ = lean_ctor_get(v_header_3319_, 2);
v_modules_3348_ = lean_ctor_get(v_header_3319_, 3);
v_moduleName2Idx_3349_ = lean_ctor_get(v_header_3319_, 4);
v_importAllModules_3350_ = lean_ctor_get(v_header_3319_, 5);
v_moduleData_3351_ = lean_ctor_get(v_header_3319_, 6);
v_isSharedCheck_3396_ = !lean_is_exclusive(v_header_3319_);
if (v_isSharedCheck_3396_ == 0)
{
lean_object* v_unused_3397_; 
v_unused_3397_ = lean_ctor_get(v_header_3319_, 1);
lean_dec(v_unused_3397_);
v___x_3353_ = v_header_3319_;
v_isShared_3354_ = v_isSharedCheck_3396_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_moduleData_3351_);
lean_inc(v_importAllModules_3350_);
lean_inc(v_moduleName2Idx_3349_);
lean_inc(v_modules_3348_);
lean_inc(v_regions_3347_);
lean_inc(v_mainModule_3345_);
lean_dec(v_header_3319_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3396_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3355_; lean_object* v_imports_3356_; lean_object* v___x_3358_; 
v___x_3355_ = lean_array_fget(v_moduleData_3312_, v___y_3303_);
lean_dec_ref(v_moduleData_3312_);
v_imports_3356_ = lean_ctor_get(v___x_3355_, 0);
lean_inc_ref(v_imports_3356_);
lean_dec(v___x_3355_);
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 1, v_imports_3356_);
v___x_3358_ = v___x_3353_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 7, 5);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_mainModule_3345_);
lean_ctor_set(v_reuseFailAlloc_3395_, 1, v_imports_3356_);
lean_ctor_set(v_reuseFailAlloc_3395_, 2, v_regions_3347_);
lean_ctor_set(v_reuseFailAlloc_3395_, 3, v_modules_3348_);
lean_ctor_set(v_reuseFailAlloc_3395_, 4, v_moduleName2Idx_3349_);
lean_ctor_set(v_reuseFailAlloc_3395_, 5, v_importAllModules_3350_);
lean_ctor_set(v_reuseFailAlloc_3395_, 6, v_moduleData_3351_);
lean_ctor_set_uint32(v_reuseFailAlloc_3395_, sizeof(void*)*7, v_trustLevel_3344_);
lean_ctor_set_uint8(v_reuseFailAlloc_3395_, sizeof(void*)*7 + 4, v_isModule_3346_);
v___x_3358_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
lean_object* v___x_3360_; 
if (v_isShared_3343_ == 0)
{
lean_ctor_set(v___x_3342_, 5, v___x_3358_);
v___x_3360_ = v___x_3342_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_constants_3335_);
lean_ctor_set(v_reuseFailAlloc_3394_, 1, v_diagnostics_3337_);
lean_ctor_set(v_reuseFailAlloc_3394_, 2, v_const2ModIdx_3338_);
lean_ctor_set(v_reuseFailAlloc_3394_, 3, v_extensions_3339_);
lean_ctor_set(v_reuseFailAlloc_3394_, 4, v_irBaseExts_3340_);
lean_ctor_set(v_reuseFailAlloc_3394_, 5, v___x_3358_);
lean_ctor_set_uint8(v_reuseFailAlloc_3394_, sizeof(void*)*6, v_quotInit_3336_);
v___x_3360_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
lean_object* v___x_3362_; 
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 0, v___x_3360_);
v___x_3362_ = v___x_3333_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v___x_3360_);
lean_ctor_set(v_reuseFailAlloc_3393_, 1, v_public_3331_);
v___x_3362_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
lean_object* v___x_3364_; 
if (v_isShared_3330_ == 0)
{
lean_ctor_set(v___x_3329_, 0, v___x_3362_);
v___x_3364_ = v___x_3329_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3362_);
lean_ctor_set(v_reuseFailAlloc_3392_, 1, v_serverBaseExts_3320_);
lean_ctor_set(v_reuseFailAlloc_3392_, 2, v_checked_3321_);
lean_ctor_set(v_reuseFailAlloc_3392_, 3, v_asyncConstsMap_3322_);
lean_ctor_set(v_reuseFailAlloc_3392_, 4, v_asyncCtx_x3f_3323_);
lean_ctor_set(v_reuseFailAlloc_3392_, 5, v_importRealizationCtx_x3f_3324_);
lean_ctor_set(v_reuseFailAlloc_3392_, 6, v_localRealizationCtxMap_3325_);
lean_ctor_set(v_reuseFailAlloc_3392_, 7, v_allRealizations_3326_);
lean_ctor_set_uint8(v_reuseFailAlloc_3392_, sizeof(void*)*8, v_isExporting_3327_);
v___x_3364_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; uint8_t v___x_3388_; lean_object* v___x_3389_; lean_object* v_env_3390_; uint8_t v___x_3391_; 
v___x_3365_ = l_Lean_Compiler_LCNF_postponedCompileDeclsExt;
v___x_3366_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2954_, v___x_3365_, v___x_3364_, v___y_3303_, v___x_3298_);
lean_dec(v___y_3303_);
v___x_3367_ = l_Lean_instInhabitedFileMap_default;
v___x_3368_ = lean_unsigned_to_nat(1000u);
v___x_3369_ = l_Lean_Core_getMaxHeartbeats(v___x_2977_);
v___x_3370_ = l_Lean_firstFrontendMacroScope;
v___x_3371_ = lean_box(0);
v___x_3372_ = lean_box(0);
v___x_3373_ = lean_obj_once(&l_main___closed__21, &l_main___closed__21_once, _init_l_main___closed__21);
v___x_3374_ = ((lean_object*)(l_main___closed__24));
lean_inc_n(v___y_3302_, 3);
v___x_3375_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3375_, 0, v___y_3302_);
lean_ctor_set(v___x_3375_, 1, v___x_3295_);
lean_ctor_set(v___x_3375_, 2, v___x_2947_);
v___x_3376_ = lean_obj_once(&l_main___closed__25, &l_main___closed__25_once, _init_l_main___closed__25);
v___x_3377_ = lean_obj_once(&l_main___closed__28, &l_main___closed__28_once, _init_l_main___closed__28);
v___x_3378_ = lean_obj_once(&l_main___closed__29, &l_main___closed__29_once, _init_l_main___closed__29);
v___x_3379_ = lean_obj_once(&l_main___closed__30, &l_main___closed__30_once, _init_l_main___closed__30);
v___x_3380_ = ((lean_object*)(l_main___closed__31));
lean_inc_ref(v___x_3375_);
v___x_3381_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3364_);
lean_ctor_set(v___x_3381_, 1, v___x_3373_);
lean_ctor_set(v___x_3381_, 2, v___x_3374_);
lean_ctor_set(v___x_3381_, 3, v___x_3375_);
lean_ctor_set(v___x_3381_, 4, v___x_3376_);
lean_ctor_set(v___x_3381_, 5, v___x_3377_);
lean_ctor_set(v___x_3381_, 6, v___x_3378_);
lean_ctor_set(v___x_3381_, 7, v___x_3379_);
lean_ctor_set(v___x_3381_, 8, v___x_3380_);
v___x_3382_ = lean_st_mk_ref(v___x_3381_);
v___x_3383_ = l_Lean_inheritedTraceOptions;
v___x_3384_ = lean_st_ref_get(v___x_3383_);
lean_inc_ref(v___x_2977_);
lean_inc(v_head_2937_);
v___x_3385_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3385_, 0, v_head_2937_);
lean_ctor_set(v___x_3385_, 1, v___x_3367_);
lean_ctor_set(v___x_3385_, 2, v___x_2977_);
lean_ctor_set(v___x_3385_, 3, v___x_3368_);
lean_ctor_set(v___x_3385_, 4, v___y_3302_);
lean_ctor_set(v___x_3385_, 5, v___x_2947_);
lean_ctor_set(v___x_3385_, 6, v___x_2976_);
lean_ctor_set(v___x_3385_, 7, v___x_3369_);
lean_ctor_set(v___x_3385_, 8, v___y_3302_);
lean_ctor_set(v___x_3385_, 9, v___x_3370_);
lean_ctor_set(v___x_3385_, 10, v___x_3371_);
lean_ctor_set(v___x_3385_, 11, v___x_3384_);
v___x_3386_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3386_, 0, v___x_3385_);
lean_ctor_set(v___x_3386_, 1, v___x_2976_);
lean_ctor_set(v___x_3386_, 2, v___x_3372_);
lean_ctor_set_uint8(v___x_3386_, sizeof(void*)*3, v___x_2960_);
lean_ctor_set_uint8(v___x_3386_, sizeof(void*)*3 + 1, v___x_2960_);
v___x_3387_ = l_Lean_diagnostics;
v___x_3388_ = l_Lean_Option_get___at___00main_spec__8(v___x_2977_, v___x_3387_);
v___x_3389_ = lean_st_ref_get(v___x_3382_);
v_env_3390_ = lean_ctor_get(v___x_3389_, 0);
lean_inc_ref(v_env_3390_);
lean_dec(v___x_3389_);
v___x_3391_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3390_);
lean_dec_ref(v_env_3390_);
if (v___x_3388_ == 0)
{
if (v___x_3391_ == 0)
{
v___y_3251_ = v___x_2947_;
v___y_3252_ = v___y_3300_;
v___y_3253_ = v___x_3375_;
v___y_3254_ = v___x_3365_;
v___y_3255_ = v___x_3373_;
v___y_3256_ = v___x_3376_;
v___y_3257_ = v___x_3314_;
v___y_3258_ = v___x_3372_;
v___y_3259_ = v___x_3374_;
v___y_3260_ = v___x_3370_;
v___y_3261_ = v___x_3371_;
v___y_3262_ = v___x_3366_;
v___y_3263_ = v___x_3367_;
v___y_3264_ = v___x_3377_;
v___y_3265_ = v___x_3379_;
v___y_3266_ = v___y_3302_;
v___y_3267_ = v___x_3386_;
v___y_3268_ = v___x_3388_;
v___y_3269_ = v___x_3382_;
v___y_3270_ = v___x_3378_;
v___y_3271_ = v___x_3380_;
v___y_3272_ = v___x_3314_;
goto v___jp_3250_;
}
else
{
v___y_3251_ = v___x_2947_;
v___y_3252_ = v___y_3300_;
v___y_3253_ = v___x_3375_;
v___y_3254_ = v___x_3365_;
v___y_3255_ = v___x_3373_;
v___y_3256_ = v___x_3376_;
v___y_3257_ = v___x_3314_;
v___y_3258_ = v___x_3372_;
v___y_3259_ = v___x_3374_;
v___y_3260_ = v___x_3370_;
v___y_3261_ = v___x_3371_;
v___y_3262_ = v___x_3366_;
v___y_3263_ = v___x_3367_;
v___y_3264_ = v___x_3377_;
v___y_3265_ = v___x_3379_;
v___y_3266_ = v___y_3302_;
v___y_3267_ = v___x_3386_;
v___y_3268_ = v___x_3388_;
v___y_3269_ = v___x_3382_;
v___y_3270_ = v___x_3378_;
v___y_3271_ = v___x_3380_;
v___y_3272_ = v___x_3388_;
goto v___jp_3250_;
}
}
else
{
v___y_3251_ = v___x_2947_;
v___y_3252_ = v___y_3300_;
v___y_3253_ = v___x_3375_;
v___y_3254_ = v___x_3365_;
v___y_3255_ = v___x_3373_;
v___y_3256_ = v___x_3376_;
v___y_3257_ = v___x_3314_;
v___y_3258_ = v___x_3372_;
v___y_3259_ = v___x_3374_;
v___y_3260_ = v___x_3370_;
v___y_3261_ = v___x_3371_;
v___y_3262_ = v___x_3366_;
v___y_3263_ = v___x_3367_;
v___y_3264_ = v___x_3377_;
v___y_3265_ = v___x_3379_;
v___y_3266_ = v___y_3302_;
v___y_3267_ = v___x_3386_;
v___y_3268_ = v___x_3388_;
v___y_3269_ = v___x_3382_;
v___y_3270_ = v___x_3378_;
v___y_3271_ = v___x_3380_;
v___y_3272_ = v___x_3391_;
goto v___jp_3250_;
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
v___jp_3405_:
{
lean_object* v___x_3410_; lean_object* v_toEnvExtension_3411_; lean_object* v_asyncMode_3412_; lean_object* v___x_3413_; lean_object* v_importedEntries_3414_; lean_object* v_state_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; uint8_t v___x_3418_; 
v___x_3410_ = l_Lean_IR_declMapExt;
v_toEnvExtension_3411_ = lean_ctor_get(v___x_3410_, 0);
v_asyncMode_3412_ = lean_ctor_get(v_toEnvExtension_3411_, 2);
lean_inc(v___y_3407_);
lean_inc_ref(v___y_3409_);
v___x_3413_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2951_, v_toEnvExtension_3411_, v___y_3409_, v_asyncMode_3412_, v___y_3407_);
v_importedEntries_3414_ = lean_ctor_get(v___x_3413_, 0);
lean_inc_ref(v_importedEntries_3414_);
v_state_3415_ = lean_ctor_get(v___x_3413_, 1);
lean_inc(v_state_3415_);
lean_dec(v___x_3413_);
v___x_3416_ = lean_array_get_borrowed(v___x_2952_, v_importedEntries_3414_, v___y_3408_);
v___x_3417_ = lean_array_get_size(v___x_3416_);
v___x_3418_ = lean_nat_dec_lt(v___x_2976_, v___x_3417_);
if (v___x_3418_ == 0)
{
v___y_3300_ = v___y_3406_;
v___y_3301_ = v_toEnvExtension_3411_;
v___y_3302_ = v___y_3407_;
v___y_3303_ = v___y_3408_;
v___y_3304_ = v___y_3409_;
v___y_3305_ = v_importedEntries_3414_;
v___y_3306_ = v_state_3415_;
goto v___jp_3299_;
}
else
{
uint8_t v___x_3419_; 
v___x_3419_ = lean_nat_dec_le(v___x_3417_, v___x_3417_);
if (v___x_3419_ == 0)
{
if (v___x_3418_ == 0)
{
v___y_3300_ = v___y_3406_;
v___y_3301_ = v_toEnvExtension_3411_;
v___y_3302_ = v___y_3407_;
v___y_3303_ = v___y_3408_;
v___y_3304_ = v___y_3409_;
v___y_3305_ = v_importedEntries_3414_;
v___y_3306_ = v_state_3415_;
goto v___jp_3299_;
}
else
{
size_t v___x_3420_; size_t v___x_3421_; lean_object* v___x_3422_; 
v___x_3420_ = ((size_t)0ULL);
v___x_3421_ = lean_usize_of_nat(v___x_3417_);
lean_inc_ref(v___y_3409_);
v___x_3422_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3409_, v___x_3416_, v___x_3420_, v___x_3421_, v_state_3415_);
v___y_3300_ = v___y_3406_;
v___y_3301_ = v_toEnvExtension_3411_;
v___y_3302_ = v___y_3407_;
v___y_3303_ = v___y_3408_;
v___y_3304_ = v___y_3409_;
v___y_3305_ = v_importedEntries_3414_;
v___y_3306_ = v___x_3422_;
goto v___jp_3299_;
}
}
else
{
size_t v___x_3423_; size_t v___x_3424_; lean_object* v___x_3425_; 
v___x_3423_ = ((size_t)0ULL);
v___x_3424_ = lean_usize_of_nat(v___x_3417_);
lean_inc_ref(v___y_3409_);
v___x_3425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3409_, v___x_3416_, v___x_3423_, v___x_3424_, v_state_3415_);
v___y_3300_ = v___y_3406_;
v___y_3301_ = v_toEnvExtension_3411_;
v___y_3302_ = v___y_3407_;
v___y_3303_ = v___y_3408_;
v___y_3304_ = v___y_3409_;
v___y_3305_ = v_importedEntries_3414_;
v___y_3306_ = v___x_3425_;
goto v___jp_3299_;
}
}
}
v___jp_3426_:
{
uint8_t v___x_3433_; 
v___x_3433_ = lean_nat_dec_lt(v___x_2976_, v___y_3431_);
if (v___x_3433_ == 0)
{
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3428_);
v___y_3406_ = v___y_3427_;
v___y_3407_ = v___y_3429_;
v___y_3408_ = v___y_3430_;
v___y_3409_ = v___y_3432_;
goto v___jp_3405_;
}
else
{
uint8_t v___x_3434_; 
v___x_3434_ = lean_nat_dec_le(v___y_3431_, v___y_3431_);
if (v___x_3434_ == 0)
{
if (v___x_3433_ == 0)
{
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3428_);
v___y_3406_ = v___y_3427_;
v___y_3407_ = v___y_3429_;
v___y_3408_ = v___y_3430_;
v___y_3409_ = v___y_3432_;
goto v___jp_3405_;
}
else
{
size_t v___x_3435_; size_t v___x_3436_; lean_object* v___x_3437_; 
v___x_3435_ = ((size_t)0ULL);
v___x_3436_ = lean_usize_of_nat(v___y_3431_);
lean_dec(v___y_3431_);
v___x_3437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3428_, v___x_3435_, v___x_3436_, v___y_3432_);
lean_dec_ref(v___y_3428_);
v___y_3406_ = v___y_3427_;
v___y_3407_ = v___y_3429_;
v___y_3408_ = v___y_3430_;
v___y_3409_ = v___x_3437_;
goto v___jp_3405_;
}
}
else
{
size_t v___x_3438_; size_t v___x_3439_; lean_object* v___x_3440_; 
v___x_3438_ = ((size_t)0ULL);
v___x_3439_ = lean_usize_of_nat(v___y_3431_);
lean_dec(v___y_3431_);
v___x_3440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3428_, v___x_3438_, v___x_3439_, v___y_3432_);
lean_dec_ref(v___y_3428_);
v___y_3406_ = v___y_3427_;
v___y_3407_ = v___y_3429_;
v___y_3408_ = v___y_3430_;
v___y_3409_ = v___x_3440_;
goto v___jp_3405_;
}
}
}
v___jp_3441_:
{
lean_object* v___x_3446_; uint8_t v___x_3447_; 
v___x_3446_ = lean_array_get_size(v___y_3445_);
v___x_3447_ = lean_nat_dec_lt(v___x_2976_, v___x_3446_);
if (v___x_3447_ == 0)
{
lean_inc(v___y_3442_);
v___y_3427_ = v___y_3442_;
v___y_3428_ = v___y_3445_;
v___y_3429_ = v___y_3442_;
v___y_3430_ = v___y_3444_;
v___y_3431_ = v___x_3446_;
v___y_3432_ = v___y_3443_;
goto v___jp_3426_;
}
else
{
uint8_t v___x_3448_; 
v___x_3448_ = lean_nat_dec_le(v___x_3446_, v___x_3446_);
if (v___x_3448_ == 0)
{
if (v___x_3447_ == 0)
{
lean_inc(v___y_3442_);
v___y_3427_ = v___y_3442_;
v___y_3428_ = v___y_3445_;
v___y_3429_ = v___y_3442_;
v___y_3430_ = v___y_3444_;
v___y_3431_ = v___x_3446_;
v___y_3432_ = v___y_3443_;
goto v___jp_3426_;
}
else
{
size_t v___x_3449_; size_t v___x_3450_; lean_object* v___x_3451_; 
v___x_3449_ = ((size_t)0ULL);
v___x_3450_ = lean_usize_of_nat(v___x_3446_);
v___x_3451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v___y_3445_, v___x_3449_, v___x_3450_, v___y_3443_);
lean_inc(v___y_3442_);
v___y_3427_ = v___y_3442_;
v___y_3428_ = v___y_3445_;
v___y_3429_ = v___y_3442_;
v___y_3430_ = v___y_3444_;
v___y_3431_ = v___x_3446_;
v___y_3432_ = v___x_3451_;
goto v___jp_3426_;
}
}
else
{
size_t v___x_3452_; size_t v___x_3453_; lean_object* v___x_3454_; 
v___x_3452_ = ((size_t)0ULL);
v___x_3453_ = lean_usize_of_nat(v___x_3446_);
v___x_3454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v___y_3445_, v___x_3452_, v___x_3453_, v___y_3443_);
lean_inc(v___y_3442_);
v___y_3427_ = v___y_3442_;
v___y_3428_ = v___y_3445_;
v___y_3429_ = v___y_3442_;
v___y_3430_ = v___y_3444_;
v___y_3431_ = v___x_3446_;
v___y_3432_ = v___x_3454_;
goto v___jp_3426_;
}
}
}
v___jp_3456_:
{
lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___f_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
v___x_3458_ = l_Lean_instInhabitedImportState_default;
v___x_3459_ = lean_box(v___x_3298_);
v___x_3460_ = lean_box(v___y_3457_);
v___x_3461_ = lean_box(v___x_2973_);
v___x_3462_ = lean_box(v___x_3455_);
v___x_3463_ = lean_box(v___x_2960_);
lean_inc_ref(v___x_2977_);
lean_inc(v_name_2957_);
v___f_3464_ = lean_alloc_closure((void*)(l_main___lam__0___boxed), 11, 10);
lean_closure_set(v___f_3464_, 0, v___x_3458_);
lean_closure_set(v___f_3464_, 1, v___x_3297_);
lean_closure_set(v___f_3464_, 2, v___x_3459_);
lean_closure_set(v___f_3464_, 3, v_importArts_2958_);
lean_closure_set(v___f_3464_, 4, v___x_3460_);
lean_closure_set(v___f_3464_, 5, v___x_3461_);
lean_closure_set(v___f_3464_, 6, v_name_2957_);
lean_closure_set(v___f_3464_, 7, v___x_3462_);
lean_closure_set(v___f_3464_, 8, v___x_2977_);
lean_closure_set(v___f_3464_, 9, v___x_3463_);
v___x_3465_ = lean_alloc_closure((void*)(l_Lean_withImporting___boxed), 3, 2);
lean_closure_set(v___x_3465_, 0, lean_box(0));
lean_closure_set(v___x_3465_, 1, v___f_3464_);
v___x_3466_ = lean_box(0);
v___x_3467_ = l_Lean_profileitIOUnsafe___redArg(v___x_3293_, v___x_2977_, v___x_3465_, v___x_3466_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v_a_3468_; lean_object* v___x_3469_; lean_object* v_ext_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; 
v_a_3468_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_a_3468_);
lean_dec_ref_known(v___x_3467_, 1);
v___x_3469_ = l_Lean_Compiler_CSimp_ext;
v_ext_3470_ = lean_ctor_get(v___x_3469_, 1);
lean_inc(v_name_2957_);
v___x_3471_ = l_Lean_Environment_setMainModule(v_a_3468_, v_name_2957_);
lean_inc_ref(v_ext_3470_);
v___x_3472_ = l_main___elam__0___redArg(v___x_3466_, v___x_2946_, v_ext_3470_, v___x_3471_);
if (lean_obj_tag(v___x_3472_) == 0)
{
lean_object* v_a_3473_; lean_object* v___x_3474_; lean_object* v_ext_3475_; lean_object* v___x_3476_; 
v_a_3473_ = lean_ctor_get(v___x_3472_, 0);
lean_inc(v_a_3473_);
lean_dec_ref_known(v___x_3472_, 1);
v___x_3474_ = l_Lean_Meta_instanceExtension;
v_ext_3475_ = lean_ctor_get(v___x_3474_, 1);
lean_inc_ref(v_ext_3475_);
v___x_3476_ = l_main___elam__0___redArg(v___x_3466_, v___x_2946_, v_ext_3475_, v_a_3473_);
if (lean_obj_tag(v___x_3476_) == 0)
{
lean_object* v_a_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; 
v_a_3477_ = lean_ctor_get(v___x_3476_, 0);
lean_inc(v_a_3477_);
lean_dec_ref_known(v___x_3476_, 1);
v___x_3478_ = l_Lean_classExtension;
v___x_3479_ = l_main___elam__0___redArg(v___x_3466_, v___x_2948_, v___x_3478_, v_a_3477_);
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_object* v_a_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; 
v_a_3480_ = lean_ctor_get(v___x_3479_, 0);
lean_inc(v_a_3480_);
lean_dec_ref_known(v___x_3479_, 1);
v___x_3481_ = l_Lean_Meta_Match_Extension_extension;
v___x_3482_ = l_main___elam__0___redArg(v___x_3466_, v___x_2949_, v___x_3481_, v_a_3480_);
if (lean_obj_tag(v___x_3482_) == 0)
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3510_; 
v_a_3483_ = lean_ctor_get(v___x_3482_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3482_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3485_ = v___x_3482_;
v_isShared_3486_ = v_isSharedCheck_3510_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3482_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3510_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3487_; 
v___x_3487_ = l_Lean_Environment_getModuleIdx_x3f(v_a_3483_, v_name_2957_);
if (lean_obj_tag(v___x_3487_) == 1)
{
lean_object* v_val_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; uint8_t v___x_3493_; 
lean_del_object(v___x_3485_);
v_val_3488_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_val_3488_);
lean_dec_ref_known(v___x_3487_, 1);
v___x_3489_ = l_Lean_Compiler_LCNF_impureSigExt;
v___x_3490_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2950_, v___x_3489_, v_a_3483_, v_val_3488_, v___x_3298_);
v___x_3491_ = lean_array_get_size(v___x_3490_);
v___x_3492_ = ((lean_object*)(l_main___closed__32));
v___x_3493_ = lean_nat_dec_lt(v___x_2976_, v___x_3491_);
if (v___x_3493_ == 0)
{
lean_dec_ref(v___x_3490_);
v___y_3442_ = v___x_3466_;
v___y_3443_ = v_a_3483_;
v___y_3444_ = v_val_3488_;
v___y_3445_ = v___x_3492_;
goto v___jp_3441_;
}
else
{
uint8_t v___x_3494_; 
v___x_3494_ = lean_nat_dec_le(v___x_3491_, v___x_3491_);
if (v___x_3494_ == 0)
{
if (v___x_3493_ == 0)
{
lean_dec_ref(v___x_3490_);
v___y_3442_ = v___x_3466_;
v___y_3443_ = v_a_3483_;
v___y_3444_ = v_val_3488_;
v___y_3445_ = v___x_3492_;
goto v___jp_3441_;
}
else
{
size_t v___x_3495_; size_t v___x_3496_; lean_object* v___x_3497_; 
v___x_3495_ = ((size_t)0ULL);
v___x_3496_ = lean_usize_of_nat(v___x_3491_);
lean_inc(v_a_3483_);
v___x_3497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_3483_, v___x_3490_, v___x_3495_, v___x_3496_, v___x_3492_);
lean_dec_ref(v___x_3490_);
v___y_3442_ = v___x_3466_;
v___y_3443_ = v_a_3483_;
v___y_3444_ = v_val_3488_;
v___y_3445_ = v___x_3497_;
goto v___jp_3441_;
}
}
else
{
size_t v___x_3498_; size_t v___x_3499_; lean_object* v___x_3500_; 
v___x_3498_ = ((size_t)0ULL);
v___x_3499_ = lean_usize_of_nat(v___x_3491_);
lean_inc(v_a_3483_);
v___x_3500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_3483_, v___x_3490_, v___x_3498_, v___x_3499_, v___x_3492_);
lean_dec_ref(v___x_3490_);
v___y_3442_ = v___x_3466_;
v___y_3443_ = v_a_3483_;
v___y_3444_ = v_val_3488_;
v___y_3445_ = v___x_3500_;
goto v___jp_3441_;
}
}
}
else
{
lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3508_; 
lean_dec(v___x_3487_);
lean_dec(v_a_3483_);
lean_dec_ref(v___x_2977_);
lean_del_object(v___x_2970_);
lean_dec(v_fst_2967_);
lean_dec(v_head_2941_);
lean_del_object(v___x_2939_);
lean_dec(v_head_2937_);
lean_del_object(v___x_2935_);
v___x_3501_ = ((lean_object*)(l_main___closed__33));
v___x_3502_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2957_, v___x_2973_);
v___x_3503_ = lean_string_append(v___x_3501_, v___x_3502_);
lean_dec_ref(v___x_3502_);
v___x_3504_ = ((lean_object*)(l_main___closed__34));
v___x_3505_ = lean_string_append(v___x_3503_, v___x_3504_);
v___x_3506_ = lean_mk_io_user_error(v___x_3505_);
if (v_isShared_3486_ == 0)
{
lean_ctor_set_tag(v___x_3485_, 1);
lean_ctor_set(v___x_3485_, 0, v___x_3506_);
v___x_3508_ = v___x_3485_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v___x_3506_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
}
}
else
{
lean_object* v_a_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3518_; 
lean_dec_ref(v___x_2977_);
lean_del_object(v___x_2970_);
lean_dec(v_fst_2967_);
lean_dec(v_name_2957_);
lean_dec(v_head_2941_);
lean_del_object(v___x_2939_);
lean_dec(v_head_2937_);
lean_del_object(v___x_2935_);
v_a_3511_ = lean_ctor_get(v___x_3482_, 0);
v_isSharedCheck_3518_ = !lean_is_exclusive(v___x_3482_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3513_ = v___x_3482_;
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_a_3511_);
lean_dec(v___x_3482_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v___x_3516_; 
if (v_isShared_3514_ == 0)
{
v___x_3516_ = v___x_3513_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_a_3511_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
}
else
{
lean_object* v_a_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3526_; 
lean_dec_ref(v___x_2977_);
lean_del_object(v___x_2970_);
lean_dec(v_fst_2967_);
lean_dec(v_name_2957_);
lean_dec(v_head_2941_);
lean_del_object(v___x_2939_);
lean_dec(v_head_2937_);
lean_del_object(v___x_2935_);
v_a_3519_ = lean_ctor_get(v___x_3479_, 0);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3521_ = v___x_3479_;
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_a_3519_);
lean_dec(v___x_3479_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v___x_3524_; 
if (v_isShared_3522_ == 0)
{
v___x_3524_ = v___x_3521_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_a_3519_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
}
}
}
}
else
{
lean_object* v_a_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3534_; 
lean_dec_ref(v___x_2977_);
lean_del_object(v___x_2970_);
lean_dec(v_fst_2967_);
lean_dec(v_name_2957_);
lean_dec(v_head_2941_);
lean_del_object(v___x_2939_);
lean_dec(v_head_2937_);
lean_del_object(v___x_2935_);
v_a_3527_ = lean_ctor_get(v___x_3476_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3476_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3529_ = v___x_3476_;
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_a_3527_);
lean_dec(v___x_3476_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v___x_3532_; 
if (v_isShared_3530_ == 0)
{
v___x_3532_ = v___x_3529_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_a_3527_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
}
}
else
{
lean_object* v_a_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3542_; 
lean_dec_ref(v___x_2977_);
lean_del_object(v___x_2970_);
lean_dec(v_fst_2967_);
lean_dec(v_name_2957_);
lean_dec(v_head_2941_);
lean_del_object(v___x_2939_);
lean_dec(v_head_2937_);
lean_del_object(v___x_2935_);
v_a_3535_ = lean_ctor_get(v___x_3472_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3472_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3537_ = v___x_3472_;
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_a_3535_);
lean_dec(v___x_3472_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3540_; 
if (v_isShared_3538_ == 0)
{
v___x_3540_ = v___x_3537_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_a_3535_);
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
else
{
lean_object* v_a_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3550_; 
lean_dec_ref(v___x_2977_);
lean_del_object(v___x_2970_);
lean_dec(v_fst_2967_);
lean_dec(v_name_2957_);
lean_dec(v_head_2941_);
lean_del_object(v___x_2939_);
lean_dec(v_head_2937_);
lean_del_object(v___x_2935_);
v_a_3543_ = lean_ctor_get(v___x_3467_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3545_ = v___x_3467_;
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_a_3543_);
lean_dec(v___x_3467_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___x_3548_; 
if (v_isShared_3546_ == 0)
{
v___x_3548_ = v___x_3545_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_a_3543_);
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
else
{
lean_object* v_a_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3559_; 
lean_dec_ref(v___x_2977_);
lean_del_object(v___x_2970_);
lean_dec(v_fst_2967_);
lean_dec(v_importArts_2958_);
lean_dec(v_name_2957_);
lean_dec(v_head_2941_);
lean_del_object(v___x_2939_);
lean_dec(v_head_2937_);
lean_del_object(v___x_2935_);
v_a_3552_ = lean_ctor_get(v___x_3292_, 0);
v_isSharedCheck_3559_ = !lean_is_exclusive(v___x_3292_);
if (v_isSharedCheck_3559_ == 0)
{
v___x_3554_ = v___x_3292_;
v_isShared_3555_ = v_isSharedCheck_3559_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_a_3552_);
lean_dec(v___x_3292_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3559_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v___x_3557_; 
if (v_isShared_3555_ == 0)
{
v___x_3557_ = v___x_3554_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_a_3552_);
v___x_3557_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
return v___x_3557_;
}
}
}
v___jp_2978_:
{
lean_object* v___x_2997_; lean_object* v_messages_2998_; lean_object* v_env_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3122_; 
v___x_2997_ = lean_st_ref_get(v___y_2988_);
lean_dec(v___y_2988_);
v_messages_2998_ = lean_ctor_get(v___x_2997_, 6);
v_env_2999_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3122_ == 0)
{
lean_object* v_unused_3123_; lean_object* v_unused_3124_; lean_object* v_unused_3125_; lean_object* v_unused_3126_; lean_object* v_unused_3127_; lean_object* v_unused_3128_; lean_object* v_unused_3129_; 
v_unused_3123_ = lean_ctor_get(v___x_2997_, 8);
lean_dec(v_unused_3123_);
v_unused_3124_ = lean_ctor_get(v___x_2997_, 7);
lean_dec(v_unused_3124_);
v_unused_3125_ = lean_ctor_get(v___x_2997_, 5);
lean_dec(v_unused_3125_);
v_unused_3126_ = lean_ctor_get(v___x_2997_, 4);
lean_dec(v_unused_3126_);
v_unused_3127_ = lean_ctor_get(v___x_2997_, 3);
lean_dec(v_unused_3127_);
v_unused_3128_ = lean_ctor_get(v___x_2997_, 2);
lean_dec(v_unused_3128_);
v_unused_3129_ = lean_ctor_get(v___x_2997_, 1);
lean_dec(v_unused_3129_);
v___x_3001_ = v___x_2997_;
v_isShared_3002_ = v_isSharedCheck_3122_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_messages_2998_);
lean_inc(v_env_2999_);
lean_dec(v___x_2997_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3122_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v_unreported_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
v_unreported_3003_ = lean_ctor_get(v_messages_2998_, 1);
v___x_3004_ = lean_box(0);
v___x_3005_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_unreported_3003_, v___x_3004_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3112_; 
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3112_ == 0)
{
lean_object* v_unused_3113_; 
v_unused_3113_ = lean_ctor_get(v___x_3005_, 0);
lean_dec(v_unused_3113_);
v___x_3007_ = v___x_3005_;
v_isShared_3008_ = v_isSharedCheck_3112_;
goto v_resetjp_3006_;
}
else
{
lean_dec(v___x_3005_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3112_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
uint8_t v___x_3009_; 
v___x_3009_ = l_Lean_MessageLog_hasErrors(v_messages_2998_);
lean_dec_ref(v_messages_2998_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
lean_del_object(v___x_3007_);
v___x_3010_ = ((lean_object*)(l_main___closed__9));
lean_inc(v_head_2937_);
v___x_3011_ = l_System_FilePath_addExtension(v_head_2937_, v___x_3010_);
lean_inc_ref(v_env_2999_);
v___x_3012_ = l___private_LeanIR_0__mkIRSigData(v_env_2999_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; lean_object* v___x_3014_; 
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
lean_inc(v_a_3013_);
lean_dec_ref_known(v___x_3012_, 1);
lean_inc_ref(v_env_2999_);
v___x_3014_ = l___private_LeanIR_0__mkIRData(v_env_2999_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v_a_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3020_; 
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc(v_a_3015_);
lean_dec_ref_known(v___x_3014_, 1);
v___x_3016_ = l_Lean_Environment_mainModule(v_env_2999_);
v___x_3017_ = ((lean_object*)(l_main___closed__11));
v___x_3018_ = l_Lean_Name_append(v___x_3016_, v___x_3017_);
if (v_isShared_2971_ == 0)
{
lean_ctor_set(v___x_2970_, 1, v_a_3013_);
lean_ctor_set(v___x_2970_, 0, v___x_3011_);
v___x_3020_ = v___x_2970_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v___x_3011_);
lean_ctor_set(v_reuseFailAlloc_3091_, 1, v_a_3013_);
v___x_3020_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
lean_object* v___x_3022_; 
lean_inc(v_head_2937_);
if (v_isShared_2940_ == 0)
{
lean_ctor_set_tag(v___x_2939_, 0);
lean_ctor_set(v___x_2939_, 1, v_a_3015_);
v___x_3022_ = v___x_2939_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_head_2937_);
lean_ctor_set(v_reuseFailAlloc_3090_, 1, v_a_3015_);
v___x_3022_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3023_ = lean_unsigned_to_nat(2u);
v___x_3024_ = lean_mk_empty_array_with_capacity(v___x_3023_);
v___x_3025_ = lean_array_push(v___x_3024_, v___x_3020_);
v___x_3026_ = lean_array_push(v___x_3025_, v___x_3022_);
v___x_3027_ = l_Lean_saveModuleDataParts(v___x_3018_, v___x_3026_);
lean_dec_ref(v___x_3026_);
lean_dec(v___x_3018_);
if (lean_obj_tag(v___x_3027_) == 0)
{
uint8_t v___x_3028_; lean_object* v___x_3029_; 
lean_dec_ref_known(v___x_3027_, 1);
v___x_3028_ = 1;
v___x_3029_ = lean_io_prim_handle_mk(v_head_2941_, v___x_3028_);
if (lean_obj_tag(v___x_3029_) == 0)
{
lean_object* v_a_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3035_; 
lean_dec(v_head_2941_);
v_a_3030_ = lean_ctor_get(v___x_3029_, 0);
lean_inc(v_a_3030_);
lean_dec_ref_known(v___x_3029_, 1);
v___x_3031_ = ((lean_object*)(l_main___closed__12));
v___x_3032_ = l_Lean_Options_empty;
v___x_3033_ = lean_obj_once(&l_main___closed__13, &l_main___closed__13_once, _init_l_main___closed__13);
lean_inc_ref(v___y_2993_);
lean_inc_ref(v___y_2987_);
lean_inc_ref(v___y_2991_);
lean_inc_ref(v___y_2995_);
lean_inc_ref(v___y_2994_);
lean_inc_ref(v___y_2996_);
lean_inc(v___y_2992_);
lean_inc_ref(v_env_2999_);
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 8, v___y_2993_);
lean_ctor_set(v___x_3001_, 7, v___y_2987_);
lean_ctor_set(v___x_3001_, 6, v___y_2991_);
lean_ctor_set(v___x_3001_, 5, v___y_2995_);
lean_ctor_set(v___x_3001_, 4, v___y_2994_);
lean_ctor_set(v___x_3001_, 3, v___y_2990_);
lean_ctor_set(v___x_3001_, 2, v___y_2996_);
lean_ctor_set(v___x_3001_, 1, v___y_2992_);
v___x_3035_ = v___x_3001_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_env_2999_);
lean_ctor_set(v_reuseFailAlloc_3059_, 1, v___y_2992_);
lean_ctor_set(v_reuseFailAlloc_3059_, 2, v___y_2996_);
lean_ctor_set(v_reuseFailAlloc_3059_, 3, v___y_2990_);
lean_ctor_set(v_reuseFailAlloc_3059_, 4, v___y_2994_);
lean_ctor_set(v_reuseFailAlloc_3059_, 5, v___y_2995_);
lean_ctor_set(v_reuseFailAlloc_3059_, 6, v___y_2991_);
lean_ctor_set(v_reuseFailAlloc_3059_, 7, v___y_2987_);
lean_ctor_set(v_reuseFailAlloc_3059_, 8, v___y_2993_);
v___x_3035_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___f_3038_; lean_object* v___x_3039_; 
v___x_3036_ = lean_box(v___x_2960_);
v___x_3037_ = lean_box(v___y_2983_);
lean_inc_ref(v___y_2986_);
lean_inc(v___y_2985_);
lean_inc(v___y_2982_);
lean_inc(v___y_2980_);
lean_inc(v___y_2979_);
lean_inc_ref(v___y_2984_);
v___f_3038_ = lean_alloc_closure((void*)(l_main___lam__1___boxed), 17, 16);
lean_closure_set(v___f_3038_, 0, v___x_3035_);
lean_closure_set(v___f_3038_, 1, v___x_3032_);
lean_closure_set(v___f_3038_, 2, v_head_2937_);
lean_closure_set(v___f_3038_, 3, v___y_2984_);
lean_closure_set(v___f_3038_, 4, v___y_2981_);
lean_closure_set(v___f_3038_, 5, v___y_2979_);
lean_closure_set(v___f_3038_, 6, v___x_3033_);
lean_closure_set(v___f_3038_, 7, v___y_2980_);
lean_closure_set(v___f_3038_, 8, v___y_2982_);
lean_closure_set(v___f_3038_, 9, v___x_2976_);
lean_closure_set(v___f_3038_, 10, v___y_2985_);
lean_closure_set(v___f_3038_, 11, v___x_3036_);
lean_closure_set(v___f_3038_, 12, v_name_2957_);
lean_closure_set(v___f_3038_, 13, v_a_3030_);
lean_closure_set(v___f_3038_, 14, v___x_3037_);
lean_closure_set(v___f_3038_, 15, v___y_2986_);
v___x_3039_ = l_Lean_profileitIOUnsafe___redArg(v___x_3031_, v___x_2977_, v___f_3038_, v___y_2989_);
lean_dec_ref(v___x_2977_);
if (lean_obj_tag(v___x_3039_) == 0)
{
lean_object* v___x_3040_; uint8_t v___x_3041_; 
lean_dec_ref_known(v___x_3039_, 1);
v___x_3040_ = lean_display_cumulative_profiling_times();
v___x_3041_ = lean_unbox(v_fst_2967_);
lean_dec(v_fst_2967_);
if (v___x_3041_ == 0)
{
lean_dec_ref(v_env_2999_);
goto v___jp_2928_;
}
else
{
lean_object* v___x_3042_; 
v___x_3042_ = l_Lean_Environment_displayStats(v_env_2999_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_dec_ref_known(v___x_3042_, 1);
goto v___jp_2928_;
}
else
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3045_ = v___x_3042_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_3042_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3048_; 
if (v_isShared_3046_ == 0)
{
v___x_3048_ = v___x_3045_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_a_3043_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
}
}
}
else
{
lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3058_; 
lean_dec_ref(v_env_2999_);
lean_dec(v_fst_2967_);
v_a_3051_ = lean_ctor_get(v___x_3039_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3039_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3053_ = v___x_3039_;
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v___x_3039_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3056_; 
if (v_isShared_3054_ == 0)
{
v___x_3056_ = v___x_3053_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_a_3051_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
}
}
else
{
lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; 
lean_dec_ref_known(v___x_3029_, 1);
lean_del_object(v___x_3001_);
lean_dec_ref(v_env_2999_);
lean_dec_ref(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec(v___y_2981_);
lean_dec_ref(v___x_2977_);
lean_dec(v_fst_2967_);
lean_dec(v_name_2957_);
lean_dec(v_head_2937_);
v___x_3060_ = ((lean_object*)(l_main___closed__14));
v___x_3061_ = lean_string_append(v___x_3060_, v_head_2941_);
lean_dec(v_head_2941_);
v___x_3062_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__1));
v___x_3063_ = lean_string_append(v___x_3061_, v___x_3062_);
v___x_3064_ = l_IO_eprintln___at___00main_spec__6(v___x_3063_);
if (lean_obj_tag(v___x_3064_) == 0)
{
lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3072_; 
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3072_ == 0)
{
lean_object* v_unused_3073_; 
v_unused_3073_ = lean_ctor_get(v___x_3064_, 0);
lean_dec(v_unused_3073_);
v___x_3066_ = v___x_3064_;
v_isShared_3067_ = v_isSharedCheck_3072_;
goto v_resetjp_3065_;
}
else
{
lean_dec(v___x_3064_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3072_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3068_; lean_object* v___x_3070_; 
v___x_3068_ = l_main___boxed__const__1;
if (v_isShared_3067_ == 0)
{
lean_ctor_set(v___x_3066_, 0, v___x_3068_);
v___x_3070_ = v___x_3066_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v___x_3068_);
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
lean_object* v_a_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3081_; 
v_a_3074_ = lean_ctor_get(v___x_3064_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3076_ = v___x_3064_;
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_a_3074_);
lean_dec(v___x_3064_);
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
}
else
{
lean_object* v_a_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3089_; 
lean_del_object(v___x_3001_);
lean_dec_ref(v_env_2999_);
lean_dec_ref(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec(v___y_2981_);
lean_dec_ref(v___x_2977_);
lean_dec(v_fst_2967_);
lean_dec(v_name_2957_);
lean_dec(v_head_2941_);
lean_dec(v_head_2937_);
v_a_3082_ = lean_ctor_get(v___x_3027_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3084_ = v___x_3027_;
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_a_3082_);
lean_dec(v___x_3027_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___x_3087_; 
if (v_isShared_3085_ == 0)
{
v___x_3087_ = v___x_3084_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_a_3082_);
v___x_3087_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
return v___x_3087_;
}
}
}
}
}
}
else
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3099_; 
lean_dec(v_a_3013_);
lean_dec_ref(v___x_3011_);
lean_del_object(v___x_3001_);
lean_dec_ref(v_env_2999_);
lean_dec_ref(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec(v___y_2981_);
lean_dec_ref(v___x_2977_);
lean_del_object(v___x_2970_);
lean_dec(v_fst_2967_);
lean_dec(v_name_2957_);
lean_dec(v_head_2941_);
lean_del_object(v___x_2939_);
lean_dec(v_head_2937_);
v_a_3092_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3094_ = v___x_3014_;
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_3014_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3097_; 
if (v_isShared_3095_ == 0)
{
v___x_3097_ = v___x_3094_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_a_3092_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
}
else
{
lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3107_; 
lean_dec_ref(v___x_3011_);
lean_del_object(v___x_3001_);
lean_dec_ref(v_env_2999_);
lean_dec_ref(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec(v___y_2981_);
lean_dec_ref(v___x_2977_);
lean_del_object(v___x_2970_);
lean_dec(v_fst_2967_);
lean_dec(v_name_2957_);
lean_dec(v_head_2941_);
lean_del_object(v___x_2939_);
lean_dec(v_head_2937_);
v_a_3100_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3102_ = v___x_3012_;
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v___x_3012_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3105_; 
if (v_isShared_3103_ == 0)
{
v___x_3105_ = v___x_3102_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_a_3100_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
}
}
else
{
lean_object* v___x_3108_; lean_object* v___x_3110_; 
lean_del_object(v___x_3001_);
lean_dec_ref(v_env_2999_);
lean_dec_ref(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec(v___y_2981_);
lean_dec_ref(v___x_2977_);
lean_del_object(v___x_2970_);
lean_dec(v_fst_2967_);
lean_dec(v_name_2957_);
lean_dec(v_head_2941_);
lean_del_object(v___x_2939_);
lean_dec(v_head_2937_);
v___x_3108_ = l_main___boxed__const__1;
if (v_isShared_3008_ == 0)
{
lean_ctor_set(v___x_3007_, 0, v___x_3108_);
v___x_3110_ = v___x_3007_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3108_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
else
{
lean_object* v_a_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3121_; 
lean_del_object(v___x_3001_);
lean_dec_ref(v_env_2999_);
lean_dec_ref(v_messages_2998_);
lean_dec_ref(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec(v___y_2981_);
lean_dec_ref(v___x_2977_);
lean_del_object(v___x_2970_);
lean_dec(v_fst_2967_);
lean_dec(v_name_2957_);
lean_dec(v_head_2941_);
lean_del_object(v___x_2939_);
lean_dec(v_head_2937_);
v_a_3114_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3121_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3116_ = v___x_3005_;
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_dec(v___x_3005_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3119_; 
if (v_isShared_3117_ == 0)
{
v___x_3119_ = v___x_3116_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_a_3114_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
}
}
}
v___jp_3130_:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; size_t v_sz_3163_; size_t v___x_3164_; lean_object* v___x_3165_; 
lean_inc_ref(v___y_3158_);
v___x_3160_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3160_, 0, v___y_3159_);
lean_ctor_set(v___x_3160_, 1, v_nextMacroScope_3139_);
lean_ctor_set(v___x_3160_, 2, v_ngen_3140_);
lean_ctor_set(v___x_3160_, 3, v_auxDeclNGen_3141_);
lean_ctor_set(v___x_3160_, 4, v_traceState_3142_);
lean_ctor_set(v___x_3160_, 5, v___y_3158_);
lean_ctor_set(v___x_3160_, 6, v_messages_3143_);
lean_ctor_set(v___x_3160_, 7, v_infoState_3144_);
lean_ctor_set(v___x_3160_, 8, v_snapshotTasks_3145_);
v___x_3161_ = lean_st_ref_put(v___y_3146_, v___x_3160_);
v___x_3162_ = lean_box(0);
v_sz_3163_ = lean_array_size(v___y_3156_);
v___x_3164_ = ((size_t)0ULL);
v___x_3165_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(v___y_3156_, v_sz_3163_, v___x_3164_, v___x_3162_, v___y_3150_, v___y_3146_);
lean_dec_ref(v___y_3156_);
if (lean_obj_tag(v___x_3165_) == 0)
{
lean_dec_ref_known(v___x_3165_, 1);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3146_);
v___y_2979_ = v___y_3131_;
v___y_2980_ = v___y_3133_;
v___y_2981_ = v___y_3132_;
v___y_2982_ = v___y_3134_;
v___y_2983_ = v___y_3136_;
v___y_2984_ = v___y_3135_;
v___y_2985_ = v___y_3137_;
v___y_2986_ = v___y_3138_;
v___y_2987_ = v___y_3147_;
v___y_2988_ = v___y_3154_;
v___y_2989_ = v___y_3148_;
v___y_2990_ = v___y_3149_;
v___y_2991_ = v___y_3155_;
v___y_2992_ = v___y_3151_;
v___y_2993_ = v___y_3157_;
v___y_2994_ = v___y_3152_;
v___y_2995_ = v___y_3158_;
v___y_2996_ = v___y_3153_;
goto v___jp_2978_;
}
else
{
if (lean_obj_tag(v___x_3165_) == 0)
{
lean_dec_ref_known(v___x_3165_, 1);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3146_);
v___y_2979_ = v___y_3131_;
v___y_2980_ = v___y_3133_;
v___y_2981_ = v___y_3132_;
v___y_2982_ = v___y_3134_;
v___y_2983_ = v___y_3136_;
v___y_2984_ = v___y_3135_;
v___y_2985_ = v___y_3137_;
v___y_2986_ = v___y_3138_;
v___y_2987_ = v___y_3147_;
v___y_2988_ = v___y_3154_;
v___y_2989_ = v___y_3148_;
v___y_2990_ = v___y_3149_;
v___y_2991_ = v___y_3155_;
v___y_2992_ = v___y_3151_;
v___y_2993_ = v___y_3157_;
v___y_2994_ = v___y_3152_;
v___y_2995_ = v___y_3158_;
v___y_2996_ = v___y_3153_;
goto v___jp_2978_;
}
else
{
lean_object* v_a_3166_; uint8_t v___x_3167_; 
v_a_3166_ = lean_ctor_get(v___x_3165_, 0);
lean_inc(v_a_3166_);
lean_dec_ref_known(v___x_3165_, 1);
v___x_3167_ = l_Lean_Exception_isInterrupt(v_a_3166_);
if (v___x_3167_ == 0)
{
lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3168_ = l_Lean_Exception_toMessageData(v_a_3166_);
v___x_3169_ = l_Lean_logError___at___00main_spec__14(v___x_3168_, v___y_3150_, v___y_3146_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3150_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_dec_ref_known(v___x_3169_, 1);
v___y_2979_ = v___y_3131_;
v___y_2980_ = v___y_3133_;
v___y_2981_ = v___y_3132_;
v___y_2982_ = v___y_3134_;
v___y_2983_ = v___y_3136_;
v___y_2984_ = v___y_3135_;
v___y_2985_ = v___y_3137_;
v___y_2986_ = v___y_3138_;
v___y_2987_ = v___y_3147_;
v___y_2988_ = v___y_3154_;
v___y_2989_ = v___y_3148_;
v___y_2990_ = v___y_3149_;
v___y_2991_ = v___y_3155_;
v___y_2992_ = v___y_3151_;
v___y_2993_ = v___y_3157_;
v___y_2994_ = v___y_3152_;
v___y_2995_ = v___y_3158_;
v___y_2996_ = v___y_3153_;
goto v___jp_2978_;
}
else
{
lean_object* v___x_3170_; lean_object* v___x_3171_; 
lean_dec_ref_known(v___x_3169_, 1);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3149_);
lean_dec(v___y_3148_);
lean_dec(v___y_3132_);
lean_dec_ref(v___x_2977_);
lean_del_object(v___x_2970_);
lean_dec(v_fst_2967_);
lean_dec(v_name_2957_);
lean_dec(v_head_2941_);
lean_del_object(v___x_2939_);
lean_dec(v_head_2937_);
v___x_3170_ = lean_obj_once(&l_main___closed__18, &l_main___closed__18_once, _init_l_main___closed__18);
v___x_3171_ = l_panic___at___00main_spec__5(v___x_3170_);
return v___x_3171_;
}
}
else
{
lean_dec(v_a_3166_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3146_);
v___y_2979_ = v___y_3131_;
v___y_2980_ = v___y_3133_;
v___y_2981_ = v___y_3132_;
v___y_2982_ = v___y_3134_;
v___y_2983_ = v___y_3136_;
v___y_2984_ = v___y_3135_;
v___y_2985_ = v___y_3137_;
v___y_2986_ = v___y_3138_;
v___y_2987_ = v___y_3147_;
v___y_2988_ = v___y_3154_;
v___y_2989_ = v___y_3148_;
v___y_2990_ = v___y_3149_;
v___y_2991_ = v___y_3155_;
v___y_2992_ = v___y_3151_;
v___y_2993_ = v___y_3157_;
v___y_2994_ = v___y_3152_;
v___y_2995_ = v___y_3158_;
v___y_2996_ = v___y_3153_;
goto v___jp_2978_;
}
}
}
}
v___jp_3172_:
{
lean_object* v_toCold_3196_; lean_object* v_currRecDepth_3197_; lean_object* v_ref_3198_; uint8_t v_suppressElabErrors_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3249_; 
v_toCold_3196_ = lean_ctor_get(v___y_3194_, 0);
v_currRecDepth_3197_ = lean_ctor_get(v___y_3194_, 1);
v_ref_3198_ = lean_ctor_get(v___y_3194_, 2);
v_suppressElabErrors_3199_ = lean_ctor_get_uint8(v___y_3194_, sizeof(void*)*3 + 1);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___y_3194_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3201_ = v___y_3194_;
v_isShared_3202_ = v_isSharedCheck_3249_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_ref_3198_);
lean_inc(v_currRecDepth_3197_);
lean_inc(v_toCold_3196_);
lean_dec(v___y_3194_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3249_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v_fileName_3203_; lean_object* v_fileMap_3204_; lean_object* v_currNamespace_3205_; lean_object* v_openDecls_3206_; lean_object* v_initHeartbeats_3207_; lean_object* v_maxHeartbeats_3208_; lean_object* v_quotContext_3209_; lean_object* v_currMacroScope_3210_; lean_object* v_cancelTk_x3f_3211_; lean_object* v_inheritedTraceOptions_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3246_; 
v_fileName_3203_ = lean_ctor_get(v_toCold_3196_, 0);
v_fileMap_3204_ = lean_ctor_get(v_toCold_3196_, 1);
v_currNamespace_3205_ = lean_ctor_get(v_toCold_3196_, 4);
v_openDecls_3206_ = lean_ctor_get(v_toCold_3196_, 5);
v_initHeartbeats_3207_ = lean_ctor_get(v_toCold_3196_, 6);
v_maxHeartbeats_3208_ = lean_ctor_get(v_toCold_3196_, 7);
v_quotContext_3209_ = lean_ctor_get(v_toCold_3196_, 8);
v_currMacroScope_3210_ = lean_ctor_get(v_toCold_3196_, 9);
v_cancelTk_x3f_3211_ = lean_ctor_get(v_toCold_3196_, 10);
v_inheritedTraceOptions_3212_ = lean_ctor_get(v_toCold_3196_, 11);
v_isSharedCheck_3246_ = !lean_is_exclusive(v_toCold_3196_);
if (v_isSharedCheck_3246_ == 0)
{
lean_object* v_unused_3247_; lean_object* v_unused_3248_; 
v_unused_3247_ = lean_ctor_get(v_toCold_3196_, 3);
lean_dec(v_unused_3247_);
v_unused_3248_ = lean_ctor_get(v_toCold_3196_, 2);
lean_dec(v_unused_3248_);
v___x_3214_ = v_toCold_3196_;
v_isShared_3215_ = v_isSharedCheck_3246_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_inheritedTraceOptions_3212_);
lean_inc(v_cancelTk_x3f_3211_);
lean_inc(v_currMacroScope_3210_);
lean_inc(v_quotContext_3209_);
lean_inc(v_maxHeartbeats_3208_);
lean_inc(v_initHeartbeats_3207_);
lean_inc(v_openDecls_3206_);
lean_inc(v_currNamespace_3205_);
lean_inc(v_fileMap_3204_);
lean_inc(v_fileName_3203_);
lean_dec(v_toCold_3196_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3246_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3219_; 
v___x_3216_ = l_Lean_maxRecDepth;
v___x_3217_ = l_Lean_Option_get___at___00main_spec__9(v___x_2977_, v___x_3216_);
lean_inc_ref(v___x_2977_);
if (v_isShared_3215_ == 0)
{
lean_ctor_set(v___x_3214_, 3, v___x_3217_);
lean_ctor_set(v___x_3214_, 2, v___x_2977_);
v___x_3219_ = v___x_3214_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v_fileName_3203_);
lean_ctor_set(v_reuseFailAlloc_3245_, 1, v_fileMap_3204_);
lean_ctor_set(v_reuseFailAlloc_3245_, 2, v___x_2977_);
lean_ctor_set(v_reuseFailAlloc_3245_, 3, v___x_3217_);
lean_ctor_set(v_reuseFailAlloc_3245_, 4, v_currNamespace_3205_);
lean_ctor_set(v_reuseFailAlloc_3245_, 5, v_openDecls_3206_);
lean_ctor_set(v_reuseFailAlloc_3245_, 6, v_initHeartbeats_3207_);
lean_ctor_set(v_reuseFailAlloc_3245_, 7, v_maxHeartbeats_3208_);
lean_ctor_set(v_reuseFailAlloc_3245_, 8, v_quotContext_3209_);
lean_ctor_set(v_reuseFailAlloc_3245_, 9, v_currMacroScope_3210_);
lean_ctor_set(v_reuseFailAlloc_3245_, 10, v_cancelTk_x3f_3211_);
lean_ctor_set(v_reuseFailAlloc_3245_, 11, v_inheritedTraceOptions_3212_);
v___x_3219_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
lean_object* v___x_3221_; 
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 0, v___x_3219_);
v___x_3221_ = v___x_3201_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v___x_3219_);
lean_ctor_set(v_reuseFailAlloc_3244_, 1, v_currRecDepth_3197_);
lean_ctor_set(v_reuseFailAlloc_3244_, 2, v_ref_3198_);
lean_ctor_set_uint8(v_reuseFailAlloc_3244_, sizeof(void*)*3 + 1, v_suppressElabErrors_3199_);
v___x_3221_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
lean_object* v___x_3222_; lean_object* v_env_3223_; lean_object* v_nextMacroScope_3224_; lean_object* v_ngen_3225_; lean_object* v_auxDeclNGen_3226_; lean_object* v_traceState_3227_; lean_object* v_messages_3228_; lean_object* v_infoState_3229_; lean_object* v_snapshotTasks_3230_; lean_object* v___x_3231_; uint8_t v___x_3232_; 
lean_ctor_set_uint8(v___x_3221_, sizeof(void*)*3, v___y_3187_);
v___x_3222_ = lean_st_ref_take(v___y_3195_);
v_env_3223_ = lean_ctor_get(v___x_3222_, 0);
lean_inc_ref(v_env_3223_);
v_nextMacroScope_3224_ = lean_ctor_get(v___x_3222_, 1);
lean_inc(v_nextMacroScope_3224_);
v_ngen_3225_ = lean_ctor_get(v___x_3222_, 2);
lean_inc_ref(v_ngen_3225_);
v_auxDeclNGen_3226_ = lean_ctor_get(v___x_3222_, 3);
lean_inc_ref(v_auxDeclNGen_3226_);
v_traceState_3227_ = lean_ctor_get(v___x_3222_, 4);
lean_inc_ref(v_traceState_3227_);
v_messages_3228_ = lean_ctor_get(v___x_3222_, 6);
lean_inc_ref(v_messages_3228_);
v_infoState_3229_ = lean_ctor_get(v___x_3222_, 7);
lean_inc_ref(v_infoState_3229_);
v_snapshotTasks_3230_ = lean_ctor_get(v___x_3222_, 8);
lean_inc_ref(v_snapshotTasks_3230_);
lean_dec(v___x_3222_);
v___x_3231_ = lean_array_get_size(v___y_3191_);
v___x_3232_ = lean_nat_dec_lt(v___x_2976_, v___x_3231_);
if (v___x_3232_ == 0)
{
lean_object* v___x_3233_; 
lean_inc_ref(v___y_3184_);
v___x_3233_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3184_, v_env_3223_, v___x_2953_);
v___y_3131_ = v___y_3173_;
v___y_3132_ = v___y_3175_;
v___y_3133_ = v___y_3174_;
v___y_3134_ = v___y_3176_;
v___y_3135_ = v___y_3178_;
v___y_3136_ = v___y_3177_;
v___y_3137_ = v___y_3179_;
v___y_3138_ = v___y_3180_;
v_nextMacroScope_3139_ = v_nextMacroScope_3224_;
v_ngen_3140_ = v_ngen_3225_;
v_auxDeclNGen_3141_ = v_auxDeclNGen_3226_;
v_traceState_3142_ = v_traceState_3227_;
v_messages_3143_ = v_messages_3228_;
v_infoState_3144_ = v_infoState_3229_;
v_snapshotTasks_3145_ = v_snapshotTasks_3230_;
v___y_3146_ = v___y_3195_;
v___y_3147_ = v___y_3181_;
v___y_3148_ = v___y_3182_;
v___y_3149_ = v___y_3183_;
v___y_3150_ = v___x_3221_;
v___y_3151_ = v___y_3185_;
v___y_3152_ = v___y_3186_;
v___y_3153_ = v___y_3188_;
v___y_3154_ = v___y_3189_;
v___y_3155_ = v___y_3190_;
v___y_3156_ = v___y_3191_;
v___y_3157_ = v___y_3192_;
v___y_3158_ = v___y_3193_;
v___y_3159_ = v___x_3233_;
goto v___jp_3130_;
}
else
{
uint8_t v___x_3234_; 
v___x_3234_ = lean_nat_dec_le(v___x_3231_, v___x_3231_);
if (v___x_3234_ == 0)
{
if (v___x_3232_ == 0)
{
lean_object* v___x_3235_; 
lean_inc_ref(v___y_3184_);
v___x_3235_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3184_, v_env_3223_, v___x_2953_);
v___y_3131_ = v___y_3173_;
v___y_3132_ = v___y_3175_;
v___y_3133_ = v___y_3174_;
v___y_3134_ = v___y_3176_;
v___y_3135_ = v___y_3178_;
v___y_3136_ = v___y_3177_;
v___y_3137_ = v___y_3179_;
v___y_3138_ = v___y_3180_;
v_nextMacroScope_3139_ = v_nextMacroScope_3224_;
v_ngen_3140_ = v_ngen_3225_;
v_auxDeclNGen_3141_ = v_auxDeclNGen_3226_;
v_traceState_3142_ = v_traceState_3227_;
v_messages_3143_ = v_messages_3228_;
v_infoState_3144_ = v_infoState_3229_;
v_snapshotTasks_3145_ = v_snapshotTasks_3230_;
v___y_3146_ = v___y_3195_;
v___y_3147_ = v___y_3181_;
v___y_3148_ = v___y_3182_;
v___y_3149_ = v___y_3183_;
v___y_3150_ = v___x_3221_;
v___y_3151_ = v___y_3185_;
v___y_3152_ = v___y_3186_;
v___y_3153_ = v___y_3188_;
v___y_3154_ = v___y_3189_;
v___y_3155_ = v___y_3190_;
v___y_3156_ = v___y_3191_;
v___y_3157_ = v___y_3192_;
v___y_3158_ = v___y_3193_;
v___y_3159_ = v___x_3235_;
goto v___jp_3130_;
}
else
{
size_t v___x_3236_; size_t v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3236_ = ((size_t)0ULL);
v___x_3237_ = lean_usize_of_nat(v___x_3231_);
v___x_3238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3191_, v___x_3236_, v___x_3237_, v___x_2953_);
lean_inc_ref(v___y_3184_);
v___x_3239_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3184_, v_env_3223_, v___x_3238_);
v___y_3131_ = v___y_3173_;
v___y_3132_ = v___y_3175_;
v___y_3133_ = v___y_3174_;
v___y_3134_ = v___y_3176_;
v___y_3135_ = v___y_3178_;
v___y_3136_ = v___y_3177_;
v___y_3137_ = v___y_3179_;
v___y_3138_ = v___y_3180_;
v_nextMacroScope_3139_ = v_nextMacroScope_3224_;
v_ngen_3140_ = v_ngen_3225_;
v_auxDeclNGen_3141_ = v_auxDeclNGen_3226_;
v_traceState_3142_ = v_traceState_3227_;
v_messages_3143_ = v_messages_3228_;
v_infoState_3144_ = v_infoState_3229_;
v_snapshotTasks_3145_ = v_snapshotTasks_3230_;
v___y_3146_ = v___y_3195_;
v___y_3147_ = v___y_3181_;
v___y_3148_ = v___y_3182_;
v___y_3149_ = v___y_3183_;
v___y_3150_ = v___x_3221_;
v___y_3151_ = v___y_3185_;
v___y_3152_ = v___y_3186_;
v___y_3153_ = v___y_3188_;
v___y_3154_ = v___y_3189_;
v___y_3155_ = v___y_3190_;
v___y_3156_ = v___y_3191_;
v___y_3157_ = v___y_3192_;
v___y_3158_ = v___y_3193_;
v___y_3159_ = v___x_3239_;
goto v___jp_3130_;
}
}
else
{
size_t v___x_3240_; size_t v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; 
v___x_3240_ = ((size_t)0ULL);
v___x_3241_ = lean_usize_of_nat(v___x_3231_);
v___x_3242_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3191_, v___x_3240_, v___x_3241_, v___x_2953_);
lean_inc_ref(v___y_3184_);
v___x_3243_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3184_, v_env_3223_, v___x_3242_);
v___y_3131_ = v___y_3173_;
v___y_3132_ = v___y_3175_;
v___y_3133_ = v___y_3174_;
v___y_3134_ = v___y_3176_;
v___y_3135_ = v___y_3178_;
v___y_3136_ = v___y_3177_;
v___y_3137_ = v___y_3179_;
v___y_3138_ = v___y_3180_;
v_nextMacroScope_3139_ = v_nextMacroScope_3224_;
v_ngen_3140_ = v_ngen_3225_;
v_auxDeclNGen_3141_ = v_auxDeclNGen_3226_;
v_traceState_3142_ = v_traceState_3227_;
v_messages_3143_ = v_messages_3228_;
v_infoState_3144_ = v_infoState_3229_;
v_snapshotTasks_3145_ = v_snapshotTasks_3230_;
v___y_3146_ = v___y_3195_;
v___y_3147_ = v___y_3181_;
v___y_3148_ = v___y_3182_;
v___y_3149_ = v___y_3183_;
v___y_3150_ = v___x_3221_;
v___y_3151_ = v___y_3185_;
v___y_3152_ = v___y_3186_;
v___y_3153_ = v___y_3188_;
v___y_3154_ = v___y_3189_;
v___y_3155_ = v___y_3190_;
v___y_3156_ = v___y_3191_;
v___y_3157_ = v___y_3192_;
v___y_3158_ = v___y_3193_;
v___y_3159_ = v___x_3243_;
goto v___jp_3130_;
}
}
}
}
}
}
}
v___jp_3250_:
{
if (v___y_3272_ == 0)
{
lean_object* v___x_3273_; lean_object* v_env_3274_; lean_object* v_nextMacroScope_3275_; lean_object* v_ngen_3276_; lean_object* v_auxDeclNGen_3277_; lean_object* v_traceState_3278_; lean_object* v_messages_3279_; lean_object* v_infoState_3280_; lean_object* v_snapshotTasks_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3290_; 
v___x_3273_ = lean_st_ref_take(v___y_3269_);
v_env_3274_ = lean_ctor_get(v___x_3273_, 0);
v_nextMacroScope_3275_ = lean_ctor_get(v___x_3273_, 1);
v_ngen_3276_ = lean_ctor_get(v___x_3273_, 2);
v_auxDeclNGen_3277_ = lean_ctor_get(v___x_3273_, 3);
v_traceState_3278_ = lean_ctor_get(v___x_3273_, 4);
v_messages_3279_ = lean_ctor_get(v___x_3273_, 6);
v_infoState_3280_ = lean_ctor_get(v___x_3273_, 7);
v_snapshotTasks_3281_ = lean_ctor_get(v___x_3273_, 8);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3273_);
if (v_isSharedCheck_3290_ == 0)
{
lean_object* v_unused_3291_; 
v_unused_3291_ = lean_ctor_get(v___x_3273_, 5);
lean_dec(v_unused_3291_);
v___x_3283_ = v___x_3273_;
v_isShared_3284_ = v_isSharedCheck_3290_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_snapshotTasks_3281_);
lean_inc(v_infoState_3280_);
lean_inc(v_messages_3279_);
lean_inc(v_traceState_3278_);
lean_inc(v_auxDeclNGen_3277_);
lean_inc(v_ngen_3276_);
lean_inc(v_nextMacroScope_3275_);
lean_inc(v_env_3274_);
lean_dec(v___x_3273_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3290_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3285_; lean_object* v___x_3287_; 
v___x_3285_ = l_Lean_Kernel_enableDiag(v_env_3274_, v___y_3268_);
lean_inc_ref(v___y_3264_);
if (v_isShared_3284_ == 0)
{
lean_ctor_set(v___x_3283_, 5, v___y_3264_);
lean_ctor_set(v___x_3283_, 0, v___x_3285_);
v___x_3287_ = v___x_3283_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v___x_3285_);
lean_ctor_set(v_reuseFailAlloc_3289_, 1, v_nextMacroScope_3275_);
lean_ctor_set(v_reuseFailAlloc_3289_, 2, v_ngen_3276_);
lean_ctor_set(v_reuseFailAlloc_3289_, 3, v_auxDeclNGen_3277_);
lean_ctor_set(v_reuseFailAlloc_3289_, 4, v_traceState_3278_);
lean_ctor_set(v_reuseFailAlloc_3289_, 5, v___y_3264_);
lean_ctor_set(v_reuseFailAlloc_3289_, 6, v_messages_3279_);
lean_ctor_set(v_reuseFailAlloc_3289_, 7, v_infoState_3280_);
lean_ctor_set(v_reuseFailAlloc_3289_, 8, v_snapshotTasks_3281_);
v___x_3287_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
lean_object* v___x_3288_; 
v___x_3288_ = lean_st_ref_put(v___y_3269_, v___x_3287_);
lean_inc(v___y_3269_);
v___y_3173_ = v___y_3251_;
v___y_3174_ = v___y_3260_;
v___y_3175_ = v___y_3252_;
v___y_3176_ = v___y_3261_;
v___y_3177_ = v___y_3257_;
v___y_3178_ = v___y_3263_;
v___y_3179_ = v___y_3258_;
v___y_3180_ = v___y_3264_;
v___y_3181_ = v___y_3265_;
v___y_3182_ = v___y_3266_;
v___y_3183_ = v___y_3253_;
v___y_3184_ = v___y_3254_;
v___y_3185_ = v___y_3255_;
v___y_3186_ = v___y_3256_;
v___y_3187_ = v___y_3268_;
v___y_3188_ = v___y_3259_;
v___y_3189_ = v___y_3269_;
v___y_3190_ = v___y_3270_;
v___y_3191_ = v___y_3262_;
v___y_3192_ = v___y_3271_;
v___y_3193_ = v___y_3264_;
v___y_3194_ = v___y_3267_;
v___y_3195_ = v___y_3269_;
goto v___jp_3172_;
}
}
}
else
{
lean_inc(v___y_3269_);
v___y_3173_ = v___y_3251_;
v___y_3174_ = v___y_3260_;
v___y_3175_ = v___y_3252_;
v___y_3176_ = v___y_3261_;
v___y_3177_ = v___y_3257_;
v___y_3178_ = v___y_3263_;
v___y_3179_ = v___y_3258_;
v___y_3180_ = v___y_3264_;
v___y_3181_ = v___y_3265_;
v___y_3182_ = v___y_3266_;
v___y_3183_ = v___y_3253_;
v___y_3184_ = v___y_3254_;
v___y_3185_ = v___y_3255_;
v___y_3186_ = v___y_3256_;
v___y_3187_ = v___y_3268_;
v___y_3188_ = v___y_3259_;
v___y_3189_ = v___y_3269_;
v___y_3190_ = v___y_3270_;
v___y_3191_ = v___y_3262_;
v___y_3192_ = v___y_3271_;
v___y_3193_ = v___y_3264_;
v___y_3194_ = v___y_3267_;
v___y_3195_ = v___y_3269_;
goto v___jp_3172_;
}
}
}
}
else
{
lean_object* v_a_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3568_; 
lean_dec(v_importArts_2958_);
lean_dec(v_name_2957_);
lean_dec(v_head_2941_);
lean_del_object(v___x_2939_);
lean_dec(v_head_2937_);
lean_del_object(v___x_2935_);
v_a_3561_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3563_ = v___x_2965_;
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_a_3561_);
lean_dec(v___x_2965_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3566_; 
if (v_isShared_3564_ == 0)
{
v___x_3566_ = v___x_3563_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3561_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
}
}
else
{
lean_object* v_a_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3577_; 
lean_del_object(v___x_2944_);
lean_dec(v_tail_2942_);
lean_dec(v_head_2941_);
lean_del_object(v___x_2939_);
lean_dec(v_head_2937_);
lean_del_object(v___x_2935_);
v_a_3570_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3572_ = v___x_2955_;
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_a_3570_);
lean_dec(v___x_2955_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3575_; 
if (v_isShared_3573_ == 0)
{
v___x_3575_ = v___x_3572_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_a_3570_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
}
}
}
}
}
else
{
lean_dec(v_tail_2932_);
lean_dec_ref_known(v_tail_2931_, 2);
lean_dec_ref_known(v_args_2906_, 2);
goto v___jp_2908_;
}
}
else
{
lean_dec_ref_known(v_args_2906_, 2);
lean_dec(v_tail_2931_);
goto v___jp_2908_;
}
}
else
{
lean_dec(v_args_2906_);
goto v___jp_2908_;
}
v___jp_2908_:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; 
v___x_2909_ = ((lean_object*)(l_main___closed__0));
v___x_2910_ = l_IO_println___at___00Lean_Environment_displayStats_spec__1(v___x_2909_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2918_; 
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_2918_ == 0)
{
lean_object* v_unused_2919_; 
v_unused_2919_ = lean_ctor_get(v___x_2910_, 0);
lean_dec(v_unused_2919_);
v___x_2912_ = v___x_2910_;
v_isShared_2913_ = v_isSharedCheck_2918_;
goto v_resetjp_2911_;
}
else
{
lean_dec(v___x_2910_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2918_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2914_; lean_object* v___x_2916_; 
v___x_2914_ = l_main___boxed__const__1;
if (v_isShared_2913_ == 0)
{
lean_ctor_set(v___x_2912_, 0, v___x_2914_);
v___x_2916_ = v___x_2912_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v___x_2914_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
else
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
v_a_2920_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2922_ = v___x_2910_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2910_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2925_; 
if (v_isShared_2923_ == 0)
{
v___x_2925_ = v___x_2922_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_a_2920_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
}
v___jp_2928_:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2929_ = l_main___boxed__const__2;
v___x_2930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2929_);
return v___x_2930_;
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_3583_, lean_object* v_a_3584_){
_start:
{
lean_object* v_res_3585_; 
v_res_3585_ = _lean_main(v_args_3583_);
return v_res_3585_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1(lean_object* v_as_3586_, lean_object* v_as_x27_3587_, lean_object* v_b_3588_, lean_object* v_a_3589_){
_start:
{
lean_object* v___x_3591_; 
v___x_3591_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_3587_, v_b_3588_);
return v___x_3591_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___boxed(lean_object* v_as_3592_, lean_object* v_as_x27_3593_, lean_object* v_b_3594_, lean_object* v_a_3595_, lean_object* v___y_3596_){
_start:
{
lean_object* v_res_3597_; 
v_res_3597_ = l_List_forIn_x27_loop___at___00main_spec__1(v_as_3592_, v_as_x27_3593_, v_b_3594_, v_a_3595_);
lean_dec(v_as_x27_3593_);
lean_dec(v_as_3592_);
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16(lean_object* v___y_3598_, lean_object* v___y_3599_){
_start:
{
lean_object* v___x_3601_; 
v___x_3601_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_3599_);
return v___x_3601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___boxed(lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_){
_start:
{
lean_object* v_res_3605_; 
v_res_3605_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16(v___y_3602_, v___y_3603_);
lean_dec(v___y_3603_);
lean_dec_ref(v___y_3602_);
return v_res_3605_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17(lean_object* v_00_u03b2_3606_, lean_object* v_m_3607_, lean_object* v_a_3608_, lean_object* v_fallback_3609_){
_start:
{
lean_object* v___x_3610_; 
v___x_3610_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_m_3607_, v_a_3608_, v_fallback_3609_);
return v___x_3610_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___boxed(lean_object* v_00_u03b2_3611_, lean_object* v_m_3612_, lean_object* v_a_3613_, lean_object* v_fallback_3614_){
_start:
{
lean_object* v_res_3615_; 
v_res_3615_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17(v_00_u03b2_3611_, v_m_3612_, v_a_3613_, v_fallback_3614_);
lean_dec(v_fallback_3614_);
lean_dec_ref(v_a_3613_);
lean_dec_ref(v_m_3612_);
return v_res_3615_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18(lean_object* v_00_u03b2_3616_, lean_object* v_m_3617_, lean_object* v_a_3618_, lean_object* v_b_3619_){
_start:
{
lean_object* v___x_3620_; 
v___x_3620_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_m_3617_, v_a_3618_, v_b_3619_);
return v___x_3620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21(lean_object* v_n_3621_, lean_object* v_as_3622_, lean_object* v_lo_3623_, lean_object* v_hi_3624_, lean_object* v_w_3625_, lean_object* v_hlo_3626_, lean_object* v_hhi_3627_){
_start:
{
lean_object* v___x_3628_; 
v___x_3628_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_3621_, v_as_3622_, v_lo_3623_, v_hi_3624_);
return v___x_3628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___boxed(lean_object* v_n_3629_, lean_object* v_as_3630_, lean_object* v_lo_3631_, lean_object* v_hi_3632_, lean_object* v_w_3633_, lean_object* v_hlo_3634_, lean_object* v_hhi_3635_){
_start:
{
lean_object* v_res_3636_; 
v_res_3636_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21(v_n_3629_, v_as_3630_, v_lo_3631_, v_hi_3632_, v_w_3633_, v_hlo_3634_, v_hhi_3635_);
lean_dec(v_hi_3632_);
lean_dec(v_n_3629_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21(lean_object* v_00_u03b2_3637_, lean_object* v_a_3638_, lean_object* v_fallback_3639_, lean_object* v_x_3640_){
_start:
{
lean_object* v___x_3641_; 
v___x_3641_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_3638_, v_fallback_3639_, v_x_3640_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___boxed(lean_object* v_00_u03b2_3642_, lean_object* v_a_3643_, lean_object* v_fallback_3644_, lean_object* v_x_3645_){
_start:
{
lean_object* v_res_3646_; 
v_res_3646_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21(v_00_u03b2_3642_, v_a_3643_, v_fallback_3644_, v_x_3645_);
lean_dec(v_x_3645_);
lean_dec(v_fallback_3644_);
lean_dec_ref(v_a_3643_);
return v_res_3646_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23(lean_object* v_00_u03b2_3647_, lean_object* v_a_3648_, lean_object* v_x_3649_){
_start:
{
uint8_t v___x_3650_; 
v___x_3650_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_3648_, v_x_3649_);
return v___x_3650_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___boxed(lean_object* v_00_u03b2_3651_, lean_object* v_a_3652_, lean_object* v_x_3653_){
_start:
{
uint8_t v_res_3654_; lean_object* v_r_3655_; 
v_res_3654_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23(v_00_u03b2_3651_, v_a_3652_, v_x_3653_);
lean_dec(v_x_3653_);
lean_dec_ref(v_a_3652_);
v_r_3655_ = lean_box(v_res_3654_);
return v_r_3655_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24(lean_object* v_00_u03b2_3656_, lean_object* v_data_3657_){
_start:
{
lean_object* v___x_3658_; 
v___x_3658_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(v_data_3657_);
return v___x_3658_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25(lean_object* v_00_u03b2_3659_, lean_object* v_a_3660_, lean_object* v_b_3661_, lean_object* v_x_3662_){
_start:
{
lean_object* v___x_3663_; 
v___x_3663_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_3660_, v_b_3661_, v_x_3662_);
return v___x_3663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31(lean_object* v_n_3664_, lean_object* v_lo_3665_, lean_object* v_hi_3666_, lean_object* v_hhi_3667_, lean_object* v_pivot_3668_, lean_object* v_as_3669_, lean_object* v_i_3670_, lean_object* v_k_3671_, lean_object* v_ilo_3672_, lean_object* v_ik_3673_, lean_object* v_w_3674_){
_start:
{
lean_object* v___x_3675_; 
v___x_3675_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_3666_, v_pivot_3668_, v_as_3669_, v_i_3670_, v_k_3671_);
return v___x_3675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___boxed(lean_object* v_n_3676_, lean_object* v_lo_3677_, lean_object* v_hi_3678_, lean_object* v_hhi_3679_, lean_object* v_pivot_3680_, lean_object* v_as_3681_, lean_object* v_i_3682_, lean_object* v_k_3683_, lean_object* v_ilo_3684_, lean_object* v_ik_3685_, lean_object* v_w_3686_){
_start:
{
lean_object* v_res_3687_; 
v_res_3687_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31(v_n_3676_, v_lo_3677_, v_hi_3678_, v_hhi_3679_, v_pivot_3680_, v_as_3681_, v_i_3682_, v_k_3683_, v_ilo_3684_, v_ik_3685_, v_w_3686_);
lean_dec_ref(v_pivot_3680_);
lean_dec(v_hi_3678_);
lean_dec(v_lo_3677_);
lean_dec(v_n_3676_);
return v_res_3687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40(lean_object* v_as_3688_, size_t v_sz_3689_, size_t v_i_3690_, lean_object* v_b_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_){
_start:
{
lean_object* v___x_3695_; 
v___x_3695_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_3688_, v_sz_3689_, v_i_3690_, v_b_3691_, v___y_3692_);
return v___x_3695_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___boxed(lean_object* v_as_3696_, lean_object* v_sz_3697_, lean_object* v_i_3698_, lean_object* v_b_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_){
_start:
{
size_t v_sz_boxed_3703_; size_t v_i_boxed_3704_; lean_object* v_res_3705_; 
v_sz_boxed_3703_ = lean_unbox_usize(v_sz_3697_);
lean_dec(v_sz_3697_);
v_i_boxed_3704_ = lean_unbox_usize(v_i_3698_);
lean_dec(v_i_3698_);
v_res_3705_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40(v_as_3696_, v_sz_boxed_3703_, v_i_boxed_3704_, v_b_3699_, v___y_3700_, v___y_3701_);
lean_dec(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec_ref(v_as_3696_);
return v_res_3705_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35(lean_object* v_00_u03b2_3706_, lean_object* v_i_3707_, lean_object* v_source_3708_, lean_object* v_target_3709_){
_start:
{
lean_object* v___x_3710_; 
v___x_3710_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(v_i_3707_, v_source_3708_, v_target_3709_);
return v___x_3710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42(uint8_t v___x_3711_, lean_object* v_as_3712_, size_t v_sz_3713_, size_t v_i_3714_, lean_object* v_b_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_){
_start:
{
lean_object* v___x_3719_; 
v___x_3719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_3711_, v_as_3712_, v_sz_3713_, v_i_3714_, v_b_3715_, v___y_3716_);
return v___x_3719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___boxed(lean_object* v___x_3720_, lean_object* v_as_3721_, lean_object* v_sz_3722_, lean_object* v_i_3723_, lean_object* v_b_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_){
_start:
{
uint8_t v___x_40442__boxed_3728_; size_t v_sz_boxed_3729_; size_t v_i_boxed_3730_; lean_object* v_res_3731_; 
v___x_40442__boxed_3728_ = lean_unbox(v___x_3720_);
v_sz_boxed_3729_ = lean_unbox_usize(v_sz_3722_);
lean_dec(v_sz_3722_);
v_i_boxed_3730_ = lean_unbox_usize(v_i_3723_);
lean_dec(v_i_3723_);
v_res_3731_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42(v___x_40442__boxed_3728_, v_as_3721_, v_sz_boxed_3729_, v_i_boxed_3730_, v_b_3724_, v___y_3725_, v___y_3726_);
lean_dec(v___y_3726_);
lean_dec_ref(v___y_3725_);
lean_dec_ref(v_as_3721_);
return v_res_3731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51(lean_object* v_as_3732_, size_t v_sz_3733_, size_t v_i_3734_, lean_object* v_b_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_){
_start:
{
lean_object* v___x_3739_; 
v___x_3739_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_3732_, v_sz_3733_, v_i_3734_, v_b_3735_, v___y_3736_);
return v___x_3739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___boxed(lean_object* v_as_3740_, lean_object* v_sz_3741_, lean_object* v_i_3742_, lean_object* v_b_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
size_t v_sz_boxed_3747_; size_t v_i_boxed_3748_; lean_object* v_res_3749_; 
v_sz_boxed_3747_ = lean_unbox_usize(v_sz_3741_);
lean_dec(v_sz_3741_);
v_i_boxed_3748_ = lean_unbox_usize(v_i_3742_);
lean_dec(v_i_3742_);
v_res_3749_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51(v_as_3740_, v_sz_boxed_3747_, v_i_boxed_3748_, v_b_3743_, v___y_3744_, v___y_3745_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
lean_dec_ref(v_as_3740_);
return v_res_3749_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44(lean_object* v_00_u03b2_3750_, lean_object* v_x_3751_, lean_object* v_x_3752_){
_start:
{
lean_object* v___x_3753_; 
v___x_3753_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(v_x_3751_, v_x_3752_);
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49(uint8_t v___x_3754_, lean_object* v_as_3755_, size_t v_sz_3756_, size_t v_i_3757_, lean_object* v_b_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_){
_start:
{
lean_object* v___x_3762_; 
v___x_3762_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_3754_, v_as_3755_, v_sz_3756_, v_i_3757_, v_b_3758_, v___y_3759_);
return v___x_3762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___boxed(lean_object* v___x_3763_, lean_object* v_as_3764_, lean_object* v_sz_3765_, lean_object* v_i_3766_, lean_object* v_b_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_){
_start:
{
uint8_t v___x_40473__boxed_3771_; size_t v_sz_boxed_3772_; size_t v_i_boxed_3773_; lean_object* v_res_3774_; 
v___x_40473__boxed_3771_ = lean_unbox(v___x_3763_);
v_sz_boxed_3772_ = lean_unbox_usize(v_sz_3765_);
lean_dec(v_sz_3765_);
v_i_boxed_3773_ = lean_unbox_usize(v_i_3766_);
lean_dec(v_i_3766_);
v_res_3774_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49(v___x_40473__boxed_3771_, v_as_3764_, v_sz_boxed_3772_, v_i_boxed_3773_, v_b_3767_, v___y_3768_, v___y_3769_);
lean_dec(v___y_3769_);
lean_dec_ref(v___y_3768_);
lean_dec_ref(v_as_3764_);
return v_res_3774_;
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
