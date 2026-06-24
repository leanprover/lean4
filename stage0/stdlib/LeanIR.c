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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t l_Lean_instDecidableEqOLeanLevel(uint8_t, uint8_t);
lean_object* l_Lean_finalizeImport(lean_object*, lean_object*, lean_object*, uint32_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecls();
lean_object* l_String_Slice_toName(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_setOption(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
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
static lean_once_cell_t l_panic___at___00main_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00main_spec__5___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00main_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00main_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00main_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_main___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_main___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_main___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "internal exception "};
static const lean_object* l_main___lam__1___closed__0 = (const lean_object*)&l_main___lam__1___closed__0_value;
static const lean_string_object l_main___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l_main___lam__1___closed__1 = (const lean_object*)&l_main___lam__1___closed__1_value;
static const lean_string_object l_main___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " (unknown)"};
static const lean_object* l_main___lam__1___closed__2 = (const lean_object*)&l_main___lam__1___closed__2_value;
LEAN_EXPORT lean_object* l_main___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
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
v_val_230_ = lean_string_utf8_extract(v_str_208_, v___x_229_, v_endExclusive_210_);
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
lean_object* v___x_359_; lean_object* v___x_19545__overap_360_; lean_object* v___x_361_; 
v___x_359_ = lean_obj_once(&l_panic___at___00main_spec__5___closed__0, &l_panic___at___00main_spec__5___closed__0_once, _init_l_panic___at___00main_spec__5___closed__0);
v___x_19545__overap_360_ = lean_panic_fn_borrowed(v___x_359_, v_msg_357_);
v___x_361_ = lean_apply_1(v___x_19545__overap_360_, lean_box(0));
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
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0(void){
_start:
{
lean_object* v___x_428_; uint64_t v___x_429_; 
v___x_428_ = lean_unsigned_to_nat(1723u);
v___x_429_ = lean_uint64_of_nat(v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(lean_object* v_m_430_, lean_object* v_a_431_){
_start:
{
lean_object* v_size_432_; lean_object* v_buckets_433_; lean_object* v___x_434_; uint64_t v___y_436_; 
v_size_432_ = lean_ctor_get(v_m_430_, 0);
v_buckets_433_ = lean_ctor_get(v_m_430_, 1);
v___x_434_ = lean_array_get_size(v_buckets_433_);
if (lean_obj_tag(v_a_431_) == 0)
{
uint64_t v___x_463_; 
v___x_463_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0);
v___y_436_ = v___x_463_;
goto v___jp_435_;
}
else
{
uint64_t v_hash_464_; 
v_hash_464_ = lean_ctor_get_uint64(v_a_431_, sizeof(void*)*2);
v___y_436_ = v_hash_464_;
goto v___jp_435_;
}
v___jp_435_:
{
uint64_t v___x_437_; uint64_t v___x_438_; uint64_t v_fold_439_; uint64_t v___x_440_; uint64_t v___x_441_; uint64_t v___x_442_; size_t v___x_443_; size_t v___x_444_; size_t v___x_445_; size_t v___x_446_; size_t v___x_447_; lean_object* v_bucket_448_; uint8_t v___x_449_; 
v___x_437_ = 32ULL;
v___x_438_ = lean_uint64_shift_right(v___y_436_, v___x_437_);
v_fold_439_ = lean_uint64_xor(v___y_436_, v___x_438_);
v___x_440_ = 16ULL;
v___x_441_ = lean_uint64_shift_right(v_fold_439_, v___x_440_);
v___x_442_ = lean_uint64_xor(v_fold_439_, v___x_441_);
v___x_443_ = lean_uint64_to_usize(v___x_442_);
v___x_444_ = lean_usize_of_nat(v___x_434_);
v___x_445_ = ((size_t)1ULL);
v___x_446_ = lean_usize_sub(v___x_444_, v___x_445_);
v___x_447_ = lean_usize_land(v___x_443_, v___x_446_);
v_bucket_448_ = lean_array_uget_borrowed(v_buckets_433_, v___x_447_);
v___x_449_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_a_431_, v_bucket_448_);
if (v___x_449_ == 0)
{
lean_dec(v_a_431_);
return v_m_430_;
}
else
{
lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_460_; 
lean_inc(v_bucket_448_);
lean_inc_ref(v_buckets_433_);
lean_inc(v_size_432_);
v_isSharedCheck_460_ = !lean_is_exclusive(v_m_430_);
if (v_isSharedCheck_460_ == 0)
{
lean_object* v_unused_461_; lean_object* v_unused_462_; 
v_unused_461_ = lean_ctor_get(v_m_430_, 1);
lean_dec(v_unused_461_);
v_unused_462_ = lean_ctor_get(v_m_430_, 0);
lean_dec(v_unused_462_);
v___x_451_ = v_m_430_;
v_isShared_452_ = v_isSharedCheck_460_;
goto v_resetjp_450_;
}
else
{
lean_dec(v_m_430_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_460_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; lean_object* v_buckets_454_; lean_object* v_bucket_455_; lean_object* v___x_456_; lean_object* v___x_458_; 
v___x_453_ = lean_box(0);
v_buckets_454_ = lean_array_uset(v_buckets_433_, v___x_447_, v___x_453_);
v_bucket_455_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(v_a_431_, v_bucket_448_);
v___x_456_ = lean_array_uset(v_buckets_454_, v___x_447_, v_bucket_455_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 1, v___x_456_);
v___x_458_ = v___x_451_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_size_432_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v___x_456_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__0(lean_object* v___x_465_, lean_object* v___x_466_, uint8_t v___x_467_, lean_object* v_importArts_468_, uint8_t v___y_469_, uint8_t v___x_470_, lean_object* v_name_471_, uint8_t v___x_472_, lean_object* v___x_473_, uint8_t v___x_474_){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = lean_st_mk_ref(v___x_465_);
v___x_477_ = l_Lean_importModulesCore(v___x_466_, v___x_467_, v_importArts_468_, v___y_469_, v___x_470_, v___x_476_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v___x_478_; lean_object* v_moduleNameMap_479_; lean_object* v_moduleNames_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_492_; 
lean_dec_ref_known(v___x_477_, 1);
v___x_478_ = lean_st_ref_get(v___x_476_);
lean_dec(v___x_476_);
v_moduleNameMap_479_ = lean_ctor_get(v___x_478_, 0);
v_moduleNames_480_ = lean_ctor_get(v___x_478_, 1);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_492_ == 0)
{
v___x_482_ = v___x_478_;
v_isShared_483_ = v_isSharedCheck_492_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_moduleNames_480_);
lean_inc(v_moduleNameMap_479_);
lean_dec(v___x_478_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_492_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_484_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(v_moduleNameMap_479_, v_name_471_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v___x_484_);
v___x_486_ = v___x_482_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_484_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_moduleNames_480_);
v___x_486_ = v_reuseFailAlloc_491_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
uint32_t v___x_487_; uint8_t v___x_488_; 
v___x_487_ = 0;
v___x_488_ = l_Lean_instDecidableEqOLeanLevel(v___x_467_, v___x_472_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; 
v___x_489_ = l_Lean_finalizeImport(v___x_486_, v___x_466_, v___x_473_, v___x_487_, v___x_470_, v___x_474_, v___x_467_, v___x_470_, v___x_470_);
lean_dec_ref(v___x_486_);
return v___x_489_;
}
else
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_finalizeImport(v___x_486_, v___x_466_, v___x_473_, v___x_487_, v___x_470_, v___x_474_, v___x_467_, v___x_474_, v___x_470_);
lean_dec_ref(v___x_486_);
return v___x_490_;
}
}
}
}
else
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
lean_dec(v___x_476_);
lean_dec_ref(v___x_473_);
lean_dec(v_name_471_);
lean_dec_ref(v___x_466_);
v_a_493_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_500_ == 0)
{
v___x_495_ = v___x_477_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_477_);
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
uint8_t v___x_35661__boxed_512_; uint8_t v___y_35662__boxed_513_; uint8_t v___x_35663__boxed_514_; uint8_t v___x_35664__boxed_515_; uint8_t v___x_35666__boxed_516_; lean_object* v_res_517_; 
v___x_35661__boxed_512_ = lean_unbox(v___x_503_);
v___y_35662__boxed_513_ = lean_unbox(v___y_505_);
v___x_35663__boxed_514_ = lean_unbox(v___x_506_);
v___x_35664__boxed_515_ = lean_unbox(v___x_508_);
v___x_35666__boxed_516_ = lean_unbox(v___x_510_);
v_res_517_ = l_main___lam__0(v___x_501_, v___x_502_, v___x_35661__boxed_512_, v_importArts_504_, v___y_35662__boxed_513_, v___x_35663__boxed_514_, v_name_507_, v___x_35664__boxed_515_, v___x_509_, v___x_35666__boxed_516_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_main___lam__1(lean_object* v___x_521_, lean_object* v___x_522_, lean_object* v___x_523_, lean_object* v_name_524_, lean_object* v_a_525_, uint8_t v___x_526_, lean_object* v___x_527_, lean_object* v_head_528_, lean_object* v___x_529_, lean_object* v___x_530_, lean_object* v___x_531_, lean_object* v___x_532_, lean_object* v___x_533_, lean_object* v___x_534_, lean_object* v___x_535_, lean_object* v___x_536_, uint8_t v___x_537_, uint8_t v___x_538_){
_start:
{
lean_object* v_a_541_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v_env_548_; lean_object* v___x_549_; uint8_t v___x_550_; lean_object* v_fileName_552_; lean_object* v_fileMap_553_; lean_object* v_currRecDepth_554_; lean_object* v_ref_555_; lean_object* v_currNamespace_556_; lean_object* v_openDecls_557_; lean_object* v_initHeartbeats_558_; lean_object* v_maxHeartbeats_559_; lean_object* v_quotContext_560_; lean_object* v_currMacroScope_561_; lean_object* v_cancelTk_x3f_562_; uint8_t v_suppressElabErrors_563_; lean_object* v_inheritedTraceOptions_564_; lean_object* v___y_565_; uint8_t v___y_597_; uint8_t v___x_617_; 
v___x_544_ = lean_io_get_num_heartbeats();
v___x_545_ = lean_st_mk_ref(v___x_521_);
v___x_546_ = lean_st_ref_get(v___x_522_);
v___x_547_ = lean_st_ref_get(v___x_545_);
v_env_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc_ref(v_env_548_);
lean_dec(v___x_547_);
v___x_549_ = l_Lean_diagnostics;
v___x_550_ = l_Lean_Option_get___at___00main_spec__8(v___x_523_, v___x_549_);
v___x_617_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_548_);
lean_dec_ref(v_env_548_);
if (v___x_617_ == 0)
{
if (v___x_550_ == 0)
{
v___y_597_ = v___x_538_;
goto v___jp_596_;
}
else
{
v___y_597_ = v___x_617_;
goto v___jp_596_;
}
}
else
{
v___y_597_ = v___x_550_;
goto v___jp_596_;
}
v___jp_540_:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = lean_mk_io_user_error(v_a_541_);
v___x_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
return v___x_543_;
}
v___jp_551_:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_566_ = l_Lean_maxRecDepth;
v___x_567_ = l_Lean_Option_get___at___00main_spec__9(v___x_523_, v___x_566_);
v___x_568_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_568_, 0, v_fileName_552_);
lean_ctor_set(v___x_568_, 1, v_fileMap_553_);
lean_ctor_set(v___x_568_, 2, v___x_523_);
lean_ctor_set(v___x_568_, 3, v_currRecDepth_554_);
lean_ctor_set(v___x_568_, 4, v___x_567_);
lean_ctor_set(v___x_568_, 5, v_ref_555_);
lean_ctor_set(v___x_568_, 6, v_currNamespace_556_);
lean_ctor_set(v___x_568_, 7, v_openDecls_557_);
lean_ctor_set(v___x_568_, 8, v_initHeartbeats_558_);
lean_ctor_set(v___x_568_, 9, v_maxHeartbeats_559_);
lean_ctor_set(v___x_568_, 10, v_quotContext_560_);
lean_ctor_set(v___x_568_, 11, v_currMacroScope_561_);
lean_ctor_set(v___x_568_, 12, v_cancelTk_x3f_562_);
lean_ctor_set(v___x_568_, 13, v_inheritedTraceOptions_564_);
lean_ctor_set_uint8(v___x_568_, sizeof(void*)*14, v___x_550_);
lean_ctor_set_uint8(v___x_568_, sizeof(void*)*14 + 1, v_suppressElabErrors_563_);
v___x_569_ = l_Lean_Compiler_LCNF_emitC(v_name_524_, v___x_568_, v___y_565_);
lean_dec(v___y_565_);
lean_dec_ref_known(v___x_568_, 14);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_a_570_);
lean_dec_ref_known(v___x_569_, 1);
v___x_571_ = lean_st_ref_get(v___x_545_);
lean_dec(v___x_545_);
lean_dec(v___x_571_);
v___x_572_ = lean_string_to_utf8(v_a_570_);
lean_dec(v_a_570_);
v___x_573_ = lean_io_prim_handle_write(v_a_525_, v___x_572_);
lean_dec_ref(v___x_572_);
return v___x_573_;
}
else
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_595_; 
lean_dec(v___x_545_);
v_a_574_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_595_ == 0)
{
v___x_576_ = v___x_569_;
v_isShared_577_ = v_isSharedCheck_595_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_569_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_595_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
if (lean_obj_tag(v_a_574_) == 0)
{
lean_object* v_msg_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_582_; 
v_msg_578_ = lean_ctor_get(v_a_574_, 1);
lean_inc_ref(v_msg_578_);
lean_dec_ref_known(v_a_574_, 2);
v___x_579_ = l_Lean_MessageData_toString(v_msg_578_);
v___x_580_ = lean_mk_io_user_error(v___x_579_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 0, v___x_580_);
v___x_582_ = v___x_576_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_580_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
else
{
lean_object* v_id_584_; lean_object* v___x_585_; 
lean_del_object(v___x_576_);
v_id_584_ = lean_ctor_get(v_a_574_, 0);
lean_inc(v_id_584_);
lean_dec_ref_known(v_a_574_, 2);
v___x_585_ = l_Lean_InternalExceptionId_getName(v_id_584_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
lean_dec(v_id_584_);
v_a_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_a_586_);
lean_dec_ref_known(v___x_585_, 1);
v___x_587_ = ((lean_object*)(l_main___lam__1___closed__0));
v___x_588_ = l_Lean_Name_toString(v_a_586_, v___x_526_);
v___x_589_ = lean_string_append(v___x_587_, v___x_588_);
lean_dec_ref(v___x_588_);
v_a_541_ = v___x_589_;
goto v___jp_540_;
}
else
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
lean_dec_ref_known(v___x_585_, 1);
v___x_590_ = ((lean_object*)(l_main___lam__1___closed__1));
v___x_591_ = l_Nat_reprFast(v_id_584_);
v___x_592_ = lean_string_append(v___x_590_, v___x_591_);
lean_dec_ref(v___x_591_);
v___x_593_ = ((lean_object*)(l_main___lam__1___closed__2));
v___x_594_ = lean_string_append(v___x_592_, v___x_593_);
v_a_541_ = v___x_594_;
goto v___jp_540_;
}
}
}
}
}
v___jp_596_:
{
if (v___y_597_ == 0)
{
lean_object* v___x_598_; lean_object* v_env_599_; lean_object* v_nextMacroScope_600_; lean_object* v_ngen_601_; lean_object* v_auxDeclNGen_602_; lean_object* v_traceState_603_; lean_object* v_messages_604_; lean_object* v_infoState_605_; lean_object* v_snapshotTasks_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_615_; 
v___x_598_ = lean_st_ref_take(v___x_545_);
v_env_599_ = lean_ctor_get(v___x_598_, 0);
v_nextMacroScope_600_ = lean_ctor_get(v___x_598_, 1);
v_ngen_601_ = lean_ctor_get(v___x_598_, 2);
v_auxDeclNGen_602_ = lean_ctor_get(v___x_598_, 3);
v_traceState_603_ = lean_ctor_get(v___x_598_, 4);
v_messages_604_ = lean_ctor_get(v___x_598_, 6);
v_infoState_605_ = lean_ctor_get(v___x_598_, 7);
v_snapshotTasks_606_ = lean_ctor_get(v___x_598_, 8);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; 
v_unused_616_ = lean_ctor_get(v___x_598_, 5);
lean_dec(v_unused_616_);
v___x_608_ = v___x_598_;
v_isShared_609_ = v_isSharedCheck_615_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_snapshotTasks_606_);
lean_inc(v_infoState_605_);
lean_inc(v_messages_604_);
lean_inc(v_traceState_603_);
lean_inc(v_auxDeclNGen_602_);
lean_inc(v_ngen_601_);
lean_inc(v_nextMacroScope_600_);
lean_inc(v_env_599_);
lean_dec(v___x_598_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_615_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; lean_object* v___x_612_; 
v___x_610_ = l_Lean_Kernel_enableDiag(v_env_599_, v___x_550_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 5, v___x_527_);
lean_ctor_set(v___x_608_, 0, v___x_610_);
v___x_612_ = v___x_608_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_610_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_nextMacroScope_600_);
lean_ctor_set(v_reuseFailAlloc_614_, 2, v_ngen_601_);
lean_ctor_set(v_reuseFailAlloc_614_, 3, v_auxDeclNGen_602_);
lean_ctor_set(v_reuseFailAlloc_614_, 4, v_traceState_603_);
lean_ctor_set(v_reuseFailAlloc_614_, 5, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_614_, 6, v_messages_604_);
lean_ctor_set(v_reuseFailAlloc_614_, 7, v_infoState_605_);
lean_ctor_set(v_reuseFailAlloc_614_, 8, v_snapshotTasks_606_);
v___x_612_ = v_reuseFailAlloc_614_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
lean_object* v___x_613_; 
v___x_613_ = lean_st_ref_set(v___x_545_, v___x_612_);
lean_inc(v___x_545_);
lean_inc(v___x_532_);
v_fileName_552_ = v_head_528_;
v_fileMap_553_ = v___x_529_;
v_currRecDepth_554_ = v___x_530_;
v_ref_555_ = v___x_531_;
v_currNamespace_556_ = v___x_532_;
v_openDecls_557_ = v___x_533_;
v_initHeartbeats_558_ = v___x_544_;
v_maxHeartbeats_559_ = v___x_534_;
v_quotContext_560_ = v___x_532_;
v_currMacroScope_561_ = v___x_535_;
v_cancelTk_x3f_562_ = v___x_536_;
v_suppressElabErrors_563_ = v___x_537_;
v_inheritedTraceOptions_564_ = v___x_546_;
v___y_565_ = v___x_545_;
goto v___jp_551_;
}
}
}
else
{
lean_dec_ref(v___x_527_);
lean_inc(v___x_545_);
lean_inc(v___x_532_);
v_fileName_552_ = v_head_528_;
v_fileMap_553_ = v___x_529_;
v_currRecDepth_554_ = v___x_530_;
v_ref_555_ = v___x_531_;
v_currNamespace_556_ = v___x_532_;
v_openDecls_557_ = v___x_533_;
v_initHeartbeats_558_ = v___x_544_;
v_maxHeartbeats_559_ = v___x_534_;
v_quotContext_560_ = v___x_532_;
v_currMacroScope_561_ = v___x_535_;
v_cancelTk_x3f_562_ = v___x_536_;
v_suppressElabErrors_563_ = v___x_537_;
v_inheritedTraceOptions_564_ = v___x_546_;
v___y_565_ = v___x_545_;
goto v___jp_551_;
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__1___boxed(lean_object** _args){
lean_object* v___x_618_ = _args[0];
lean_object* v___x_619_ = _args[1];
lean_object* v___x_620_ = _args[2];
lean_object* v_name_621_ = _args[3];
lean_object* v_a_622_ = _args[4];
lean_object* v___x_623_ = _args[5];
lean_object* v___x_624_ = _args[6];
lean_object* v_head_625_ = _args[7];
lean_object* v___x_626_ = _args[8];
lean_object* v___x_627_ = _args[9];
lean_object* v___x_628_ = _args[10];
lean_object* v___x_629_ = _args[11];
lean_object* v___x_630_ = _args[12];
lean_object* v___x_631_ = _args[13];
lean_object* v___x_632_ = _args[14];
lean_object* v___x_633_ = _args[15];
lean_object* v___x_634_ = _args[16];
lean_object* v___x_635_ = _args[17];
lean_object* v___y_636_ = _args[18];
_start:
{
uint8_t v___x_35743__boxed_637_; uint8_t v___x_35754__boxed_638_; uint8_t v___x_35755__boxed_639_; lean_object* v_res_640_; 
v___x_35743__boxed_637_ = lean_unbox(v___x_623_);
v___x_35754__boxed_638_ = lean_unbox(v___x_634_);
v___x_35755__boxed_639_ = lean_unbox(v___x_635_);
v_res_640_ = l_main___lam__1(v___x_618_, v___x_619_, v___x_620_, v_name_621_, v_a_622_, v___x_35743__boxed_637_, v___x_624_, v_head_625_, v___x_626_, v___x_627_, v___x_628_, v___x_629_, v___x_630_, v___x_631_, v___x_632_, v___x_633_, v___x_35754__boxed_638_, v___x_35755__boxed_639_);
lean_dec(v_a_622_);
lean_dec(v___x_619_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(lean_object* v_s_641_){
_start:
{
lean_object* v___x_643_; lean_object* v_putStr_644_; lean_object* v___x_645_; 
v___x_643_ = lean_get_stderr();
v_putStr_644_ = lean_ctor_get(v___x_643_, 4);
lean_inc_ref(v_putStr_644_);
lean_dec_ref(v___x_643_);
v___x_645_ = lean_apply_2(v_putStr_644_, v_s_641_, lean_box(0));
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8___boxed(lean_object* v_s_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v_s_646_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6(lean_object* v_s_649_){
_start:
{
uint32_t v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_651_ = 10;
v___x_652_ = lean_string_push(v_s_649_, v___x_651_);
v___x_653_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v___x_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6___boxed(lean_object* v_s_654_, lean_object* v_a_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_IO_eprintln___at___00main_spec__6(v_s_654_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(lean_object* v_o_660_, lean_object* v_k_661_, lean_object* v_v_662_){
_start:
{
lean_object* v_map_663_; uint8_t v_hasTrace_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_678_; 
v_map_663_ = lean_ctor_get(v_o_660_, 0);
v_hasTrace_664_ = lean_ctor_get_uint8(v_o_660_, sizeof(void*)*1);
v_isSharedCheck_678_ = !lean_is_exclusive(v_o_660_);
if (v_isSharedCheck_678_ == 0)
{
v___x_666_ = v_o_660_;
v_isShared_667_ = v_isSharedCheck_678_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_map_663_);
lean_dec(v_o_660_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_678_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_668_, 0, v_v_662_);
lean_inc(v_k_661_);
v___x_669_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_661_, v___x_668_, v_map_663_);
if (v_hasTrace_664_ == 0)
{
lean_object* v___x_670_; uint8_t v___x_671_; lean_object* v___x_673_; 
v___x_670_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_671_ = l_Lean_Name_isPrefixOf(v___x_670_, v_k_661_);
lean_dec(v_k_661_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_669_);
v___x_673_ = v___x_666_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_669_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
lean_ctor_set_uint8(v___x_673_, sizeof(void*)*1, v___x_671_);
return v___x_673_;
}
}
else
{
lean_object* v___x_676_; 
lean_dec(v_k_661_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_669_);
v___x_676_ = v___x_666_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_669_);
lean_ctor_set_uint8(v_reuseFailAlloc_677_, sizeof(void*)*1, v_hasTrace_664_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00main_spec__3(lean_object* v_opts_679_, lean_object* v_opt_680_, lean_object* v_val_681_){
_start:
{
lean_object* v_name_682_; lean_object* v___x_683_; 
v_name_682_ = lean_ctor_get(v_opt_680_, 0);
lean_inc(v_name_682_);
lean_dec_ref(v_opt_680_);
v___x_683_ = l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(v_opts_679_, v_name_682_, v_val_681_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(lean_object* v___y_685_, lean_object* v_as_686_, size_t v_i_687_, size_t v_stop_688_, lean_object* v_b_689_){
_start:
{
lean_object* v___y_691_; uint8_t v___x_695_; 
v___x_695_ = lean_usize_dec_eq(v_i_687_, v_stop_688_);
if (v___x_695_ == 0)
{
lean_object* v_fst_696_; lean_object* v_snd_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___y_701_; 
v_fst_696_ = lean_ctor_get(v_b_689_, 0);
v_snd_697_ = lean_ctor_get(v_b_689_, 1);
v___x_698_ = lean_array_uget_borrowed(v_as_686_, v_i_687_);
v___x_699_ = l_Lean_IR_Decl_name(v___x_698_);
if (lean_obj_tag(v___x_699_) == 1)
{
lean_object* v_pre_714_; lean_object* v_str_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v_pre_714_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_pre_714_);
v_str_715_ = lean_ctor_get(v___x_699_, 1);
lean_inc_ref(v_str_715_);
v___x_716_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___closed__0));
v___x_717_ = lean_string_dec_eq(v_str_715_, v___x_716_);
lean_dec_ref(v_str_715_);
if (v___x_717_ == 0)
{
lean_dec(v_pre_714_);
lean_inc_ref(v___x_699_);
v___y_701_ = v___x_699_;
goto v___jp_700_;
}
else
{
v___y_701_ = v_pre_714_;
goto v___jp_700_;
}
}
else
{
lean_inc(v___x_699_);
v___y_701_ = v___x_699_;
goto v___jp_700_;
}
v___jp_700_:
{
uint8_t v___x_702_; 
lean_inc_ref(v___y_685_);
v___x_702_ = l_Lean_isExtern(v___y_685_, v___y_701_);
if (v___x_702_ == 0)
{
lean_dec(v___x_699_);
v___y_691_ = v_b_689_;
goto v___jp_690_;
}
else
{
lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_711_; 
lean_inc(v_snd_697_);
lean_inc(v_fst_696_);
v_isSharedCheck_711_ = !lean_is_exclusive(v_b_689_);
if (v_isSharedCheck_711_ == 0)
{
lean_object* v_unused_712_; lean_object* v_unused_713_; 
v_unused_712_ = lean_ctor_get(v_b_689_, 1);
lean_dec(v_unused_712_);
v_unused_713_ = lean_ctor_get(v_b_689_, 0);
lean_dec(v_unused_713_);
v___x_704_ = v_b_689_;
v_isShared_705_ = v_isSharedCheck_711_;
goto v_resetjp_703_;
}
else
{
lean_dec(v_b_689_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_711_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_709_; 
lean_inc_n(v___x_698_, 2);
v___x_706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_698_);
lean_ctor_set(v___x_706_, 1, v_fst_696_);
v___x_707_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(v_snd_697_, v___x_699_, v___x_698_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 1, v___x_707_);
lean_ctor_set(v___x_704_, 0, v___x_706_);
v___x_709_ = v___x_704_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_706_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v___x_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
v___y_691_ = v___x_709_;
goto v___jp_690_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_685_);
return v_b_689_;
}
v___jp_690_:
{
size_t v___x_692_; size_t v___x_693_; 
v___x_692_ = ((size_t)1ULL);
v___x_693_ = lean_usize_add(v_i_687_, v___x_692_);
v_i_687_ = v___x_693_;
v_b_689_ = v___y_691_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___boxed(lean_object* v___y_718_, lean_object* v_as_719_, lean_object* v_i_720_, lean_object* v_stop_721_, lean_object* v_b_722_){
_start:
{
size_t v_i_boxed_723_; size_t v_stop_boxed_724_; lean_object* v_res_725_; 
v_i_boxed_723_ = lean_unbox_usize(v_i_720_);
lean_dec(v_i_720_);
v_stop_boxed_724_ = lean_unbox_usize(v_stop_721_);
lean_dec(v_stop_721_);
v_res_725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_718_, v_as_719_, v_i_boxed_723_, v_stop_boxed_724_, v_b_722_);
lean_dec_ref(v_as_719_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg(lean_object* v_as_x27_727_, lean_object* v_b_728_){
_start:
{
if (lean_obj_tag(v_as_x27_727_) == 0)
{
lean_object* v___x_730_; 
v___x_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_730_, 0, v_b_728_);
return v___x_730_;
}
else
{
lean_object* v_head_731_; lean_object* v_tail_732_; lean_object* v_fst_733_; lean_object* v_snd_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_759_; 
v_head_731_ = lean_ctor_get(v_as_x27_727_, 0);
v_tail_732_ = lean_ctor_get(v_as_x27_727_, 1);
v_fst_733_ = lean_ctor_get(v_b_728_, 0);
v_snd_734_ = lean_ctor_get(v_b_728_, 1);
v_isSharedCheck_759_ = !lean_is_exclusive(v_b_728_);
if (v_isSharedCheck_759_ == 0)
{
v___x_736_ = v_b_728_;
v_isShared_737_ = v_isSharedCheck_759_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_snd_734_);
lean_inc(v_fst_733_);
lean_dec(v_b_728_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_759_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_738_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0));
v___x_739_ = lean_string_dec_eq(v_head_731_, v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; 
lean_inc(v_head_731_);
v___x_740_ = l___private_LeanIR_0__setConfigOption(v_snd_734_, v_head_731_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; lean_object* v___x_743_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_a_741_);
lean_dec_ref_known(v___x_740_, 1);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 1, v_a_741_);
v___x_743_ = v___x_736_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_fst_733_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_a_741_);
v___x_743_ = v_reuseFailAlloc_745_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
v_as_x27_727_ = v_tail_732_;
v_b_728_ = v___x_743_;
goto _start;
}
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
lean_del_object(v___x_736_);
lean_dec(v_fst_733_);
v_a_746_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_740_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_740_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
else
{
lean_object* v___x_754_; lean_object* v___x_756_; 
lean_dec(v_fst_733_);
v___x_754_ = lean_box(v___x_739_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v___x_754_);
v___x_756_ = v___x_736_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_snd_734_);
v___x_756_ = v_reuseFailAlloc_758_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
v_as_x27_727_ = v_tail_732_;
v_b_728_ = v___x_756_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg___boxed(lean_object* v_as_x27_760_, lean_object* v_b_761_, lean_object* v___y_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_760_, v_b_761_);
lean_dec(v_as_x27_760_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(lean_object* v_as_764_, size_t v_i_765_, size_t v_stop_766_, lean_object* v_b_767_){
_start:
{
uint8_t v___x_768_; 
v___x_768_ = lean_usize_dec_eq(v_i_765_, v_stop_766_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; lean_object* v_toEnvExtension_770_; lean_object* v_asyncMode_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; size_t v___x_775_; size_t v___x_776_; 
v___x_769_ = l_Lean_Compiler_LCNF_impureSigExt;
v_toEnvExtension_770_ = lean_ctor_get(v___x_769_, 0);
v_asyncMode_771_ = lean_ctor_get(v_toEnvExtension_770_, 2);
v___x_772_ = lean_box(0);
v___x_773_ = lean_array_uget_borrowed(v_as_764_, v_i_765_);
lean_inc(v___x_773_);
v___x_774_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_769_, v_b_767_, v___x_773_, v_asyncMode_771_, v___x_772_);
v___x_775_ = ((size_t)1ULL);
v___x_776_ = lean_usize_add(v_i_765_, v___x_775_);
v_i_765_ = v___x_776_;
v_b_767_ = v___x_774_;
goto _start;
}
else
{
return v_b_767_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18___boxed(lean_object* v_as_778_, lean_object* v_i_779_, lean_object* v_stop_780_, lean_object* v_b_781_){
_start:
{
size_t v_i_boxed_782_; size_t v_stop_boxed_783_; lean_object* v_res_784_; 
v_i_boxed_782_ = lean_unbox_usize(v_i_779_);
lean_dec(v_i_779_);
v_stop_boxed_783_ = lean_unbox_usize(v_stop_780_);
lean_dec(v_stop_780_);
v_res_784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_as_778_, v_i_boxed_782_, v_stop_boxed_783_, v_b_781_);
lean_dec_ref(v_as_778_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(lean_object* v_as_788_, size_t v_sz_789_, size_t v_i_790_, lean_object* v_b_791_, lean_object* v___y_792_){
_start:
{
uint8_t v___x_794_; 
v___x_794_ = lean_usize_dec_lt(v_i_790_, v_sz_789_);
if (v___x_794_ == 0)
{
lean_object* v___x_795_; 
v___x_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_795_, 0, v_b_791_);
return v___x_795_;
}
else
{
uint8_t v___x_796_; lean_object* v_a_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
lean_dec_ref(v_b_791_);
v___x_796_ = 0;
v_a_797_ = lean_array_uget_borrowed(v_as_788_, v_i_790_);
lean_inc(v_a_797_);
v___x_798_ = l_Lean_Message_toString(v_a_797_, v___x_796_);
v___x_799_ = l_IO_eprintln___at___00main_spec__6(v___x_798_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v___x_800_; size_t v___x_801_; size_t v___x_802_; 
lean_dec_ref_known(v___x_799_, 1);
v___x_800_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_801_ = ((size_t)1ULL);
v___x_802_ = lean_usize_add(v_i_790_, v___x_801_);
v_i_790_ = v___x_802_;
v_b_791_ = v___x_800_;
goto _start;
}
else
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_816_; 
v_a_804_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_816_ == 0)
{
v___x_806_ = v___x_799_;
v_isShared_807_ = v_isSharedCheck_816_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_799_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_816_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v_ref_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_814_; 
v_ref_808_ = lean_ctor_get(v___y_792_, 5);
v___x_809_ = lean_io_error_to_string(v_a_804_);
v___x_810_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
v___x_811_ = l_Lean_MessageData_ofFormat(v___x_810_);
lean_inc(v_ref_808_);
v___x_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_812_, 0, v_ref_808_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 0, v___x_812_);
v___x_814_ = v___x_806_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_812_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___boxed(lean_object* v_as_817_, lean_object* v_sz_818_, lean_object* v_i_819_, lean_object* v_b_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
size_t v_sz_boxed_823_; size_t v_i_boxed_824_; lean_object* v_res_825_; 
v_sz_boxed_823_ = lean_unbox_usize(v_sz_818_);
lean_dec(v_sz_818_);
v_i_boxed_824_ = lean_unbox_usize(v_i_819_);
lean_dec(v_i_819_);
v_res_825_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_817_, v_sz_boxed_823_, v_i_boxed_824_, v_b_820_, v___y_821_);
lean_dec_ref(v___y_821_);
lean_dec_ref(v_as_817_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(lean_object* v_as_826_, size_t v_sz_827_, size_t v_i_828_, lean_object* v_b_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
uint8_t v___x_833_; 
v___x_833_ = lean_usize_dec_lt(v_i_828_, v_sz_827_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; 
v___x_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_834_, 0, v_b_829_);
return v___x_834_;
}
else
{
uint8_t v___x_835_; lean_object* v_a_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
lean_dec_ref(v_b_829_);
v___x_835_ = 0;
v_a_836_ = lean_array_uget_borrowed(v_as_826_, v_i_828_);
lean_inc(v_a_836_);
v___x_837_ = l_Lean_Message_toString(v_a_836_, v___x_835_);
v___x_838_ = l_IO_eprintln___at___00main_spec__6(v___x_837_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v___x_839_; size_t v___x_840_; size_t v___x_841_; lean_object* v___x_842_; 
lean_dec_ref_known(v___x_838_, 1);
v___x_839_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_840_ = ((size_t)1ULL);
v___x_841_ = lean_usize_add(v_i_828_, v___x_840_);
v___x_842_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_826_, v_sz_827_, v___x_841_, v___x_839_, v___y_830_);
return v___x_842_;
}
else
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_855_; 
v_a_843_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_855_ == 0)
{
v___x_845_ = v___x_838_;
v_isShared_846_ = v_isSharedCheck_855_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_838_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_855_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v_ref_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_853_; 
v_ref_847_ = lean_ctor_get(v___y_830_, 5);
v___x_848_ = lean_io_error_to_string(v_a_843_);
v___x_849_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
v___x_850_ = l_Lean_MessageData_ofFormat(v___x_849_);
lean_inc(v_ref_847_);
v___x_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_851_, 0, v_ref_847_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v___x_851_);
v___x_853_ = v___x_845_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_851_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27___boxed(lean_object* v_as_856_, lean_object* v_sz_857_, lean_object* v_i_858_, lean_object* v_b_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
size_t v_sz_boxed_863_; size_t v_i_boxed_864_; lean_object* v_res_865_; 
v_sz_boxed_863_ = lean_unbox_usize(v_sz_857_);
lean_dec(v_sz_857_);
v_i_boxed_864_ = lean_unbox_usize(v_i_858_);
lean_dec(v_i_858_);
v_res_865_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(v_as_856_, v_sz_boxed_863_, v_i_boxed_864_, v_b_859_, v___y_860_, v___y_861_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec_ref(v_as_856_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(lean_object* v_as_869_, size_t v_sz_870_, size_t v_i_871_, lean_object* v_b_872_, lean_object* v___y_873_){
_start:
{
uint8_t v___x_875_; 
v___x_875_ = lean_usize_dec_lt(v_i_871_, v_sz_870_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; 
v___x_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_876_, 0, v_b_872_);
return v___x_876_;
}
else
{
uint8_t v___x_877_; lean_object* v_a_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
lean_dec_ref(v_b_872_);
v___x_877_ = 0;
v_a_878_ = lean_array_uget_borrowed(v_as_869_, v_i_871_);
lean_inc(v_a_878_);
v___x_879_ = l_Lean_Message_toString(v_a_878_, v___x_877_);
v___x_880_ = l_IO_eprintln___at___00main_spec__6(v___x_879_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v___x_881_; size_t v___x_882_; size_t v___x_883_; 
lean_dec_ref_known(v___x_880_, 1);
v___x_881_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_882_ = ((size_t)1ULL);
v___x_883_ = lean_usize_add(v_i_871_, v___x_882_);
v_i_871_ = v___x_883_;
v_b_872_ = v___x_881_;
goto _start;
}
else
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_897_; 
v_a_885_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_897_ == 0)
{
v___x_887_ = v___x_880_;
v_isShared_888_ = v_isSharedCheck_897_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_880_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_897_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v_ref_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_895_; 
v_ref_889_ = lean_ctor_get(v___y_873_, 5);
v___x_890_ = lean_io_error_to_string(v_a_885_);
v___x_891_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
v___x_892_ = l_Lean_MessageData_ofFormat(v___x_891_);
lean_inc(v_ref_889_);
v___x_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_893_, 0, v_ref_889_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v___x_893_);
v___x_895_ = v___x_887_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_893_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___boxed(lean_object* v_as_898_, lean_object* v_sz_899_, lean_object* v_i_900_, lean_object* v_b_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
size_t v_sz_boxed_904_; size_t v_i_boxed_905_; lean_object* v_res_906_; 
v_sz_boxed_904_ = lean_unbox_usize(v_sz_899_);
lean_dec(v_sz_899_);
v_i_boxed_905_ = lean_unbox_usize(v_i_900_);
lean_dec(v_i_900_);
v_res_906_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_898_, v_sz_boxed_904_, v_i_boxed_905_, v_b_901_, v___y_902_);
lean_dec_ref(v___y_902_);
lean_dec_ref(v_as_898_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(lean_object* v_as_907_, size_t v_sz_908_, size_t v_i_909_, lean_object* v_b_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
uint8_t v___x_914_; 
v___x_914_ = lean_usize_dec_lt(v_i_909_, v_sz_908_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; 
v___x_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_915_, 0, v_b_910_);
return v___x_915_;
}
else
{
uint8_t v___x_916_; lean_object* v_a_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
lean_dec_ref(v_b_910_);
v___x_916_ = 0;
v_a_917_ = lean_array_uget_borrowed(v_as_907_, v_i_909_);
lean_inc(v_a_917_);
v___x_918_ = l_Lean_Message_toString(v_a_917_, v___x_916_);
v___x_919_ = l_IO_eprintln___at___00main_spec__6(v___x_918_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v___x_920_; size_t v___x_921_; size_t v___x_922_; lean_object* v___x_923_; 
lean_dec_ref_known(v___x_919_, 1);
v___x_920_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_921_ = ((size_t)1ULL);
v___x_922_ = lean_usize_add(v_i_909_, v___x_921_);
v___x_923_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_907_, v_sz_908_, v___x_922_, v___x_920_, v___y_911_);
return v___x_923_;
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_936_; 
v_a_924_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_936_ == 0)
{
v___x_926_ = v___x_919_;
v_isShared_927_ = v_isSharedCheck_936_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_919_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_936_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v_ref_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_934_; 
v_ref_928_ = lean_ctor_get(v___y_911_, 5);
v___x_929_ = lean_io_error_to_string(v_a_924_);
v___x_930_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
v___x_931_ = l_Lean_MessageData_ofFormat(v___x_930_);
lean_inc(v_ref_928_);
v___x_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_932_, 0, v_ref_928_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 0, v___x_932_);
v___x_934_ = v___x_926_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_932_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38___boxed(lean_object* v_as_937_, lean_object* v_sz_938_, lean_object* v_i_939_, lean_object* v_b_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
size_t v_sz_boxed_944_; size_t v_i_boxed_945_; lean_object* v_res_946_; 
v_sz_boxed_944_ = lean_unbox_usize(v_sz_938_);
lean_dec(v_sz_938_);
v_i_boxed_945_ = lean_unbox_usize(v_i_939_);
lean_dec(v_i_939_);
v_res_946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(v_as_937_, v_sz_boxed_944_, v_i_boxed_945_, v_b_940_, v___y_941_, v___y_942_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec_ref(v_as_937_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(lean_object* v_init_947_, lean_object* v_n_948_, lean_object* v_b_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
if (lean_obj_tag(v_n_948_) == 0)
{
lean_object* v_cs_953_; lean_object* v___x_954_; lean_object* v___x_955_; size_t v_sz_956_; size_t v___x_957_; lean_object* v___x_958_; 
v_cs_953_ = lean_ctor_get(v_n_948_, 0);
v___x_954_ = lean_box(0);
v___x_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
lean_ctor_set(v___x_955_, 1, v_b_949_);
v_sz_956_ = lean_array_size(v_cs_953_);
v___x_957_ = ((size_t)0ULL);
v___x_958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(v_init_947_, v_cs_953_, v_sz_956_, v___x_957_, v___x_955_, v___y_950_, v___y_951_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_973_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_973_ == 0)
{
v___x_961_ = v___x_958_;
v_isShared_962_ = v_isSharedCheck_973_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_958_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_973_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v_fst_963_; 
v_fst_963_ = lean_ctor_get(v_a_959_, 0);
if (lean_obj_tag(v_fst_963_) == 0)
{
lean_object* v_snd_964_; lean_object* v___x_965_; lean_object* v___x_967_; 
v_snd_964_ = lean_ctor_get(v_a_959_, 1);
lean_inc(v_snd_964_);
lean_dec(v_a_959_);
v___x_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_965_, 0, v_snd_964_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 0, v___x_965_);
v___x_967_ = v___x_961_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_965_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
else
{
lean_object* v_val_969_; lean_object* v___x_971_; 
lean_inc_ref(v_fst_963_);
lean_dec(v_a_959_);
v_val_969_ = lean_ctor_get(v_fst_963_, 0);
lean_inc(v_val_969_);
lean_dec_ref_known(v_fst_963_, 1);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 0, v_val_969_);
v___x_971_ = v___x_961_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_val_969_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
else
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
v_a_974_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_958_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_958_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
else
{
lean_object* v_vs_982_; lean_object* v___x_983_; lean_object* v___x_984_; size_t v_sz_985_; size_t v___x_986_; lean_object* v___x_987_; 
v_vs_982_ = lean_ctor_get(v_n_948_, 0);
v___x_983_ = lean_box(0);
v___x_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
lean_ctor_set(v___x_984_, 1, v_b_949_);
v_sz_985_ = lean_array_size(v_vs_982_);
v___x_986_ = ((size_t)0ULL);
v___x_987_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(v_vs_982_, v_sz_985_, v___x_986_, v___x_984_, v___y_950_, v___y_951_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_1002_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_990_ = v___x_987_;
v_isShared_991_ = v_isSharedCheck_1002_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_987_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_1002_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v_fst_992_; 
v_fst_992_ = lean_ctor_get(v_a_988_, 0);
if (lean_obj_tag(v_fst_992_) == 0)
{
lean_object* v_snd_993_; lean_object* v___x_994_; lean_object* v___x_996_; 
v_snd_993_ = lean_ctor_get(v_a_988_, 1);
lean_inc(v_snd_993_);
lean_dec(v_a_988_);
v___x_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_994_, 0, v_snd_993_);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 0, v___x_994_);
v___x_996_ = v___x_990_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_994_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
else
{
lean_object* v_val_998_; lean_object* v___x_1000_; 
lean_inc_ref(v_fst_992_);
lean_dec(v_a_988_);
v_val_998_ = lean_ctor_get(v_fst_992_, 0);
lean_inc(v_val_998_);
lean_dec_ref_known(v_fst_992_, 1);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 0, v_val_998_);
v___x_1000_ = v___x_990_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_val_998_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
v_a_1003_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_987_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_987_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(lean_object* v_init_1011_, lean_object* v_as_1012_, size_t v_sz_1013_, size_t v_i_1014_, lean_object* v_b_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
uint8_t v___x_1019_; 
v___x_1019_ = lean_usize_dec_lt(v_i_1014_, v_sz_1013_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; 
v___x_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1020_, 0, v_b_1015_);
return v___x_1020_;
}
else
{
lean_object* v_snd_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1055_; 
v_snd_1021_ = lean_ctor_get(v_b_1015_, 1);
v_isSharedCheck_1055_ = !lean_is_exclusive(v_b_1015_);
if (v_isSharedCheck_1055_ == 0)
{
lean_object* v_unused_1056_; 
v_unused_1056_ = lean_ctor_get(v_b_1015_, 0);
lean_dec(v_unused_1056_);
v___x_1023_ = v_b_1015_;
v_isShared_1024_ = v_isSharedCheck_1055_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_snd_1021_);
lean_dec(v_b_1015_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1055_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v_a_1025_; lean_object* v___x_1026_; 
v_a_1025_ = lean_array_uget_borrowed(v_as_1012_, v_i_1014_);
lean_inc(v_snd_1021_);
v___x_1026_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_1011_, v_a_1025_, v_snd_1021_, v___y_1016_, v___y_1017_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1046_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1029_ = v___x_1026_;
v_isShared_1030_ = v_isSharedCheck_1046_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1026_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1046_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
if (lean_obj_tag(v_a_1027_) == 0)
{
lean_object* v___x_1031_; lean_object* v___x_1033_; 
v___x_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1031_, 0, v_a_1027_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v___x_1031_);
v___x_1033_ = v___x_1023_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1031_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v_snd_1021_);
v___x_1033_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
lean_object* v___x_1035_; 
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v___x_1033_);
v___x_1035_ = v___x_1029_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1033_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1039_; lean_object* v___x_1041_; 
lean_del_object(v___x_1029_);
lean_dec(v_snd_1021_);
v_a_1038_ = lean_ctor_get(v_a_1027_, 0);
lean_inc(v_a_1038_);
lean_dec_ref_known(v_a_1027_, 1);
v___x_1039_ = lean_box(0);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 1, v_a_1038_);
lean_ctor_set(v___x_1023_, 0, v___x_1039_);
v___x_1041_ = v___x_1023_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_a_1038_);
v___x_1041_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
size_t v___x_1042_; size_t v___x_1043_; 
v___x_1042_ = ((size_t)1ULL);
v___x_1043_ = lean_usize_add(v_i_1014_, v___x_1042_);
v_i_1014_ = v___x_1043_;
v_b_1015_ = v___x_1041_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_del_object(v___x_1023_);
lean_dec(v_snd_1021_);
v_a_1047_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1026_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1026_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37___boxed(lean_object* v_init_1057_, lean_object* v_as_1058_, lean_object* v_sz_1059_, lean_object* v_i_1060_, lean_object* v_b_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
size_t v_sz_boxed_1065_; size_t v_i_boxed_1066_; lean_object* v_res_1067_; 
v_sz_boxed_1065_ = lean_unbox_usize(v_sz_1059_);
lean_dec(v_sz_1059_);
v_i_boxed_1066_ = lean_unbox_usize(v_i_1060_);
lean_dec(v_i_1060_);
v_res_1067_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(v_init_1057_, v_as_1058_, v_sz_boxed_1065_, v_i_boxed_1066_, v_b_1061_, v___y_1062_, v___y_1063_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec_ref(v_as_1058_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26___boxed(lean_object* v_init_1068_, lean_object* v_n_1069_, lean_object* v_b_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_1068_, v_n_1069_, v_b_1070_, v___y_1071_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec_ref(v_n_1069_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__12(lean_object* v_t_1075_, lean_object* v_init_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_root_1080_; lean_object* v_tail_1081_; lean_object* v___x_1082_; 
v_root_1080_ = lean_ctor_get(v_t_1075_, 0);
v_tail_1081_ = lean_ctor_get(v_t_1075_, 1);
v___x_1082_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_1076_, v_root_1080_, v_init_1076_, v___y_1077_, v___y_1078_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1119_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1085_ = v___x_1082_;
v_isShared_1086_ = v_isSharedCheck_1119_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1082_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1119_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
if (lean_obj_tag(v_a_1083_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1089_; 
v_a_1087_ = lean_ctor_get(v_a_1083_, 0);
lean_inc(v_a_1087_);
lean_dec_ref_known(v_a_1083_, 1);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v_a_1087_);
v___x_1089_ = v___x_1085_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1087_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; size_t v_sz_1094_; size_t v___x_1095_; lean_object* v___x_1096_; 
lean_del_object(v___x_1085_);
v_a_1091_ = lean_ctor_get(v_a_1083_, 0);
lean_inc(v_a_1091_);
lean_dec_ref_known(v_a_1083_, 1);
v___x_1092_ = lean_box(0);
v___x_1093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
lean_ctor_set(v___x_1093_, 1, v_a_1091_);
v_sz_1094_ = lean_array_size(v_tail_1081_);
v___x_1095_ = ((size_t)0ULL);
v___x_1096_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(v_tail_1081_, v_sz_1094_, v___x_1095_, v___x_1093_, v___y_1077_, v___y_1078_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1110_; 
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1099_ = v___x_1096_;
v_isShared_1100_ = v_isSharedCheck_1110_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1096_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1110_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v_fst_1101_; 
v_fst_1101_ = lean_ctor_get(v_a_1097_, 0);
if (lean_obj_tag(v_fst_1101_) == 0)
{
lean_object* v_snd_1102_; lean_object* v___x_1104_; 
v_snd_1102_ = lean_ctor_get(v_a_1097_, 1);
lean_inc(v_snd_1102_);
lean_dec(v_a_1097_);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 0, v_snd_1102_);
v___x_1104_ = v___x_1099_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_snd_1102_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
else
{
lean_object* v_val_1106_; lean_object* v___x_1108_; 
lean_inc_ref(v_fst_1101_);
lean_dec(v_a_1097_);
v_val_1106_ = lean_ctor_get(v_fst_1101_, 0);
lean_inc(v_val_1106_);
lean_dec_ref_known(v_fst_1101_, 1);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 0, v_val_1106_);
v___x_1108_ = v___x_1099_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_val_1106_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
v_a_1111_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1096_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1096_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
}
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
v_a_1120_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1082_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1082_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__12___boxed(lean_object* v_t_1128_, lean_object* v_init_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lean_PersistentArray_forIn___at___00main_spec__12(v_t_1128_, v_init_1129_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec_ref(v_t_1128_);
return v_res_1133_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0(uint8_t v___x_1141_, uint8_t v_suppressElabErrors_1142_, lean_object* v___x_1143_, lean_object* v_x_1144_){
_start:
{
if (lean_obj_tag(v_x_1144_) == 1)
{
lean_object* v_pre_1145_; 
v_pre_1145_ = lean_ctor_get(v_x_1144_, 0);
switch(lean_obj_tag(v_pre_1145_))
{
case 1:
{
lean_object* v_pre_1146_; 
v_pre_1146_ = lean_ctor_get(v_pre_1145_, 0);
switch(lean_obj_tag(v_pre_1146_))
{
case 0:
{
lean_object* v_str_1147_; lean_object* v_str_1148_; lean_object* v___x_1149_; uint8_t v___x_1150_; 
v_str_1147_ = lean_ctor_get(v_x_1144_, 1);
v_str_1148_ = lean_ctor_get(v_pre_1145_, 1);
v___x_1149_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0));
v___x_1150_ = lean_string_dec_eq(v_str_1148_, v___x_1149_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; uint8_t v___x_1152_; 
v___x_1151_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1));
v___x_1152_ = lean_string_dec_eq(v_str_1148_, v___x_1151_);
if (v___x_1152_ == 0)
{
return v___x_1141_;
}
else
{
lean_object* v___x_1153_; uint8_t v___x_1154_; 
v___x_1153_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2));
v___x_1154_ = lean_string_dec_eq(v_str_1147_, v___x_1153_);
if (v___x_1154_ == 0)
{
return v___x_1141_;
}
else
{
return v_suppressElabErrors_1142_;
}
}
}
else
{
lean_object* v___x_1155_; uint8_t v___x_1156_; 
v___x_1155_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3));
v___x_1156_ = lean_string_dec_eq(v_str_1147_, v___x_1155_);
if (v___x_1156_ == 0)
{
return v___x_1141_;
}
else
{
return v_suppressElabErrors_1142_;
}
}
}
case 1:
{
lean_object* v_pre_1157_; 
v_pre_1157_ = lean_ctor_get(v_pre_1146_, 0);
if (lean_obj_tag(v_pre_1157_) == 0)
{
lean_object* v_str_1158_; lean_object* v_str_1159_; lean_object* v_str_1160_; lean_object* v___x_1161_; uint8_t v___x_1162_; 
v_str_1158_ = lean_ctor_get(v_x_1144_, 1);
v_str_1159_ = lean_ctor_get(v_pre_1145_, 1);
v_str_1160_ = lean_ctor_get(v_pre_1146_, 1);
v___x_1161_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4));
v___x_1162_ = lean_string_dec_eq(v_str_1160_, v___x_1161_);
if (v___x_1162_ == 0)
{
return v___x_1141_;
}
else
{
lean_object* v___x_1163_; uint8_t v___x_1164_; 
v___x_1163_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5));
v___x_1164_ = lean_string_dec_eq(v_str_1159_, v___x_1163_);
if (v___x_1164_ == 0)
{
return v___x_1141_;
}
else
{
lean_object* v___x_1165_; uint8_t v___x_1166_; 
v___x_1165_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6));
v___x_1166_ = lean_string_dec_eq(v_str_1158_, v___x_1165_);
if (v___x_1166_ == 0)
{
return v___x_1141_;
}
else
{
return v_suppressElabErrors_1142_;
}
}
}
}
else
{
return v___x_1141_;
}
}
default: 
{
return v___x_1141_;
}
}
}
case 0:
{
lean_object* v_str_1167_; uint8_t v___x_1168_; 
v_str_1167_ = lean_ctor_get(v_x_1144_, 1);
v___x_1168_ = lean_string_dec_eq(v_str_1167_, v___x_1143_);
if (v___x_1168_ == 0)
{
return v___x_1141_;
}
else
{
return v_suppressElabErrors_1142_;
}
}
default: 
{
return v___x_1141_;
}
}
}
else
{
return v___x_1141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___boxed(lean_object* v___x_1169_, lean_object* v_suppressElabErrors_1170_, lean_object* v___x_1171_, lean_object* v_x_1172_){
_start:
{
uint8_t v___x_36640__boxed_1173_; uint8_t v_suppressElabErrors_boxed_1174_; uint8_t v_res_1175_; lean_object* v_r_1176_; 
v___x_36640__boxed_1173_ = lean_unbox(v___x_1169_);
v_suppressElabErrors_boxed_1174_ = lean_unbox(v_suppressElabErrors_1170_);
v_res_1175_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0(v___x_36640__boxed_1173_, v_suppressElabErrors_boxed_1174_, v___x_1171_, v_x_1172_);
lean_dec(v_x_1172_);
lean_dec_ref(v___x_1171_);
v_r_1176_ = lean_box(v_res_1175_);
return v_r_1176_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0(void){
_start:
{
lean_object* v___x_1177_; double v___x_1178_; 
v___x_1177_ = lean_unsigned_to_nat(0u);
v___x_1178_ = lean_float_of_nat(v___x_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(uint8_t v___x_1180_, lean_object* v_as_1181_, size_t v_sz_1182_, size_t v_i_1183_, lean_object* v_b_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v_a_1189_; uint8_t v___x_1193_; 
v___x_1193_ = lean_usize_dec_lt(v_i_1183_, v_sz_1182_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; 
v___x_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1194_, 0, v_b_1184_);
return v___x_1194_;
}
else
{
lean_object* v_a_1195_; lean_object* v_fst_1196_; lean_object* v_snd_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1273_; 
v_a_1195_ = lean_array_uget(v_as_1181_, v_i_1183_);
v_fst_1196_ = lean_ctor_get(v_a_1195_, 0);
v_snd_1197_ = lean_ctor_get(v_a_1195_, 1);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_a_1195_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1199_ = v_a_1195_;
v_isShared_1200_ = v_isSharedCheck_1273_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_snd_1197_);
lean_inc(v_fst_1196_);
lean_dec(v_a_1195_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1273_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v_fst_1201_; lean_object* v_snd_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1272_; 
v_fst_1201_ = lean_ctor_get(v_fst_1196_, 0);
v_snd_1202_ = lean_ctor_get(v_fst_1196_, 1);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_fst_1196_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1204_ = v_fst_1196_;
v_isShared_1205_ = v_isSharedCheck_1272_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_snd_1202_);
lean_inc(v_fst_1201_);
lean_dec(v_fst_1196_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1272_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; double v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v_fileName_1211_; lean_object* v_fileMap_1212_; uint8_t v_suppressElabErrors_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1206_ = lean_box(0);
v___x_1207_ = lean_box(0);
v___x_1208_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0);
v___x_1209_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1));
v___x_1210_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1210_, 0, v___x_1206_);
lean_ctor_set(v___x_1210_, 1, v___x_1207_);
lean_ctor_set(v___x_1210_, 2, v___x_1209_);
lean_ctor_set_float(v___x_1210_, sizeof(void*)*3, v___x_1208_);
lean_ctor_set_float(v___x_1210_, sizeof(void*)*3 + 8, v___x_1208_);
lean_ctor_set_uint8(v___x_1210_, sizeof(void*)*3 + 16, v___x_1193_);
v_fileName_1211_ = lean_ctor_get(v___y_1185_, 0);
v_fileMap_1212_ = lean_ctor_get(v___y_1185_, 1);
v_suppressElabErrors_1213_ = lean_ctor_get_uint8(v___y_1185_, sizeof(void*)*14 + 1);
v___x_1214_ = lean_box(0);
v___x_1215_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_1216_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_1217_ = l_Lean_MessageData_nil;
v___x_1218_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1210_);
lean_ctor_set(v___x_1218_, 1, v___x_1217_);
lean_ctor_set(v___x_1218_, 2, v_snd_1197_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set_tag(v___x_1204_, 8);
lean_ctor_set(v___x_1204_, 1, v___x_1218_);
lean_ctor_set(v___x_1204_, 0, v___x_1216_);
v___x_1220_ = v___x_1204_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1216_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v___x_1218_);
v___x_1220_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
uint8_t v___x_1221_; lean_object* v___x_1222_; lean_object* v___y_1224_; lean_object* v___y_1225_; 
v___x_1221_ = 0;
lean_inc_ref(v_fileMap_1212_);
lean_inc_ref(v_fileName_1211_);
v___x_1222_ = l_Lean_Elab_mkMessageCore(v_fileName_1211_, v_fileMap_1212_, v___x_1220_, v___x_1221_, v_fst_1201_, v_snd_1202_);
lean_dec(v_snd_1202_);
lean_dec(v_fst_1201_);
if (v_suppressElabErrors_1213_ == 0)
{
v___y_1224_ = v___y_1185_;
v___y_1225_ = v___y_1186_;
goto v___jp_1223_;
}
else
{
lean_object* v_data_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___f_1269_; uint8_t v___x_1270_; 
v_data_1266_ = lean_ctor_get(v___x_1222_, 4);
lean_inc(v_data_1266_);
v___x_1267_ = lean_box(v___x_1180_);
v___x_1268_ = lean_box(v_suppressElabErrors_1213_);
v___f_1269_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1269_, 0, v___x_1267_);
lean_closure_set(v___f_1269_, 1, v___x_1268_);
lean_closure_set(v___f_1269_, 2, v___x_1215_);
v___x_1270_ = l_Lean_MessageData_hasTag(v___f_1269_, v_data_1266_);
if (v___x_1270_ == 0)
{
lean_dec_ref(v___x_1222_);
lean_del_object(v___x_1199_);
v_a_1189_ = v___x_1214_;
goto v___jp_1188_;
}
else
{
v___y_1224_ = v___y_1185_;
v___y_1225_ = v___y_1186_;
goto v___jp_1223_;
}
}
v___jp_1223_:
{
lean_object* v___x_1226_; lean_object* v_fileName_1227_; lean_object* v_pos_1228_; lean_object* v_endPos_1229_; uint8_t v_keepFullRange_1230_; uint8_t v_severity_1231_; uint8_t v_isSilent_1232_; lean_object* v_caption_1233_; lean_object* v_data_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1265_; 
v___x_1226_ = lean_st_ref_take(v___y_1225_);
v_fileName_1227_ = lean_ctor_get(v___x_1222_, 0);
v_pos_1228_ = lean_ctor_get(v___x_1222_, 1);
v_endPos_1229_ = lean_ctor_get(v___x_1222_, 2);
v_keepFullRange_1230_ = lean_ctor_get_uint8(v___x_1222_, sizeof(void*)*5);
v_severity_1231_ = lean_ctor_get_uint8(v___x_1222_, sizeof(void*)*5 + 1);
v_isSilent_1232_ = lean_ctor_get_uint8(v___x_1222_, sizeof(void*)*5 + 2);
v_caption_1233_ = lean_ctor_get(v___x_1222_, 3);
v_data_1234_ = lean_ctor_get(v___x_1222_, 4);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1236_ = v___x_1222_;
v_isShared_1237_ = v_isSharedCheck_1265_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_data_1234_);
lean_inc(v_caption_1233_);
lean_inc(v_endPos_1229_);
lean_inc(v_pos_1228_);
lean_inc(v_fileName_1227_);
lean_dec(v___x_1222_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1265_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v_currNamespace_1238_; lean_object* v_openDecls_1239_; lean_object* v_env_1240_; lean_object* v_nextMacroScope_1241_; lean_object* v_ngen_1242_; lean_object* v_auxDeclNGen_1243_; lean_object* v_traceState_1244_; lean_object* v_cache_1245_; lean_object* v_messages_1246_; lean_object* v_infoState_1247_; lean_object* v_snapshotTasks_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1264_; 
v_currNamespace_1238_ = lean_ctor_get(v___y_1224_, 6);
v_openDecls_1239_ = lean_ctor_get(v___y_1224_, 7);
v_env_1240_ = lean_ctor_get(v___x_1226_, 0);
v_nextMacroScope_1241_ = lean_ctor_get(v___x_1226_, 1);
v_ngen_1242_ = lean_ctor_get(v___x_1226_, 2);
v_auxDeclNGen_1243_ = lean_ctor_get(v___x_1226_, 3);
v_traceState_1244_ = lean_ctor_get(v___x_1226_, 4);
v_cache_1245_ = lean_ctor_get(v___x_1226_, 5);
v_messages_1246_ = lean_ctor_get(v___x_1226_, 6);
v_infoState_1247_ = lean_ctor_get(v___x_1226_, 7);
v_snapshotTasks_1248_ = lean_ctor_get(v___x_1226_, 8);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1250_ = v___x_1226_;
v_isShared_1251_ = v_isSharedCheck_1264_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_snapshotTasks_1248_);
lean_inc(v_infoState_1247_);
lean_inc(v_messages_1246_);
lean_inc(v_cache_1245_);
lean_inc(v_traceState_1244_);
lean_inc(v_auxDeclNGen_1243_);
lean_inc(v_ngen_1242_);
lean_inc(v_nextMacroScope_1241_);
lean_inc(v_env_1240_);
lean_dec(v___x_1226_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1264_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
lean_inc(v_openDecls_1239_);
lean_inc(v_currNamespace_1238_);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 1, v_openDecls_1239_);
lean_ctor_set(v___x_1199_, 0, v_currNamespace_1238_);
v___x_1253_ = v___x_1199_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_currNamespace_1238_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v_openDecls_1239_);
v___x_1253_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1254_; lean_object* v___x_1256_; 
v___x_1254_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
lean_ctor_set(v___x_1254_, 1, v_data_1234_);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 4, v___x_1254_);
v___x_1256_ = v___x_1236_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_fileName_1227_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v_pos_1228_);
lean_ctor_set(v_reuseFailAlloc_1262_, 2, v_endPos_1229_);
lean_ctor_set(v_reuseFailAlloc_1262_, 3, v_caption_1233_);
lean_ctor_set(v_reuseFailAlloc_1262_, 4, v___x_1254_);
lean_ctor_set_uint8(v_reuseFailAlloc_1262_, sizeof(void*)*5, v_keepFullRange_1230_);
lean_ctor_set_uint8(v_reuseFailAlloc_1262_, sizeof(void*)*5 + 1, v_severity_1231_);
lean_ctor_set_uint8(v_reuseFailAlloc_1262_, sizeof(void*)*5 + 2, v_isSilent_1232_);
v___x_1256_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
lean_object* v___x_1257_; lean_object* v___x_1259_; 
v___x_1257_ = l_Lean_MessageLog_add(v___x_1256_, v_messages_1246_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 6, v___x_1257_);
v___x_1259_ = v___x_1250_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_env_1240_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_nextMacroScope_1241_);
lean_ctor_set(v_reuseFailAlloc_1261_, 2, v_ngen_1242_);
lean_ctor_set(v_reuseFailAlloc_1261_, 3, v_auxDeclNGen_1243_);
lean_ctor_set(v_reuseFailAlloc_1261_, 4, v_traceState_1244_);
lean_ctor_set(v_reuseFailAlloc_1261_, 5, v_cache_1245_);
lean_ctor_set(v_reuseFailAlloc_1261_, 6, v___x_1257_);
lean_ctor_set(v_reuseFailAlloc_1261_, 7, v_infoState_1247_);
lean_ctor_set(v_reuseFailAlloc_1261_, 8, v_snapshotTasks_1248_);
v___x_1259_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
lean_object* v___x_1260_; 
v___x_1260_ = lean_st_ref_set(v___y_1225_, v___x_1259_);
v_a_1189_ = v___x_1214_;
goto v___jp_1188_;
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
v___jp_1188_:
{
size_t v___x_1190_; size_t v___x_1191_; 
v___x_1190_ = ((size_t)1ULL);
v___x_1191_ = lean_usize_add(v_i_1183_, v___x_1190_);
v_i_1183_ = v___x_1191_;
v_b_1184_ = v_a_1189_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___boxed(lean_object* v___x_1274_, lean_object* v_as_1275_, lean_object* v_sz_1276_, lean_object* v_i_1277_, lean_object* v_b_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
uint8_t v___x_36713__boxed_1282_; size_t v_sz_boxed_1283_; size_t v_i_boxed_1284_; lean_object* v_res_1285_; 
v___x_36713__boxed_1282_ = lean_unbox(v___x_1274_);
v_sz_boxed_1283_ = lean_unbox_usize(v_sz_1276_);
lean_dec(v_sz_1276_);
v_i_boxed_1284_ = lean_unbox_usize(v_i_1277_);
lean_dec(v_i_1277_);
v_res_1285_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(v___x_36713__boxed_1282_, v_as_1275_, v_sz_boxed_1283_, v_i_boxed_1284_, v_b_1278_, v___y_1279_, v___y_1280_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec_ref(v_as_1275_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(lean_object* v_opts_1286_, lean_object* v_opt_1287_){
_start:
{
lean_object* v_name_1288_; lean_object* v_map_1289_; lean_object* v___x_1290_; 
v_name_1288_ = lean_ctor_get(v_opt_1287_, 0);
v_map_1289_ = lean_ctor_get(v_opts_1286_, 0);
v___x_1290_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1289_, v_name_1288_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v___x_1291_; 
v___x_1291_ = lean_box(0);
return v___x_1291_;
}
else
{
lean_object* v_val_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1301_; 
v_val_1292_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1294_ = v___x_1290_;
v_isShared_1295_ = v_isSharedCheck_1301_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_val_1292_);
lean_dec(v___x_1290_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1301_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
if (lean_obj_tag(v_val_1292_) == 0)
{
lean_object* v_v_1296_; lean_object* v___x_1298_; 
v_v_1296_ = lean_ctor_get(v_val_1292_, 0);
lean_inc_ref(v_v_1296_);
lean_dec_ref_known(v_val_1292_, 1);
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 0, v_v_1296_);
v___x_1298_ = v___x_1294_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_v_1296_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
else
{
lean_object* v___x_1300_; 
lean_del_object(v___x_1294_);
lean_dec(v_val_1292_);
v___x_1300_ = lean_box(0);
return v___x_1300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15___boxed(lean_object* v_opts_1302_, lean_object* v_opt_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(v_opts_1302_, v_opt_1303_);
lean_dec_ref(v_opt_1303_);
lean_dec_ref(v_opts_1302_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(lean_object* v_a_1305_, lean_object* v_fallback_1306_, lean_object* v_x_1307_){
_start:
{
if (lean_obj_tag(v_x_1307_) == 0)
{
lean_inc(v_fallback_1306_);
return v_fallback_1306_;
}
else
{
lean_object* v_key_1308_; lean_object* v_value_1309_; lean_object* v_tail_1310_; uint8_t v___y_1312_; lean_object* v_fst_1314_; lean_object* v_snd_1315_; lean_object* v_fst_1316_; lean_object* v_snd_1317_; uint8_t v___x_1318_; 
v_key_1308_ = lean_ctor_get(v_x_1307_, 0);
v_value_1309_ = lean_ctor_get(v_x_1307_, 1);
v_tail_1310_ = lean_ctor_get(v_x_1307_, 2);
v_fst_1314_ = lean_ctor_get(v_key_1308_, 0);
v_snd_1315_ = lean_ctor_get(v_key_1308_, 1);
v_fst_1316_ = lean_ctor_get(v_a_1305_, 0);
v_snd_1317_ = lean_ctor_get(v_a_1305_, 1);
v___x_1318_ = lean_nat_dec_eq(v_fst_1314_, v_fst_1316_);
if (v___x_1318_ == 0)
{
v___y_1312_ = v___x_1318_;
goto v___jp_1311_;
}
else
{
uint8_t v___x_1319_; 
v___x_1319_ = lean_nat_dec_eq(v_snd_1315_, v_snd_1317_);
v___y_1312_ = v___x_1319_;
goto v___jp_1311_;
}
v___jp_1311_:
{
if (v___y_1312_ == 0)
{
v_x_1307_ = v_tail_1310_;
goto _start;
}
else
{
lean_inc(v_value_1309_);
return v_value_1309_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg___boxed(lean_object* v_a_1320_, lean_object* v_fallback_1321_, lean_object* v_x_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_1320_, v_fallback_1321_, v_x_1322_);
lean_dec(v_x_1322_);
lean_dec(v_fallback_1321_);
lean_dec_ref(v_a_1320_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(lean_object* v_m_1324_, lean_object* v_a_1325_, lean_object* v_fallback_1326_){
_start:
{
lean_object* v_buckets_1327_; lean_object* v_fst_1328_; lean_object* v_snd_1329_; lean_object* v___x_1330_; uint64_t v___x_1331_; uint64_t v___x_1332_; uint64_t v___x_1333_; uint64_t v___x_1334_; uint64_t v___x_1335_; uint64_t v_fold_1336_; uint64_t v___x_1337_; uint64_t v___x_1338_; uint64_t v___x_1339_; size_t v___x_1340_; size_t v___x_1341_; size_t v___x_1342_; size_t v___x_1343_; size_t v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v_buckets_1327_ = lean_ctor_get(v_m_1324_, 1);
v_fst_1328_ = lean_ctor_get(v_a_1325_, 0);
v_snd_1329_ = lean_ctor_get(v_a_1325_, 1);
v___x_1330_ = lean_array_get_size(v_buckets_1327_);
v___x_1331_ = l_String_instHashableRaw_hash(v_fst_1328_);
v___x_1332_ = l_String_instHashableRaw_hash(v_snd_1329_);
v___x_1333_ = lean_uint64_mix_hash(v___x_1331_, v___x_1332_);
v___x_1334_ = 32ULL;
v___x_1335_ = lean_uint64_shift_right(v___x_1333_, v___x_1334_);
v_fold_1336_ = lean_uint64_xor(v___x_1333_, v___x_1335_);
v___x_1337_ = 16ULL;
v___x_1338_ = lean_uint64_shift_right(v_fold_1336_, v___x_1337_);
v___x_1339_ = lean_uint64_xor(v_fold_1336_, v___x_1338_);
v___x_1340_ = lean_uint64_to_usize(v___x_1339_);
v___x_1341_ = lean_usize_of_nat(v___x_1330_);
v___x_1342_ = ((size_t)1ULL);
v___x_1343_ = lean_usize_sub(v___x_1341_, v___x_1342_);
v___x_1344_ = lean_usize_land(v___x_1340_, v___x_1343_);
v___x_1345_ = lean_array_uget_borrowed(v_buckets_1327_, v___x_1344_);
v___x_1346_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_1325_, v_fallback_1326_, v___x_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg___boxed(lean_object* v_m_1347_, lean_object* v_a_1348_, lean_object* v_fallback_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_m_1347_, v_a_1348_, v_fallback_1349_);
lean_dec(v_fallback_1349_);
lean_dec_ref(v_a_1348_);
lean_dec_ref(v_m_1347_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(lean_object* v_x_1351_, lean_object* v_x_1352_){
_start:
{
if (lean_obj_tag(v_x_1352_) == 0)
{
return v_x_1351_;
}
else
{
lean_object* v_key_1353_; lean_object* v_value_1354_; lean_object* v_tail_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1382_; 
v_key_1353_ = lean_ctor_get(v_x_1352_, 0);
v_value_1354_ = lean_ctor_get(v_x_1352_, 1);
v_tail_1355_ = lean_ctor_get(v_x_1352_, 2);
v_isSharedCheck_1382_ = !lean_is_exclusive(v_x_1352_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1357_ = v_x_1352_;
v_isShared_1358_ = v_isSharedCheck_1382_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_tail_1355_);
lean_inc(v_value_1354_);
lean_inc(v_key_1353_);
lean_dec(v_x_1352_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1382_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v_fst_1359_; lean_object* v_snd_1360_; lean_object* v___x_1361_; uint64_t v___x_1362_; uint64_t v___x_1363_; uint64_t v___x_1364_; uint64_t v___x_1365_; uint64_t v___x_1366_; uint64_t v_fold_1367_; uint64_t v___x_1368_; uint64_t v___x_1369_; uint64_t v___x_1370_; size_t v___x_1371_; size_t v___x_1372_; size_t v___x_1373_; size_t v___x_1374_; size_t v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1378_; 
v_fst_1359_ = lean_ctor_get(v_key_1353_, 0);
v_snd_1360_ = lean_ctor_get(v_key_1353_, 1);
v___x_1361_ = lean_array_get_size(v_x_1351_);
v___x_1362_ = l_String_instHashableRaw_hash(v_fst_1359_);
v___x_1363_ = l_String_instHashableRaw_hash(v_snd_1360_);
v___x_1364_ = lean_uint64_mix_hash(v___x_1362_, v___x_1363_);
v___x_1365_ = 32ULL;
v___x_1366_ = lean_uint64_shift_right(v___x_1364_, v___x_1365_);
v_fold_1367_ = lean_uint64_xor(v___x_1364_, v___x_1366_);
v___x_1368_ = 16ULL;
v___x_1369_ = lean_uint64_shift_right(v_fold_1367_, v___x_1368_);
v___x_1370_ = lean_uint64_xor(v_fold_1367_, v___x_1369_);
v___x_1371_ = lean_uint64_to_usize(v___x_1370_);
v___x_1372_ = lean_usize_of_nat(v___x_1361_);
v___x_1373_ = ((size_t)1ULL);
v___x_1374_ = lean_usize_sub(v___x_1372_, v___x_1373_);
v___x_1375_ = lean_usize_land(v___x_1371_, v___x_1374_);
v___x_1376_ = lean_array_uget_borrowed(v_x_1351_, v___x_1375_);
lean_inc(v___x_1376_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 2, v___x_1376_);
v___x_1378_ = v___x_1357_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_key_1353_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v_value_1354_);
lean_ctor_set(v_reuseFailAlloc_1381_, 2, v___x_1376_);
v___x_1378_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
lean_object* v___x_1379_; 
v___x_1379_ = lean_array_uset(v_x_1351_, v___x_1375_, v___x_1378_);
v_x_1351_ = v___x_1379_;
v_x_1352_ = v_tail_1355_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(lean_object* v_i_1383_, lean_object* v_source_1384_, lean_object* v_target_1385_){
_start:
{
lean_object* v___x_1386_; uint8_t v___x_1387_; 
v___x_1386_ = lean_array_get_size(v_source_1384_);
v___x_1387_ = lean_nat_dec_lt(v_i_1383_, v___x_1386_);
if (v___x_1387_ == 0)
{
lean_dec_ref(v_source_1384_);
lean_dec(v_i_1383_);
return v_target_1385_;
}
else
{
lean_object* v_es_1388_; lean_object* v___x_1389_; lean_object* v_source_1390_; lean_object* v_target_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v_es_1388_ = lean_array_fget(v_source_1384_, v_i_1383_);
v___x_1389_ = lean_box(0);
v_source_1390_ = lean_array_fset(v_source_1384_, v_i_1383_, v___x_1389_);
v_target_1391_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(v_target_1385_, v_es_1388_);
v___x_1392_ = lean_unsigned_to_nat(1u);
v___x_1393_ = lean_nat_add(v_i_1383_, v___x_1392_);
lean_dec(v_i_1383_);
v_i_1383_ = v___x_1393_;
v_source_1384_ = v_source_1390_;
v_target_1385_ = v_target_1391_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(lean_object* v_data_1395_){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v_nbuckets_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1396_ = lean_array_get_size(v_data_1395_);
v___x_1397_ = lean_unsigned_to_nat(2u);
v_nbuckets_1398_ = lean_nat_mul(v___x_1396_, v___x_1397_);
v___x_1399_ = lean_unsigned_to_nat(0u);
v___x_1400_ = lean_box(0);
v___x_1401_ = lean_mk_array(v_nbuckets_1398_, v___x_1400_);
v___x_1402_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(v___x_1399_, v_data_1395_, v___x_1401_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(lean_object* v_a_1403_, lean_object* v_b_1404_, lean_object* v_x_1405_){
_start:
{
if (lean_obj_tag(v_x_1405_) == 0)
{
lean_dec(v_b_1404_);
lean_dec_ref(v_a_1403_);
return v_x_1405_;
}
else
{
lean_object* v_key_1406_; lean_object* v_value_1407_; lean_object* v_tail_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1427_; 
v_key_1406_ = lean_ctor_get(v_x_1405_, 0);
v_value_1407_ = lean_ctor_get(v_x_1405_, 1);
v_tail_1408_ = lean_ctor_get(v_x_1405_, 2);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_x_1405_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1410_ = v_x_1405_;
v_isShared_1411_ = v_isSharedCheck_1427_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_tail_1408_);
lean_inc(v_value_1407_);
lean_inc(v_key_1406_);
lean_dec(v_x_1405_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1427_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
uint8_t v___y_1413_; lean_object* v_fst_1421_; lean_object* v_snd_1422_; lean_object* v_fst_1423_; lean_object* v_snd_1424_; uint8_t v___x_1425_; 
v_fst_1421_ = lean_ctor_get(v_key_1406_, 0);
v_snd_1422_ = lean_ctor_get(v_key_1406_, 1);
v_fst_1423_ = lean_ctor_get(v_a_1403_, 0);
v_snd_1424_ = lean_ctor_get(v_a_1403_, 1);
v___x_1425_ = lean_nat_dec_eq(v_fst_1421_, v_fst_1423_);
if (v___x_1425_ == 0)
{
v___y_1413_ = v___x_1425_;
goto v___jp_1412_;
}
else
{
uint8_t v___x_1426_; 
v___x_1426_ = lean_nat_dec_eq(v_snd_1422_, v_snd_1424_);
v___y_1413_ = v___x_1426_;
goto v___jp_1412_;
}
v___jp_1412_:
{
if (v___y_1413_ == 0)
{
lean_object* v___x_1414_; lean_object* v___x_1416_; 
v___x_1414_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_1403_, v_b_1404_, v_tail_1408_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 2, v___x_1414_);
v___x_1416_ = v___x_1410_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_key_1406_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_value_1407_);
lean_ctor_set(v_reuseFailAlloc_1417_, 2, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
else
{
lean_object* v___x_1419_; 
lean_dec(v_value_1407_);
lean_dec(v_key_1406_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 1, v_b_1404_);
lean_ctor_set(v___x_1410_, 0, v_a_1403_);
v___x_1419_ = v___x_1410_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1403_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_b_1404_);
lean_ctor_set(v_reuseFailAlloc_1420_, 2, v_tail_1408_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(lean_object* v_a_1428_, lean_object* v_x_1429_){
_start:
{
if (lean_obj_tag(v_x_1429_) == 0)
{
uint8_t v___x_1430_; 
v___x_1430_ = 0;
return v___x_1430_;
}
else
{
lean_object* v_key_1431_; lean_object* v_tail_1432_; uint8_t v___y_1434_; lean_object* v_fst_1436_; lean_object* v_snd_1437_; lean_object* v_fst_1438_; lean_object* v_snd_1439_; uint8_t v___x_1440_; 
v_key_1431_ = lean_ctor_get(v_x_1429_, 0);
v_tail_1432_ = lean_ctor_get(v_x_1429_, 2);
v_fst_1436_ = lean_ctor_get(v_key_1431_, 0);
v_snd_1437_ = lean_ctor_get(v_key_1431_, 1);
v_fst_1438_ = lean_ctor_get(v_a_1428_, 0);
v_snd_1439_ = lean_ctor_get(v_a_1428_, 1);
v___x_1440_ = lean_nat_dec_eq(v_fst_1436_, v_fst_1438_);
if (v___x_1440_ == 0)
{
v___y_1434_ = v___x_1440_;
goto v___jp_1433_;
}
else
{
uint8_t v___x_1441_; 
v___x_1441_ = lean_nat_dec_eq(v_snd_1437_, v_snd_1439_);
v___y_1434_ = v___x_1441_;
goto v___jp_1433_;
}
v___jp_1433_:
{
if (v___y_1434_ == 0)
{
v_x_1429_ = v_tail_1432_;
goto _start;
}
else
{
return v___y_1434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg___boxed(lean_object* v_a_1442_, lean_object* v_x_1443_){
_start:
{
uint8_t v_res_1444_; lean_object* v_r_1445_; 
v_res_1444_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_1442_, v_x_1443_);
lean_dec(v_x_1443_);
lean_dec_ref(v_a_1442_);
v_r_1445_ = lean_box(v_res_1444_);
return v_r_1445_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(lean_object* v_m_1446_, lean_object* v_a_1447_, lean_object* v_b_1448_){
_start:
{
lean_object* v_size_1449_; lean_object* v_buckets_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1497_; 
v_size_1449_ = lean_ctor_get(v_m_1446_, 0);
v_buckets_1450_ = lean_ctor_get(v_m_1446_, 1);
v_isSharedCheck_1497_ = !lean_is_exclusive(v_m_1446_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1452_ = v_m_1446_;
v_isShared_1453_ = v_isSharedCheck_1497_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_buckets_1450_);
lean_inc(v_size_1449_);
lean_dec(v_m_1446_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1497_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v_fst_1454_; lean_object* v_snd_1455_; lean_object* v___x_1456_; uint64_t v___x_1457_; uint64_t v___x_1458_; uint64_t v___x_1459_; uint64_t v___x_1460_; uint64_t v___x_1461_; uint64_t v_fold_1462_; uint64_t v___x_1463_; uint64_t v___x_1464_; uint64_t v___x_1465_; size_t v___x_1466_; size_t v___x_1467_; size_t v___x_1468_; size_t v___x_1469_; size_t v___x_1470_; lean_object* v_bkt_1471_; uint8_t v___x_1472_; 
v_fst_1454_ = lean_ctor_get(v_a_1447_, 0);
v_snd_1455_ = lean_ctor_get(v_a_1447_, 1);
v___x_1456_ = lean_array_get_size(v_buckets_1450_);
v___x_1457_ = l_String_instHashableRaw_hash(v_fst_1454_);
v___x_1458_ = l_String_instHashableRaw_hash(v_snd_1455_);
v___x_1459_ = lean_uint64_mix_hash(v___x_1457_, v___x_1458_);
v___x_1460_ = 32ULL;
v___x_1461_ = lean_uint64_shift_right(v___x_1459_, v___x_1460_);
v_fold_1462_ = lean_uint64_xor(v___x_1459_, v___x_1461_);
v___x_1463_ = 16ULL;
v___x_1464_ = lean_uint64_shift_right(v_fold_1462_, v___x_1463_);
v___x_1465_ = lean_uint64_xor(v_fold_1462_, v___x_1464_);
v___x_1466_ = lean_uint64_to_usize(v___x_1465_);
v___x_1467_ = lean_usize_of_nat(v___x_1456_);
v___x_1468_ = ((size_t)1ULL);
v___x_1469_ = lean_usize_sub(v___x_1467_, v___x_1468_);
v___x_1470_ = lean_usize_land(v___x_1466_, v___x_1469_);
v_bkt_1471_ = lean_array_uget_borrowed(v_buckets_1450_, v___x_1470_);
v___x_1472_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_1447_, v_bkt_1471_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1473_; lean_object* v_size_x27_1474_; lean_object* v___x_1475_; lean_object* v_buckets_x27_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; uint8_t v___x_1482_; 
v___x_1473_ = lean_unsigned_to_nat(1u);
v_size_x27_1474_ = lean_nat_add(v_size_1449_, v___x_1473_);
lean_dec(v_size_1449_);
lean_inc(v_bkt_1471_);
v___x_1475_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1475_, 0, v_a_1447_);
lean_ctor_set(v___x_1475_, 1, v_b_1448_);
lean_ctor_set(v___x_1475_, 2, v_bkt_1471_);
v_buckets_x27_1476_ = lean_array_uset(v_buckets_1450_, v___x_1470_, v___x_1475_);
v___x_1477_ = lean_unsigned_to_nat(4u);
v___x_1478_ = lean_nat_mul(v_size_x27_1474_, v___x_1477_);
v___x_1479_ = lean_unsigned_to_nat(3u);
v___x_1480_ = lean_nat_div(v___x_1478_, v___x_1479_);
lean_dec(v___x_1478_);
v___x_1481_ = lean_array_get_size(v_buckets_x27_1476_);
v___x_1482_ = lean_nat_dec_le(v___x_1480_, v___x_1481_);
lean_dec(v___x_1480_);
if (v___x_1482_ == 0)
{
lean_object* v_val_1483_; lean_object* v___x_1485_; 
v_val_1483_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(v_buckets_x27_1476_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 1, v_val_1483_);
lean_ctor_set(v___x_1452_, 0, v_size_x27_1474_);
v___x_1485_ = v___x_1452_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_size_x27_1474_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v_val_1483_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
else
{
lean_object* v___x_1488_; 
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 1, v_buckets_x27_1476_);
lean_ctor_set(v___x_1452_, 0, v_size_x27_1474_);
v___x_1488_ = v___x_1452_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_size_x27_1474_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v_buckets_x27_1476_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
else
{
lean_object* v___x_1490_; lean_object* v_buckets_x27_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1495_; 
lean_inc(v_bkt_1471_);
v___x_1490_ = lean_box(0);
v_buckets_x27_1491_ = lean_array_uset(v_buckets_1450_, v___x_1470_, v___x_1490_);
v___x_1492_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_1447_, v_b_1448_, v_bkt_1471_);
v___x_1493_ = lean_array_uset(v_buckets_x27_1491_, v___x_1470_, v___x_1492_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 1, v___x_1493_);
v___x_1495_ = v___x_1452_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_size_1449_);
lean_ctor_set(v_reuseFailAlloc_1496_, 1, v___x_1493_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(uint8_t v___x_1500_, lean_object* v_as_1501_, size_t v_sz_1502_, size_t v_i_1503_, lean_object* v_b_1504_, lean_object* v___y_1505_){
_start:
{
uint8_t v___x_1507_; 
v___x_1507_ = lean_usize_dec_lt(v_i_1503_, v_sz_1502_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1508_; 
v___x_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1508_, 0, v_b_1504_);
return v___x_1508_;
}
else
{
lean_object* v_snd_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1546_; 
v_snd_1509_ = lean_ctor_get(v_b_1504_, 1);
v_isSharedCheck_1546_ = !lean_is_exclusive(v_b_1504_);
if (v_isSharedCheck_1546_ == 0)
{
lean_object* v_unused_1547_; 
v_unused_1547_ = lean_ctor_get(v_b_1504_, 0);
lean_dec(v_unused_1547_);
v___x_1511_ = v_b_1504_;
v_isShared_1512_ = v_isSharedCheck_1546_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_snd_1509_);
lean_dec(v_b_1504_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1546_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v_ref_1513_; lean_object* v_a_1514_; lean_object* v_ref_1515_; lean_object* v_msg_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1545_; 
v_ref_1513_ = lean_ctor_get(v___y_1505_, 5);
v_a_1514_ = lean_array_uget(v_as_1501_, v_i_1503_);
v_ref_1515_ = lean_ctor_get(v_a_1514_, 0);
v_msg_1516_ = lean_ctor_get(v_a_1514_, 1);
v_isSharedCheck_1545_ = !lean_is_exclusive(v_a_1514_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1518_ = v_a_1514_;
v_isShared_1519_ = v_isSharedCheck_1545_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_msg_1516_);
lean_inc(v_ref_1515_);
lean_dec(v_a_1514_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1545_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1520_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v_ref_1537_; lean_object* v___y_1539_; lean_object* v___x_1542_; 
v___x_1520_ = lean_box(0);
v_ref_1537_ = l_Lean_replaceRef(v_ref_1515_, v_ref_1513_);
lean_dec(v_ref_1515_);
v___x_1542_ = l_Lean_Syntax_getPos_x3f(v_ref_1537_, v___x_1500_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v___x_1543_; 
v___x_1543_ = lean_unsigned_to_nat(0u);
v___y_1539_ = v___x_1543_;
goto v___jp_1538_;
}
else
{
lean_object* v_val_1544_; 
v_val_1544_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_val_1544_);
lean_dec_ref_known(v___x_1542_, 1);
v___y_1539_ = v_val_1544_;
goto v___jp_1538_;
}
v___jp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 1, v___y_1523_);
lean_ctor_set(v___x_1511_, 0, v___y_1522_);
v___x_1525_ = v___x_1511_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___y_1522_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v___y_1523_);
v___x_1525_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v_pos2traces_1529_; lean_object* v___x_1531_; 
v___x_1526_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1527_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1509_, v___x_1525_, v___x_1526_);
v___x_1528_ = lean_array_push(v___x_1527_, v_msg_1516_);
v_pos2traces_1529_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1509_, v___x_1525_, v___x_1528_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 1, v_pos2traces_1529_);
lean_ctor_set(v___x_1518_, 0, v___x_1520_);
v___x_1531_ = v___x_1518_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1520_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v_pos2traces_1529_);
v___x_1531_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
size_t v___x_1532_; size_t v___x_1533_; 
v___x_1532_ = ((size_t)1ULL);
v___x_1533_ = lean_usize_add(v_i_1503_, v___x_1532_);
v_i_1503_ = v___x_1533_;
v_b_1504_ = v___x_1531_;
goto _start;
}
}
}
v___jp_1538_:
{
lean_object* v___x_1540_; 
v___x_1540_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1537_, v___x_1500_);
lean_dec(v_ref_1537_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_inc(v___y_1539_);
v___y_1522_ = v___y_1539_;
v___y_1523_ = v___y_1539_;
goto v___jp_1521_;
}
else
{
lean_object* v_val_1541_; 
v_val_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_val_1541_);
lean_dec_ref_known(v___x_1540_, 1);
v___y_1522_ = v___y_1539_;
v___y_1523_ = v_val_1541_;
goto v___jp_1521_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___boxed(lean_object* v___x_1548_, lean_object* v_as_1549_, lean_object* v_sz_1550_, lean_object* v_i_1551_, lean_object* v_b_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
uint8_t v___x_37193__boxed_1555_; size_t v_sz_boxed_1556_; size_t v_i_boxed_1557_; lean_object* v_res_1558_; 
v___x_37193__boxed_1555_ = lean_unbox(v___x_1548_);
v_sz_boxed_1556_ = lean_unbox_usize(v_sz_1550_);
lean_dec(v_sz_1550_);
v_i_boxed_1557_ = lean_unbox_usize(v_i_1551_);
lean_dec(v_i_1551_);
v_res_1558_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_37193__boxed_1555_, v_as_1549_, v_sz_boxed_1556_, v_i_boxed_1557_, v_b_1552_, v___y_1553_);
lean_dec_ref(v___y_1553_);
lean_dec_ref(v_as_1549_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(uint8_t v___x_1559_, lean_object* v_as_1560_, size_t v_sz_1561_, size_t v_i_1562_, lean_object* v_b_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
uint8_t v___x_1567_; 
v___x_1567_ = lean_usize_dec_lt(v_i_1562_, v_sz_1561_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; 
v___x_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1568_, 0, v_b_1563_);
return v___x_1568_;
}
else
{
lean_object* v_snd_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1606_; 
v_snd_1569_ = lean_ctor_get(v_b_1563_, 1);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_b_1563_);
if (v_isSharedCheck_1606_ == 0)
{
lean_object* v_unused_1607_; 
v_unused_1607_ = lean_ctor_get(v_b_1563_, 0);
lean_dec(v_unused_1607_);
v___x_1571_ = v_b_1563_;
v_isShared_1572_ = v_isSharedCheck_1606_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_snd_1569_);
lean_dec(v_b_1563_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1606_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v_ref_1573_; lean_object* v_a_1574_; lean_object* v_ref_1575_; lean_object* v_msg_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1605_; 
v_ref_1573_ = lean_ctor_get(v___y_1564_, 5);
v_a_1574_ = lean_array_uget(v_as_1560_, v_i_1562_);
v_ref_1575_ = lean_ctor_get(v_a_1574_, 0);
v_msg_1576_ = lean_ctor_get(v_a_1574_, 1);
v_isSharedCheck_1605_ = !lean_is_exclusive(v_a_1574_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1578_ = v_a_1574_;
v_isShared_1579_ = v_isSharedCheck_1605_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_msg_1576_);
lean_inc(v_ref_1575_);
lean_dec(v_a_1574_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1605_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1580_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v_ref_1597_; lean_object* v___y_1599_; lean_object* v___x_1602_; 
v___x_1580_ = lean_box(0);
v_ref_1597_ = l_Lean_replaceRef(v_ref_1575_, v_ref_1573_);
lean_dec(v_ref_1575_);
v___x_1602_ = l_Lean_Syntax_getPos_x3f(v_ref_1597_, v___x_1559_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v___x_1603_; 
v___x_1603_ = lean_unsigned_to_nat(0u);
v___y_1599_ = v___x_1603_;
goto v___jp_1598_;
}
else
{
lean_object* v_val_1604_; 
v_val_1604_ = lean_ctor_get(v___x_1602_, 0);
lean_inc(v_val_1604_);
lean_dec_ref_known(v___x_1602_, 1);
v___y_1599_ = v_val_1604_;
goto v___jp_1598_;
}
v___jp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 1, v___y_1583_);
lean_ctor_set(v___x_1571_, 0, v___y_1582_);
v___x_1585_ = v___x_1571_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___y_1582_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v___y_1583_);
v___x_1585_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v_pos2traces_1589_; lean_object* v___x_1591_; 
v___x_1586_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1587_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1569_, v___x_1585_, v___x_1586_);
v___x_1588_ = lean_array_push(v___x_1587_, v_msg_1576_);
v_pos2traces_1589_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1569_, v___x_1585_, v___x_1588_);
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 1, v_pos2traces_1589_);
lean_ctor_set(v___x_1578_, 0, v___x_1580_);
v___x_1591_ = v___x_1578_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1580_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v_pos2traces_1589_);
v___x_1591_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
size_t v___x_1592_; size_t v___x_1593_; lean_object* v___x_1594_; 
v___x_1592_ = ((size_t)1ULL);
v___x_1593_ = lean_usize_add(v_i_1562_, v___x_1592_);
v___x_1594_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_1559_, v_as_1560_, v_sz_1561_, v___x_1593_, v___x_1591_, v___y_1564_);
return v___x_1594_;
}
}
}
v___jp_1598_:
{
lean_object* v___x_1600_; 
v___x_1600_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1597_, v___x_1559_);
lean_dec(v_ref_1597_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_inc(v___y_1599_);
v___y_1582_ = v___y_1599_;
v___y_1583_ = v___y_1599_;
goto v___jp_1581_;
}
else
{
lean_object* v_val_1601_; 
v_val_1601_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_val_1601_);
lean_dec_ref_known(v___x_1600_, 1);
v___y_1582_ = v___y_1599_;
v___y_1583_ = v_val_1601_;
goto v___jp_1581_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40___boxed(lean_object* v___x_1608_, lean_object* v_as_1609_, lean_object* v_sz_1610_, lean_object* v_i_1611_, lean_object* v_b_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
uint8_t v___x_37274__boxed_1616_; size_t v_sz_boxed_1617_; size_t v_i_boxed_1618_; lean_object* v_res_1619_; 
v___x_37274__boxed_1616_ = lean_unbox(v___x_1608_);
v_sz_boxed_1617_ = lean_unbox_usize(v_sz_1610_);
lean_dec(v_sz_1610_);
v_i_boxed_1618_ = lean_unbox_usize(v_i_1611_);
lean_dec(v_i_1611_);
v_res_1619_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(v___x_37274__boxed_1616_, v_as_1609_, v_sz_boxed_1617_, v_i_boxed_1618_, v_b_1612_, v___y_1613_, v___y_1614_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec_ref(v_as_1609_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(lean_object* v_init_1620_, uint8_t v___x_1621_, lean_object* v_n_1622_, lean_object* v_b_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
if (lean_obj_tag(v_n_1622_) == 0)
{
lean_object* v_cs_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; size_t v_sz_1630_; size_t v___x_1631_; lean_object* v___x_1632_; 
v_cs_1627_ = lean_ctor_get(v_n_1622_, 0);
v___x_1628_ = lean_box(0);
v___x_1629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1628_);
lean_ctor_set(v___x_1629_, 1, v_b_1623_);
v_sz_1630_ = lean_array_size(v_cs_1627_);
v___x_1631_ = ((size_t)0ULL);
v___x_1632_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(v_init_1620_, v___x_1621_, v_cs_1627_, v_sz_1630_, v___x_1631_, v___x_1629_, v___y_1624_, v___y_1625_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1647_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1635_ = v___x_1632_;
v_isShared_1636_ = v_isSharedCheck_1647_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1632_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1647_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v_fst_1637_; 
v_fst_1637_ = lean_ctor_get(v_a_1633_, 0);
if (lean_obj_tag(v_fst_1637_) == 0)
{
lean_object* v_snd_1638_; lean_object* v___x_1639_; lean_object* v___x_1641_; 
v_snd_1638_ = lean_ctor_get(v_a_1633_, 1);
lean_inc(v_snd_1638_);
lean_dec(v_a_1633_);
v___x_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1639_, 0, v_snd_1638_);
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 0, v___x_1639_);
v___x_1641_ = v___x_1635_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1639_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
else
{
lean_object* v_val_1643_; lean_object* v___x_1645_; 
lean_inc_ref(v_fst_1637_);
lean_dec(v_a_1633_);
v_val_1643_ = lean_ctor_get(v_fst_1637_, 0);
lean_inc(v_val_1643_);
lean_dec_ref_known(v_fst_1637_, 1);
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 0, v_val_1643_);
v___x_1645_ = v___x_1635_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_val_1643_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
else
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1655_; 
v_a_1648_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1650_ = v___x_1632_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1632_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_a_1648_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
else
{
lean_object* v_vs_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; size_t v_sz_1659_; size_t v___x_1660_; lean_object* v___x_1661_; 
v_vs_1656_ = lean_ctor_get(v_n_1622_, 0);
v___x_1657_ = lean_box(0);
v___x_1658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1657_);
lean_ctor_set(v___x_1658_, 1, v_b_1623_);
v_sz_1659_ = lean_array_size(v_vs_1656_);
v___x_1660_ = ((size_t)0ULL);
v___x_1661_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(v___x_1621_, v_vs_1656_, v_sz_1659_, v___x_1660_, v___x_1658_, v___y_1624_, v___y_1625_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1676_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1664_ = v___x_1661_;
v_isShared_1665_ = v_isSharedCheck_1676_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1661_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1676_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v_fst_1666_; 
v_fst_1666_ = lean_ctor_get(v_a_1662_, 0);
if (lean_obj_tag(v_fst_1666_) == 0)
{
lean_object* v_snd_1667_; lean_object* v___x_1668_; lean_object* v___x_1670_; 
v_snd_1667_ = lean_ctor_get(v_a_1662_, 1);
lean_inc(v_snd_1667_);
lean_dec(v_a_1662_);
v___x_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1668_, 0, v_snd_1667_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 0, v___x_1668_);
v___x_1670_ = v___x_1664_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1668_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
else
{
lean_object* v_val_1672_; lean_object* v___x_1674_; 
lean_inc_ref(v_fst_1666_);
lean_dec(v_a_1662_);
v_val_1672_ = lean_ctor_get(v_fst_1666_, 0);
lean_inc(v_val_1672_);
lean_dec_ref_known(v_fst_1666_, 1);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 0, v_val_1672_);
v___x_1674_ = v___x_1664_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_val_1672_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
else
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1684_; 
v_a_1677_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1679_ = v___x_1661_;
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v___x_1661_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1682_; 
if (v_isShared_1680_ == 0)
{
v___x_1682_ = v___x_1679_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1677_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(lean_object* v_init_1685_, uint8_t v___x_1686_, lean_object* v_as_1687_, size_t v_sz_1688_, size_t v_i_1689_, lean_object* v_b_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
uint8_t v___x_1694_; 
v___x_1694_ = lean_usize_dec_lt(v_i_1689_, v_sz_1688_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1695_; 
v___x_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1695_, 0, v_b_1690_);
return v___x_1695_;
}
else
{
lean_object* v_snd_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1730_; 
v_snd_1696_ = lean_ctor_get(v_b_1690_, 1);
v_isSharedCheck_1730_ = !lean_is_exclusive(v_b_1690_);
if (v_isSharedCheck_1730_ == 0)
{
lean_object* v_unused_1731_; 
v_unused_1731_ = lean_ctor_get(v_b_1690_, 0);
lean_dec(v_unused_1731_);
v___x_1698_ = v_b_1690_;
v_isShared_1699_ = v_isSharedCheck_1730_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_snd_1696_);
lean_dec(v_b_1690_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1730_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v_a_1700_; lean_object* v___x_1701_; 
v_a_1700_ = lean_array_uget_borrowed(v_as_1687_, v_i_1689_);
lean_inc(v_snd_1696_);
v___x_1701_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1685_, v___x_1686_, v_a_1700_, v_snd_1696_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1721_; 
v_a_1702_ = lean_ctor_get(v___x_1701_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1704_ = v___x_1701_;
v_isShared_1705_ = v_isSharedCheck_1721_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1701_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1721_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
if (lean_obj_tag(v_a_1702_) == 0)
{
lean_object* v___x_1706_; lean_object* v___x_1708_; 
v___x_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1706_, 0, v_a_1702_);
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 0, v___x_1706_);
v___x_1708_ = v___x_1698_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1706_);
lean_ctor_set(v_reuseFailAlloc_1712_, 1, v_snd_1696_);
v___x_1708_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
lean_object* v___x_1710_; 
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 0, v___x_1708_);
v___x_1710_ = v___x_1704_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1708_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
else
{
lean_object* v_a_1713_; lean_object* v___x_1714_; lean_object* v___x_1716_; 
lean_del_object(v___x_1704_);
lean_dec(v_snd_1696_);
v_a_1713_ = lean_ctor_get(v_a_1702_, 0);
lean_inc(v_a_1713_);
lean_dec_ref_known(v_a_1702_, 1);
v___x_1714_ = lean_box(0);
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 1, v_a_1713_);
lean_ctor_set(v___x_1698_, 0, v___x_1714_);
v___x_1716_ = v___x_1698_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v___x_1714_);
lean_ctor_set(v_reuseFailAlloc_1720_, 1, v_a_1713_);
v___x_1716_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
size_t v___x_1717_; size_t v___x_1718_; 
v___x_1717_ = ((size_t)1ULL);
v___x_1718_ = lean_usize_add(v_i_1689_, v___x_1717_);
v_i_1689_ = v___x_1718_;
v_b_1690_ = v___x_1716_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
lean_del_object(v___x_1698_);
lean_dec(v_snd_1696_);
v_a_1722_ = lean_ctor_get(v___x_1701_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1724_ = v___x_1701_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1701_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_a_1722_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39___boxed(lean_object* v_init_1732_, lean_object* v___x_1733_, lean_object* v_as_1734_, lean_object* v_sz_1735_, lean_object* v_i_1736_, lean_object* v_b_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
uint8_t v___x_37355__boxed_1741_; size_t v_sz_boxed_1742_; size_t v_i_boxed_1743_; lean_object* v_res_1744_; 
v___x_37355__boxed_1741_ = lean_unbox(v___x_1733_);
v_sz_boxed_1742_ = lean_unbox_usize(v_sz_1735_);
lean_dec(v_sz_1735_);
v_i_boxed_1743_ = lean_unbox_usize(v_i_1736_);
lean_dec(v_i_1736_);
v_res_1744_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(v_init_1732_, v___x_37355__boxed_1741_, v_as_1734_, v_sz_boxed_1742_, v_i_boxed_1743_, v_b_1737_, v___y_1738_, v___y_1739_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec_ref(v_as_1734_);
lean_dec_ref(v_init_1732_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27___boxed(lean_object* v_init_1745_, lean_object* v___x_1746_, lean_object* v_n_1747_, lean_object* v_b_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
uint8_t v___x_37375__boxed_1752_; lean_object* v_res_1753_; 
v___x_37375__boxed_1752_ = lean_unbox(v___x_1746_);
v_res_1753_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1745_, v___x_37375__boxed_1752_, v_n_1747_, v_b_1748_, v___y_1749_, v___y_1750_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec_ref(v_n_1747_);
lean_dec_ref(v_init_1745_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(uint8_t v___x_1754_, lean_object* v_as_1755_, size_t v_sz_1756_, size_t v_i_1757_, lean_object* v_b_1758_, lean_object* v___y_1759_){
_start:
{
uint8_t v___x_1761_; 
v___x_1761_ = lean_usize_dec_lt(v_i_1757_, v_sz_1756_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1762_; 
v___x_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1762_, 0, v_b_1758_);
return v___x_1762_;
}
else
{
lean_object* v_snd_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1800_; 
v_snd_1763_ = lean_ctor_get(v_b_1758_, 1);
v_isSharedCheck_1800_ = !lean_is_exclusive(v_b_1758_);
if (v_isSharedCheck_1800_ == 0)
{
lean_object* v_unused_1801_; 
v_unused_1801_ = lean_ctor_get(v_b_1758_, 0);
lean_dec(v_unused_1801_);
v___x_1765_ = v_b_1758_;
v_isShared_1766_ = v_isSharedCheck_1800_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_snd_1763_);
lean_dec(v_b_1758_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1800_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v_ref_1767_; lean_object* v_a_1768_; lean_object* v_ref_1769_; lean_object* v_msg_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1799_; 
v_ref_1767_ = lean_ctor_get(v___y_1759_, 5);
v_a_1768_ = lean_array_uget(v_as_1755_, v_i_1757_);
v_ref_1769_ = lean_ctor_get(v_a_1768_, 0);
v_msg_1770_ = lean_ctor_get(v_a_1768_, 1);
v_isSharedCheck_1799_ = !lean_is_exclusive(v_a_1768_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1772_ = v_a_1768_;
v_isShared_1773_ = v_isSharedCheck_1799_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_msg_1770_);
lean_inc(v_ref_1769_);
lean_dec(v_a_1768_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1799_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1774_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v_ref_1791_; lean_object* v___y_1793_; lean_object* v___x_1796_; 
v___x_1774_ = lean_box(0);
v_ref_1791_ = l_Lean_replaceRef(v_ref_1769_, v_ref_1767_);
lean_dec(v_ref_1769_);
v___x_1796_ = l_Lean_Syntax_getPos_x3f(v_ref_1791_, v___x_1754_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v___x_1797_; 
v___x_1797_ = lean_unsigned_to_nat(0u);
v___y_1793_ = v___x_1797_;
goto v___jp_1792_;
}
else
{
lean_object* v_val_1798_; 
v_val_1798_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_val_1798_);
lean_dec_ref_known(v___x_1796_, 1);
v___y_1793_ = v_val_1798_;
goto v___jp_1792_;
}
v___jp_1775_:
{
lean_object* v___x_1779_; 
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 1, v___y_1777_);
lean_ctor_set(v___x_1765_, 0, v___y_1776_);
v___x_1779_ = v___x_1765_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___y_1776_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v___y_1777_);
v___x_1779_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v_pos2traces_1783_; lean_object* v___x_1785_; 
v___x_1780_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1781_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1763_, v___x_1779_, v___x_1780_);
v___x_1782_ = lean_array_push(v___x_1781_, v_msg_1770_);
v_pos2traces_1783_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1763_, v___x_1779_, v___x_1782_);
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 1, v_pos2traces_1783_);
lean_ctor_set(v___x_1772_, 0, v___x_1774_);
v___x_1785_ = v___x_1772_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___x_1774_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v_pos2traces_1783_);
v___x_1785_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
size_t v___x_1786_; size_t v___x_1787_; 
v___x_1786_ = ((size_t)1ULL);
v___x_1787_ = lean_usize_add(v_i_1757_, v___x_1786_);
v_i_1757_ = v___x_1787_;
v_b_1758_ = v___x_1785_;
goto _start;
}
}
}
v___jp_1792_:
{
lean_object* v___x_1794_; 
v___x_1794_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1791_, v___x_1754_);
lean_dec(v_ref_1791_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_inc(v___y_1793_);
v___y_1776_ = v___y_1793_;
v___y_1777_ = v___y_1793_;
goto v___jp_1775_;
}
else
{
lean_object* v_val_1795_; 
v_val_1795_ = lean_ctor_get(v___x_1794_, 0);
lean_inc(v_val_1795_);
lean_dec_ref_known(v___x_1794_, 1);
v___y_1776_ = v___y_1793_;
v___y_1777_ = v_val_1795_;
goto v___jp_1775_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg___boxed(lean_object* v___x_1802_, lean_object* v_as_1803_, lean_object* v_sz_1804_, lean_object* v_i_1805_, lean_object* v_b_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
uint8_t v___x_37558__boxed_1809_; size_t v_sz_boxed_1810_; size_t v_i_boxed_1811_; lean_object* v_res_1812_; 
v___x_37558__boxed_1809_ = lean_unbox(v___x_1802_);
v_sz_boxed_1810_ = lean_unbox_usize(v_sz_1804_);
lean_dec(v_sz_1804_);
v_i_boxed_1811_ = lean_unbox_usize(v_i_1805_);
lean_dec(v_i_1805_);
v_res_1812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_37558__boxed_1809_, v_as_1803_, v_sz_boxed_1810_, v_i_boxed_1811_, v_b_1806_, v___y_1807_);
lean_dec_ref(v___y_1807_);
lean_dec_ref(v_as_1803_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(uint8_t v___x_1813_, lean_object* v_as_1814_, size_t v_sz_1815_, size_t v_i_1816_, lean_object* v_b_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
uint8_t v___x_1821_; 
v___x_1821_ = lean_usize_dec_lt(v_i_1816_, v_sz_1815_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; 
v___x_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1822_, 0, v_b_1817_);
return v___x_1822_;
}
else
{
lean_object* v_snd_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1860_; 
v_snd_1823_ = lean_ctor_get(v_b_1817_, 1);
v_isSharedCheck_1860_ = !lean_is_exclusive(v_b_1817_);
if (v_isSharedCheck_1860_ == 0)
{
lean_object* v_unused_1861_; 
v_unused_1861_ = lean_ctor_get(v_b_1817_, 0);
lean_dec(v_unused_1861_);
v___x_1825_ = v_b_1817_;
v_isShared_1826_ = v_isSharedCheck_1860_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_snd_1823_);
lean_dec(v_b_1817_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1860_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v_ref_1827_; lean_object* v_a_1828_; lean_object* v_ref_1829_; lean_object* v_msg_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1859_; 
v_ref_1827_ = lean_ctor_get(v___y_1818_, 5);
v_a_1828_ = lean_array_uget(v_as_1814_, v_i_1816_);
v_ref_1829_ = lean_ctor_get(v_a_1828_, 0);
v_msg_1830_ = lean_ctor_get(v_a_1828_, 1);
v_isSharedCheck_1859_ = !lean_is_exclusive(v_a_1828_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1832_ = v_a_1828_;
v_isShared_1833_ = v_isSharedCheck_1859_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_msg_1830_);
lean_inc(v_ref_1829_);
lean_dec(v_a_1828_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1859_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1834_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v_ref_1851_; lean_object* v___y_1853_; lean_object* v___x_1856_; 
v___x_1834_ = lean_box(0);
v_ref_1851_ = l_Lean_replaceRef(v_ref_1829_, v_ref_1827_);
lean_dec(v_ref_1829_);
v___x_1856_ = l_Lean_Syntax_getPos_x3f(v_ref_1851_, v___x_1813_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v___x_1857_; 
v___x_1857_ = lean_unsigned_to_nat(0u);
v___y_1853_ = v___x_1857_;
goto v___jp_1852_;
}
else
{
lean_object* v_val_1858_; 
v_val_1858_ = lean_ctor_get(v___x_1856_, 0);
lean_inc(v_val_1858_);
lean_dec_ref_known(v___x_1856_, 1);
v___y_1853_ = v_val_1858_;
goto v___jp_1852_;
}
v___jp_1835_:
{
lean_object* v___x_1839_; 
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 1, v___y_1837_);
lean_ctor_set(v___x_1825_, 0, v___y_1836_);
v___x_1839_ = v___x_1825_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___y_1836_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v___y_1837_);
v___x_1839_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v_pos2traces_1843_; lean_object* v___x_1845_; 
v___x_1840_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1841_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1823_, v___x_1839_, v___x_1840_);
v___x_1842_ = lean_array_push(v___x_1841_, v_msg_1830_);
v_pos2traces_1843_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1823_, v___x_1839_, v___x_1842_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 1, v_pos2traces_1843_);
lean_ctor_set(v___x_1832_, 0, v___x_1834_);
v___x_1845_ = v___x_1832_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v___x_1834_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v_pos2traces_1843_);
v___x_1845_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
size_t v___x_1846_; size_t v___x_1847_; lean_object* v___x_1848_; 
v___x_1846_ = ((size_t)1ULL);
v___x_1847_ = lean_usize_add(v_i_1816_, v___x_1846_);
v___x_1848_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_1813_, v_as_1814_, v_sz_1815_, v___x_1847_, v___x_1845_, v___y_1818_);
return v___x_1848_;
}
}
}
v___jp_1852_:
{
lean_object* v___x_1854_; 
v___x_1854_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1851_, v___x_1813_);
lean_dec(v_ref_1851_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_inc(v___y_1853_);
v___y_1836_ = v___y_1853_;
v___y_1837_ = v___y_1853_;
goto v___jp_1835_;
}
else
{
lean_object* v_val_1855_; 
v_val_1855_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_val_1855_);
lean_dec_ref_known(v___x_1854_, 1);
v___y_1836_ = v___y_1853_;
v___y_1837_ = v_val_1855_;
goto v___jp_1835_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28___boxed(lean_object* v___x_1862_, lean_object* v_as_1863_, lean_object* v_sz_1864_, lean_object* v_i_1865_, lean_object* v_b_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
uint8_t v___x_37638__boxed_1870_; size_t v_sz_boxed_1871_; size_t v_i_boxed_1872_; lean_object* v_res_1873_; 
v___x_37638__boxed_1870_ = lean_unbox(v___x_1862_);
v_sz_boxed_1871_ = lean_unbox_usize(v_sz_1864_);
lean_dec(v_sz_1864_);
v_i_boxed_1872_ = lean_unbox_usize(v_i_1865_);
lean_dec(v_i_1865_);
v_res_1873_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(v___x_37638__boxed_1870_, v_as_1863_, v_sz_boxed_1871_, v_i_boxed_1872_, v_b_1866_, v___y_1867_, v___y_1868_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec_ref(v_as_1863_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(uint8_t v___x_1874_, lean_object* v_t_1875_, lean_object* v_init_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v_root_1880_; lean_object* v_tail_1881_; lean_object* v___x_1882_; 
v_root_1880_ = lean_ctor_get(v_t_1875_, 0);
v_tail_1881_ = lean_ctor_get(v_t_1875_, 1);
lean_inc_ref(v_init_1876_);
v___x_1882_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1876_, v___x_1874_, v_root_1880_, v_init_1876_, v___y_1877_, v___y_1878_);
lean_dec_ref(v_init_1876_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1919_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1885_ = v___x_1882_;
v_isShared_1886_ = v_isSharedCheck_1919_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1882_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1919_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
if (lean_obj_tag(v_a_1883_) == 0)
{
lean_object* v_a_1887_; lean_object* v___x_1889_; 
v_a_1887_ = lean_ctor_get(v_a_1883_, 0);
lean_inc(v_a_1887_);
lean_dec_ref_known(v_a_1883_, 1);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v_a_1887_);
v___x_1889_ = v___x_1885_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1887_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; size_t v_sz_1894_; size_t v___x_1895_; lean_object* v___x_1896_; 
lean_del_object(v___x_1885_);
v_a_1891_ = lean_ctor_get(v_a_1883_, 0);
lean_inc(v_a_1891_);
lean_dec_ref_known(v_a_1883_, 1);
v___x_1892_ = lean_box(0);
v___x_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
lean_ctor_set(v___x_1893_, 1, v_a_1891_);
v_sz_1894_ = lean_array_size(v_tail_1881_);
v___x_1895_ = ((size_t)0ULL);
v___x_1896_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(v___x_1874_, v_tail_1881_, v_sz_1894_, v___x_1895_, v___x_1893_, v___y_1877_, v___y_1878_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1910_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1899_ = v___x_1896_;
v_isShared_1900_ = v_isSharedCheck_1910_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1896_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1910_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v_fst_1901_; 
v_fst_1901_ = lean_ctor_get(v_a_1897_, 0);
if (lean_obj_tag(v_fst_1901_) == 0)
{
lean_object* v_snd_1902_; lean_object* v___x_1904_; 
v_snd_1902_ = lean_ctor_get(v_a_1897_, 1);
lean_inc(v_snd_1902_);
lean_dec(v_a_1897_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v_snd_1902_);
v___x_1904_ = v___x_1899_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_snd_1902_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
else
{
lean_object* v_val_1906_; lean_object* v___x_1908_; 
lean_inc_ref(v_fst_1901_);
lean_dec(v_a_1897_);
v_val_1906_ = lean_ctor_get(v_fst_1901_, 0);
lean_inc(v_val_1906_);
lean_dec_ref_known(v_fst_1901_, 1);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v_val_1906_);
v___x_1908_ = v___x_1899_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_val_1906_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
}
else
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
v_a_1911_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1913_ = v___x_1896_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1896_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
}
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
v_a_1920_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1882_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1882_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19___boxed(lean_object* v___x_1928_, lean_object* v_t_1929_, lean_object* v_init_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
uint8_t v___x_37719__boxed_1934_; lean_object* v_res_1935_; 
v___x_37719__boxed_1934_ = lean_unbox(v___x_1928_);
v_res_1935_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(v___x_37719__boxed_1934_, v_t_1929_, v_init_1930_, v___y_1931_, v___y_1932_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec_ref(v_t_1929_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(lean_object* v_x_1936_, lean_object* v_x_1937_){
_start:
{
if (lean_obj_tag(v_x_1937_) == 0)
{
return v_x_1936_;
}
else
{
lean_object* v_key_1938_; lean_object* v_value_1939_; lean_object* v_tail_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v_key_1938_ = lean_ctor_get(v_x_1937_, 0);
v_value_1939_ = lean_ctor_get(v_x_1937_, 1);
v_tail_1940_ = lean_ctor_get(v_x_1937_, 2);
lean_inc(v_value_1939_);
lean_inc(v_key_1938_);
v___x_1941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1941_, 0, v_key_1938_);
lean_ctor_set(v___x_1941_, 1, v_value_1939_);
v___x_1942_ = lean_array_push(v_x_1936_, v___x_1941_);
v_x_1936_ = v___x_1942_;
v_x_1937_ = v_tail_1940_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22___boxed(lean_object* v_x_1944_, lean_object* v_x_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(v_x_1944_, v_x_1945_);
lean_dec(v_x_1945_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(lean_object* v_as_1947_, size_t v_i_1948_, size_t v_stop_1949_, lean_object* v_b_1950_){
_start:
{
uint8_t v___x_1951_; 
v___x_1951_ = lean_usize_dec_eq(v_i_1948_, v_stop_1949_);
if (v___x_1951_ == 0)
{
lean_object* v___x_1952_; lean_object* v___x_1953_; size_t v___x_1954_; size_t v___x_1955_; 
v___x_1952_ = lean_array_uget_borrowed(v_as_1947_, v_i_1948_);
v___x_1953_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(v_b_1950_, v___x_1952_);
v___x_1954_ = ((size_t)1ULL);
v___x_1955_ = lean_usize_add(v_i_1948_, v___x_1954_);
v_i_1948_ = v___x_1955_;
v_b_1950_ = v___x_1953_;
goto _start;
}
else
{
return v_b_1950_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23___boxed(lean_object* v_as_1957_, lean_object* v_i_1958_, lean_object* v_stop_1959_, lean_object* v_b_1960_){
_start:
{
size_t v_i_boxed_1961_; size_t v_stop_boxed_1962_; lean_object* v_res_1963_; 
v_i_boxed_1961_ = lean_unbox_usize(v_i_1958_);
lean_dec(v_i_1958_);
v_stop_boxed_1962_ = lean_unbox_usize(v_stop_1959_);
lean_dec(v_stop_1959_);
v_res_1963_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_as_1957_, v_i_boxed_1961_, v_stop_boxed_1962_, v_b_1960_);
lean_dec_ref(v_as_1957_);
return v_res_1963_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0(void){
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
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1(void){
_start:
{
size_t v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1967_ = ((size_t)5ULL);
v___x_1968_ = lean_unsigned_to_nat(0u);
v___x_1969_ = lean_unsigned_to_nat(32u);
v___x_1970_ = lean_mk_empty_array_with_capacity(v___x_1969_);
v___x_1971_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0);
v___x_1972_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1972_, 0, v___x_1971_);
lean_ctor_set(v___x_1972_, 1, v___x_1970_);
lean_ctor_set(v___x_1972_, 2, v___x_1968_);
lean_ctor_set(v___x_1972_, 3, v___x_1968_);
lean_ctor_set_usize(v___x_1972_, 4, v___x_1967_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(lean_object* v___y_1973_){
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
v___x_1995_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
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
v___x_2000_ = lean_st_ref_set(v___y_1973_, v___x_1999_);
v___x_2001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2001_, 0, v_traces_1977_);
return v___x_2001_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___boxed(lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_2007_);
lean_dec(v___y_2007_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(lean_object* v_hi_2010_, lean_object* v_pivot_2011_, lean_object* v_as_2012_, lean_object* v_i_2013_, lean_object* v_k_2014_){
_start:
{
uint8_t v___x_2015_; 
v___x_2015_ = lean_nat_dec_lt(v_k_2014_, v_hi_2010_);
if (v___x_2015_ == 0)
{
lean_object* v___x_2016_; lean_object* v___x_2017_; 
lean_dec(v_k_2014_);
v___x_2016_ = lean_array_fswap(v_as_2012_, v_i_2013_, v_hi_2010_);
v___x_2017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2017_, 0, v_i_2013_);
lean_ctor_set(v___x_2017_, 1, v___x_2016_);
return v___x_2017_;
}
else
{
lean_object* v___x_2018_; lean_object* v_fst_2019_; lean_object* v_fst_2020_; lean_object* v_fst_2021_; lean_object* v_fst_2022_; uint8_t v___x_2023_; 
v___x_2018_ = lean_array_fget_borrowed(v_as_2012_, v_k_2014_);
v_fst_2019_ = lean_ctor_get(v___x_2018_, 0);
v_fst_2020_ = lean_ctor_get(v_pivot_2011_, 0);
v_fst_2021_ = lean_ctor_get(v_fst_2019_, 0);
v_fst_2022_ = lean_ctor_get(v_fst_2020_, 0);
v___x_2023_ = lean_nat_dec_lt(v_fst_2021_, v_fst_2022_);
if (v___x_2023_ == 0)
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2024_ = lean_unsigned_to_nat(1u);
v___x_2025_ = lean_nat_add(v_k_2014_, v___x_2024_);
lean_dec(v_k_2014_);
v_k_2014_ = v___x_2025_;
goto _start;
}
else
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2027_ = lean_array_fswap(v_as_2012_, v_i_2013_, v_k_2014_);
v___x_2028_ = lean_unsigned_to_nat(1u);
v___x_2029_ = lean_nat_add(v_i_2013_, v___x_2028_);
lean_dec(v_i_2013_);
v___x_2030_ = lean_nat_add(v_k_2014_, v___x_2028_);
lean_dec(v_k_2014_);
v_as_2012_ = v___x_2027_;
v_i_2013_ = v___x_2029_;
v_k_2014_ = v___x_2030_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg___boxed(lean_object* v_hi_2032_, lean_object* v_pivot_2033_, lean_object* v_as_2034_, lean_object* v_i_2035_, lean_object* v_k_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_2032_, v_pivot_2033_, v_as_2034_, v_i_2035_, v_k_2036_);
lean_dec_ref(v_pivot_2033_);
lean_dec(v_hi_2032_);
return v_res_2037_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(lean_object* v_x_2038_, lean_object* v_x_2039_){
_start:
{
lean_object* v_fst_2040_; lean_object* v_fst_2041_; lean_object* v_fst_2042_; lean_object* v_fst_2043_; uint8_t v___x_2044_; 
v_fst_2040_ = lean_ctor_get(v_x_2038_, 0);
v_fst_2041_ = lean_ctor_get(v_x_2039_, 0);
v_fst_2042_ = lean_ctor_get(v_fst_2040_, 0);
v_fst_2043_ = lean_ctor_get(v_fst_2041_, 0);
v___x_2044_ = lean_nat_dec_lt(v_fst_2042_, v_fst_2043_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0___boxed(lean_object* v_x_2045_, lean_object* v_x_2046_){
_start:
{
uint8_t v_res_2047_; lean_object* v_r_2048_; 
v_res_2047_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v_x_2045_, v_x_2046_);
lean_dec_ref(v_x_2046_);
lean_dec_ref(v_x_2045_);
v_r_2048_ = lean_box(v_res_2047_);
return v_r_2048_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(lean_object* v_n_2049_, lean_object* v_as_2050_, lean_object* v_lo_2051_, lean_object* v_hi_2052_){
_start:
{
lean_object* v___y_2054_; uint8_t v___x_2064_; 
v___x_2064_ = lean_nat_dec_lt(v_lo_2051_, v_hi_2052_);
if (v___x_2064_ == 0)
{
lean_dec(v_lo_2051_);
return v_as_2050_;
}
else
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v_mid_2067_; lean_object* v___y_2069_; lean_object* v___y_2075_; lean_object* v___x_2080_; lean_object* v___x_2081_; uint8_t v___x_2082_; 
v___x_2065_ = lean_nat_add(v_lo_2051_, v_hi_2052_);
v___x_2066_ = lean_unsigned_to_nat(1u);
v_mid_2067_ = lean_nat_shiftr(v___x_2065_, v___x_2066_);
lean_dec(v___x_2065_);
v___x_2080_ = lean_array_fget_borrowed(v_as_2050_, v_mid_2067_);
v___x_2081_ = lean_array_fget_borrowed(v_as_2050_, v_lo_2051_);
v___x_2082_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2080_, v___x_2081_);
if (v___x_2082_ == 0)
{
v___y_2075_ = v_as_2050_;
goto v___jp_2074_;
}
else
{
lean_object* v___x_2083_; 
v___x_2083_ = lean_array_fswap(v_as_2050_, v_lo_2051_, v_mid_2067_);
v___y_2075_ = v___x_2083_;
goto v___jp_2074_;
}
v___jp_2068_:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; 
v___x_2070_ = lean_array_fget_borrowed(v___y_2069_, v_mid_2067_);
v___x_2071_ = lean_array_fget_borrowed(v___y_2069_, v_hi_2052_);
v___x_2072_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2070_, v___x_2071_);
if (v___x_2072_ == 0)
{
lean_dec(v_mid_2067_);
v___y_2054_ = v___y_2069_;
goto v___jp_2053_;
}
else
{
lean_object* v___x_2073_; 
v___x_2073_ = lean_array_fswap(v___y_2069_, v_mid_2067_, v_hi_2052_);
lean_dec(v_mid_2067_);
v___y_2054_ = v___x_2073_;
goto v___jp_2053_;
}
}
v___jp_2074_:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; uint8_t v___x_2078_; 
v___x_2076_ = lean_array_fget_borrowed(v___y_2075_, v_hi_2052_);
v___x_2077_ = lean_array_fget_borrowed(v___y_2075_, v_lo_2051_);
v___x_2078_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2076_, v___x_2077_);
if (v___x_2078_ == 0)
{
v___y_2069_ = v___y_2075_;
goto v___jp_2068_;
}
else
{
lean_object* v___x_2079_; 
v___x_2079_ = lean_array_fswap(v___y_2075_, v_lo_2051_, v_hi_2052_);
v___y_2069_ = v___x_2079_;
goto v___jp_2068_;
}
}
}
v___jp_2053_:
{
lean_object* v_pivot_2055_; lean_object* v___x_2056_; lean_object* v_fst_2057_; lean_object* v_snd_2058_; uint8_t v___x_2059_; 
v_pivot_2055_ = lean_array_fget(v___y_2054_, v_hi_2052_);
lean_inc_n(v_lo_2051_, 2);
v___x_2056_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_2052_, v_pivot_2055_, v___y_2054_, v_lo_2051_, v_lo_2051_);
lean_dec(v_pivot_2055_);
v_fst_2057_ = lean_ctor_get(v___x_2056_, 0);
lean_inc(v_fst_2057_);
v_snd_2058_ = lean_ctor_get(v___x_2056_, 1);
lean_inc(v_snd_2058_);
lean_dec_ref(v___x_2056_);
v___x_2059_ = lean_nat_dec_le(v_hi_2052_, v_fst_2057_);
if (v___x_2059_ == 0)
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2060_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_2049_, v_snd_2058_, v_lo_2051_, v_fst_2057_);
v___x_2061_ = lean_unsigned_to_nat(1u);
v___x_2062_ = lean_nat_add(v_fst_2057_, v___x_2061_);
lean_dec(v_fst_2057_);
v_as_2050_ = v___x_2060_;
v_lo_2051_ = v___x_2062_;
goto _start;
}
else
{
lean_dec(v_fst_2057_);
lean_dec(v_lo_2051_);
return v_snd_2058_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___boxed(lean_object* v_n_2084_, lean_object* v_as_2085_, lean_object* v_lo_2086_, lean_object* v_hi_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_2084_, v_as_2085_, v_lo_2086_, v_hi_2087_);
lean_dec(v_hi_2087_);
lean_dec(v_n_2084_);
return v_res_2088_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0(void){
_start:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2089_ = lean_box(0);
v___x_2090_ = lean_unsigned_to_nat(16u);
v___x_2091_ = lean_mk_array(v___x_2090_, v___x_2089_);
return v___x_2091_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1(void){
_start:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v_pos2traces_2094_; 
v___x_2092_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0, &l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0);
v___x_2093_ = lean_unsigned_to_nat(0u);
v_pos2traces_2094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos2traces_2094_, 0, v___x_2093_);
lean_ctor_set(v_pos2traces_2094_, 1, v___x_2092_);
return v_pos2traces_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10(lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v_options_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v_options_2101_ = lean_ctor_get(v___y_2095_, 2);
v___x_2102_ = l_Lean_trace_profiler_output;
v___x_2103_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(v_options_2101_, v___x_2102_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v___x_2104_; uint8_t v___x_2105_; 
v___x_2104_ = l_Lean_trace_profiler_serve;
v___x_2105_ = l_Lean_Option_get___at___00main_spec__8(v_options_2101_, v___x_2104_);
if (v___x_2105_ == 0)
{
lean_object* v___x_2106_; lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2173_; 
v___x_2106_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_2096_);
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2109_ = v___x_2106_;
v_isShared_2110_ = v_isSharedCheck_2173_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2106_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2173_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
uint8_t v___x_2111_; 
v___x_2111_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_2107_);
if (v___x_2111_ == 0)
{
lean_object* v___x_2112_; lean_object* v_pos2traces_2113_; lean_object* v___x_2114_; 
lean_del_object(v___x_2109_);
v___x_2112_ = lean_unsigned_to_nat(0u);
v_pos2traces_2113_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1, &l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1);
v___x_2114_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(v___x_2111_, v_a_2107_, v_pos2traces_2113_, v___y_2095_, v___y_2096_);
lean_dec(v_a_2107_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; lean_object* v___y_2117_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2143_; lean_object* v_size_2149_; lean_object* v_buckets_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; uint8_t v___x_2153_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2115_);
lean_dec_ref_known(v___x_2114_, 1);
v_size_2149_ = lean_ctor_get(v_a_2115_, 0);
lean_inc(v_size_2149_);
v_buckets_2150_ = lean_ctor_get(v_a_2115_, 1);
lean_inc_ref(v_buckets_2150_);
lean_dec(v_a_2115_);
v___x_2151_ = lean_mk_empty_array_with_capacity(v_size_2149_);
lean_dec(v_size_2149_);
v___x_2152_ = lean_array_get_size(v_buckets_2150_);
v___x_2153_ = lean_nat_dec_lt(v___x_2112_, v___x_2152_);
if (v___x_2153_ == 0)
{
lean_dec_ref(v_buckets_2150_);
v___y_2143_ = v___x_2151_;
goto v___jp_2142_;
}
else
{
uint8_t v___x_2154_; 
v___x_2154_ = lean_nat_dec_le(v___x_2152_, v___x_2152_);
if (v___x_2154_ == 0)
{
if (v___x_2153_ == 0)
{
lean_dec_ref(v_buckets_2150_);
v___y_2143_ = v___x_2151_;
goto v___jp_2142_;
}
else
{
size_t v___x_2155_; size_t v___x_2156_; lean_object* v___x_2157_; 
v___x_2155_ = ((size_t)0ULL);
v___x_2156_ = lean_usize_of_nat(v___x_2152_);
v___x_2157_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_buckets_2150_, v___x_2155_, v___x_2156_, v___x_2151_);
lean_dec_ref(v_buckets_2150_);
v___y_2143_ = v___x_2157_;
goto v___jp_2142_;
}
}
else
{
size_t v___x_2158_; size_t v___x_2159_; lean_object* v___x_2160_; 
v___x_2158_ = ((size_t)0ULL);
v___x_2159_ = lean_usize_of_nat(v___x_2152_);
v___x_2160_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_buckets_2150_, v___x_2158_, v___x_2159_, v___x_2151_);
lean_dec_ref(v_buckets_2150_);
v___y_2143_ = v___x_2160_;
goto v___jp_2142_;
}
}
v___jp_2116_:
{
lean_object* v___x_2118_; size_t v_sz_2119_; size_t v___x_2120_; lean_object* v___x_2121_; 
v___x_2118_ = lean_box(0);
v_sz_2119_ = lean_array_size(v___y_2117_);
v___x_2120_ = ((size_t)0ULL);
v___x_2121_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(v___x_2105_, v___y_2117_, v_sz_2119_, v___x_2120_, v___x_2118_, v___y_2095_, v___y_2096_);
lean_dec_ref(v___y_2117_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2128_ == 0)
{
lean_object* v_unused_2129_; 
v_unused_2129_ = lean_ctor_get(v___x_2121_, 0);
lean_dec(v_unused_2129_);
v___x_2123_ = v___x_2121_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_dec(v___x_2121_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 0, v___x_2118_);
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2118_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
else
{
return v___x_2121_;
}
}
v___jp_2130_:
{
lean_object* v___x_2135_; 
v___x_2135_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v___y_2132_, v___y_2131_, v___y_2133_, v___y_2134_);
lean_dec(v___y_2134_);
lean_dec(v___y_2132_);
v___y_2117_ = v___x_2135_;
goto v___jp_2116_;
}
v___jp_2136_:
{
uint8_t v___x_2141_; 
v___x_2141_ = lean_nat_dec_le(v___y_2140_, v___y_2137_);
if (v___x_2141_ == 0)
{
lean_dec(v___y_2137_);
lean_inc(v___y_2140_);
v___y_2131_ = v___y_2138_;
v___y_2132_ = v___y_2139_;
v___y_2133_ = v___y_2140_;
v___y_2134_ = v___y_2140_;
goto v___jp_2130_;
}
else
{
v___y_2131_ = v___y_2138_;
v___y_2132_ = v___y_2139_;
v___y_2133_ = v___y_2140_;
v___y_2134_ = v___y_2137_;
goto v___jp_2130_;
}
}
v___jp_2142_:
{
lean_object* v___x_2144_; uint8_t v___x_2145_; 
v___x_2144_ = lean_array_get_size(v___y_2143_);
v___x_2145_ = lean_nat_dec_eq(v___x_2144_, v___x_2112_);
if (v___x_2145_ == 0)
{
lean_object* v___x_2146_; lean_object* v___x_2147_; uint8_t v___x_2148_; 
v___x_2146_ = lean_unsigned_to_nat(1u);
v___x_2147_ = lean_nat_sub(v___x_2144_, v___x_2146_);
v___x_2148_ = lean_nat_dec_le(v___x_2112_, v___x_2147_);
if (v___x_2148_ == 0)
{
lean_inc(v___x_2147_);
v___y_2137_ = v___x_2147_;
v___y_2138_ = v___y_2143_;
v___y_2139_ = v___x_2144_;
v___y_2140_ = v___x_2147_;
goto v___jp_2136_;
}
else
{
v___y_2137_ = v___x_2147_;
v___y_2138_ = v___y_2143_;
v___y_2139_ = v___x_2144_;
v___y_2140_ = v___x_2112_;
goto v___jp_2136_;
}
}
else
{
v___y_2117_ = v___y_2143_;
goto v___jp_2116_;
}
}
}
else
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2168_; 
v_a_2161_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2163_ = v___x_2114_;
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2114_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2166_; 
if (v_isShared_2164_ == 0)
{
v___x_2166_ = v___x_2163_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_a_2161_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
}
else
{
lean_object* v___x_2169_; lean_object* v___x_2171_; 
lean_dec(v_a_2107_);
v___x_2169_ = lean_box(0);
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 0, v___x_2169_);
v___x_2171_ = v___x_2109_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2169_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
else
{
goto v___jp_2098_;
}
}
else
{
lean_dec_ref_known(v___x_2103_, 1);
goto v___jp_2098_;
}
v___jp_2098_:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2099_ = lean_box(0);
v___x_2100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2099_);
return v___x_2100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10___boxed(lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2174_, v___y_2175_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(lean_object* v_as_2178_, size_t v_sz_2179_, size_t v_i_2180_, lean_object* v_b_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
uint8_t v___x_2185_; 
v___x_2185_ = lean_usize_dec_lt(v_i_2180_, v_sz_2179_);
if (v___x_2185_ == 0)
{
lean_object* v___x_2186_; 
v___x_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2186_, 0, v_b_2181_);
return v___x_2186_;
}
else
{
lean_object* v_options_2187_; lean_object* v_a_2188_; lean_object* v___x_2189_; 
v_options_2187_ = lean_ctor_get(v___y_2182_, 2);
v_a_2188_ = lean_array_uget_borrowed(v_as_2178_, v_i_2180_);
lean_inc_ref(v_options_2187_);
lean_inc(v_a_2188_);
v___x_2189_ = l_Lean_Compiler_LCNF_resumeCompilation(v_a_2188_, v_options_2187_, v___y_2182_, v___y_2183_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v___x_2190_; 
lean_dec_ref_known(v___x_2189_, 1);
v___x_2190_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2182_, v___y_2183_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v___x_2191_; size_t v___x_2192_; size_t v___x_2193_; 
lean_dec_ref_known(v___x_2190_, 1);
v___x_2191_ = lean_box(0);
v___x_2192_ = ((size_t)1ULL);
v___x_2193_ = lean_usize_add(v_i_2180_, v___x_2192_);
v_i_2180_ = v___x_2193_;
v_b_2181_ = v___x_2191_;
goto _start;
}
else
{
return v___x_2190_;
}
}
else
{
lean_object* v_a_2195_; lean_object* v___x_2196_; 
v_a_2195_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_a_2195_);
lean_dec_ref_known(v___x_2189_, 1);
v___x_2196_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2182_, v___y_2183_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2203_; 
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2203_ == 0)
{
lean_object* v_unused_2204_; 
v_unused_2204_ = lean_ctor_get(v___x_2196_, 0);
lean_dec(v_unused_2204_);
v___x_2198_ = v___x_2196_;
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
else
{
lean_dec(v___x_2196_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
if (v_isShared_2199_ == 0)
{
lean_ctor_set_tag(v___x_2198_, 1);
lean_ctor_set(v___x_2198_, 0, v_a_2195_);
v___x_2201_ = v___x_2198_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_a_2195_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
else
{
lean_dec(v_a_2195_);
return v___x_2196_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11___boxed(lean_object* v_as_2205_, lean_object* v_sz_2206_, lean_object* v_i_2207_, lean_object* v_b_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
size_t v_sz_boxed_2212_; size_t v_i_boxed_2213_; lean_object* v_res_2214_; 
v_sz_boxed_2212_ = lean_unbox_usize(v_sz_2206_);
lean_dec(v_sz_2206_);
v_i_boxed_2213_ = lean_unbox_usize(v_i_2207_);
lean_dec(v_i_2207_);
v_res_2214_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(v_as_2205_, v_sz_boxed_2212_, v_i_boxed_2213_, v_b_2208_, v___y_2209_, v___y_2210_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec_ref(v_as_2205_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(lean_object* v_as_2215_, size_t v_sz_2216_, size_t v_i_2217_, lean_object* v_b_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
uint8_t v___x_2222_; 
v___x_2222_ = lean_usize_dec_lt(v_i_2217_, v_sz_2216_);
if (v___x_2222_ == 0)
{
lean_object* v___x_2223_; 
v___x_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2223_, 0, v_b_2218_);
return v___x_2223_;
}
else
{
lean_object* v_a_2224_; lean_object* v_declNames_2225_; lean_object* v___x_2226_; size_t v_sz_2227_; size_t v___x_2228_; lean_object* v___x_2229_; 
v_a_2224_ = lean_array_uget_borrowed(v_as_2215_, v_i_2217_);
v_declNames_2225_ = lean_ctor_get(v_a_2224_, 0);
v___x_2226_ = lean_box(0);
v_sz_2227_ = lean_array_size(v_declNames_2225_);
v___x_2228_ = ((size_t)0ULL);
v___x_2229_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(v_declNames_2225_, v_sz_2227_, v___x_2228_, v___x_2226_, v___y_2219_, v___y_2220_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v___x_2230_; 
lean_dec_ref_known(v___x_2229_, 1);
v___x_2230_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v___y_2220_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v_a_2231_; lean_object* v_unreported_2232_; lean_object* v___x_2233_; 
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_a_2231_);
lean_dec_ref_known(v___x_2230_, 1);
v_unreported_2232_ = lean_ctor_get(v_a_2231_, 1);
lean_inc_ref(v_unreported_2232_);
lean_dec(v_a_2231_);
v___x_2233_ = l_Lean_PersistentArray_forIn___at___00main_spec__12(v_unreported_2232_, v___x_2226_, v___y_2219_, v___y_2220_);
lean_dec_ref(v_unreported_2232_);
if (lean_obj_tag(v___x_2233_) == 0)
{
size_t v___x_2234_; size_t v___x_2235_; 
lean_dec_ref_known(v___x_2233_, 1);
v___x_2234_ = ((size_t)1ULL);
v___x_2235_ = lean_usize_add(v_i_2217_, v___x_2234_);
v_i_2217_ = v___x_2235_;
v_b_2218_ = v___x_2226_;
goto _start;
}
else
{
return v___x_2233_;
}
}
else
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2244_; 
v_a_2237_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2239_ = v___x_2230_;
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2230_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2242_; 
if (v_isShared_2240_ == 0)
{
v___x_2242_ = v___x_2239_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_a_2237_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
else
{
return v___x_2229_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13___boxed(lean_object* v_as_2245_, lean_object* v_sz_2246_, lean_object* v_i_2247_, lean_object* v_b_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
size_t v_sz_boxed_2252_; size_t v_i_boxed_2253_; lean_object* v_res_2254_; 
v_sz_boxed_2252_ = lean_unbox_usize(v_sz_2246_);
lean_dec(v_sz_2246_);
v_i_boxed_2253_ = lean_unbox_usize(v_i_2247_);
lean_dec(v_i_2247_);
v_res_2254_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(v_as_2245_, v_sz_boxed_2252_, v_i_boxed_2253_, v_b_2248_, v___y_2249_, v___y_2250_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec_ref(v_as_2245_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(lean_object* v_as_2255_, size_t v_i_2256_, size_t v_stop_2257_, lean_object* v_b_2258_){
_start:
{
uint8_t v___x_2259_; 
v___x_2259_ = lean_usize_dec_eq(v_i_2256_, v_stop_2257_);
if (v___x_2259_ == 0)
{
lean_object* v___x_2260_; lean_object* v_name_2261_; lean_object* v___x_2262_; size_t v___x_2263_; size_t v___x_2264_; 
v___x_2260_ = lean_array_uget_borrowed(v_as_2255_, v_i_2256_);
v_name_2261_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_name_2261_);
v___x_2262_ = l_Lean_Compiler_LCNF_setDeclPublic(v_b_2258_, v_name_2261_);
v___x_2263_ = ((size_t)1ULL);
v___x_2264_ = lean_usize_add(v_i_2256_, v___x_2263_);
v_i_2256_ = v___x_2264_;
v_b_2258_ = v___x_2262_;
goto _start;
}
else
{
return v_b_2258_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___boxed(lean_object* v_as_2266_, lean_object* v_i_2267_, lean_object* v_stop_2268_, lean_object* v_b_2269_){
_start:
{
size_t v_i_boxed_2270_; size_t v_stop_boxed_2271_; lean_object* v_res_2272_; 
v_i_boxed_2270_ = lean_unbox_usize(v_i_2267_);
lean_dec(v_i_2267_);
v_stop_boxed_2271_ = lean_unbox_usize(v_stop_2268_);
lean_dec(v_stop_2268_);
v_res_2272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v_as_2266_, v_i_boxed_2270_, v_stop_boxed_2271_, v_b_2269_);
lean_dec_ref(v_as_2266_);
return v_res_2272_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0(uint8_t v___y_2273_, uint8_t v_suppressElabErrors_2274_, lean_object* v_x_2275_){
_start:
{
if (lean_obj_tag(v_x_2275_) == 1)
{
lean_object* v_pre_2276_; 
v_pre_2276_ = lean_ctor_get(v_x_2275_, 0);
switch(lean_obj_tag(v_pre_2276_))
{
case 1:
{
lean_object* v_pre_2277_; 
v_pre_2277_ = lean_ctor_get(v_pre_2276_, 0);
switch(lean_obj_tag(v_pre_2277_))
{
case 0:
{
lean_object* v_str_2278_; lean_object* v_str_2279_; lean_object* v___x_2280_; uint8_t v___x_2281_; 
v_str_2278_ = lean_ctor_get(v_x_2275_, 1);
v_str_2279_ = lean_ctor_get(v_pre_2276_, 1);
v___x_2280_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0));
v___x_2281_ = lean_string_dec_eq(v_str_2279_, v___x_2280_);
if (v___x_2281_ == 0)
{
lean_object* v___x_2282_; uint8_t v___x_2283_; 
v___x_2282_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1));
v___x_2283_ = lean_string_dec_eq(v_str_2279_, v___x_2282_);
if (v___x_2283_ == 0)
{
return v___y_2273_;
}
else
{
lean_object* v___x_2284_; uint8_t v___x_2285_; 
v___x_2284_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2));
v___x_2285_ = lean_string_dec_eq(v_str_2278_, v___x_2284_);
if (v___x_2285_ == 0)
{
return v___y_2273_;
}
else
{
return v_suppressElabErrors_2274_;
}
}
}
else
{
lean_object* v___x_2286_; uint8_t v___x_2287_; 
v___x_2286_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3));
v___x_2287_ = lean_string_dec_eq(v_str_2278_, v___x_2286_);
if (v___x_2287_ == 0)
{
return v___y_2273_;
}
else
{
return v_suppressElabErrors_2274_;
}
}
}
case 1:
{
lean_object* v_pre_2288_; 
v_pre_2288_ = lean_ctor_get(v_pre_2277_, 0);
if (lean_obj_tag(v_pre_2288_) == 0)
{
lean_object* v_str_2289_; lean_object* v_str_2290_; lean_object* v_str_2291_; lean_object* v___x_2292_; uint8_t v___x_2293_; 
v_str_2289_ = lean_ctor_get(v_x_2275_, 1);
v_str_2290_ = lean_ctor_get(v_pre_2276_, 1);
v_str_2291_ = lean_ctor_get(v_pre_2277_, 1);
v___x_2292_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4));
v___x_2293_ = lean_string_dec_eq(v_str_2291_, v___x_2292_);
if (v___x_2293_ == 0)
{
return v___y_2273_;
}
else
{
lean_object* v___x_2294_; uint8_t v___x_2295_; 
v___x_2294_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5));
v___x_2295_ = lean_string_dec_eq(v_str_2290_, v___x_2294_);
if (v___x_2295_ == 0)
{
return v___y_2273_;
}
else
{
lean_object* v___x_2296_; uint8_t v___x_2297_; 
v___x_2296_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6));
v___x_2297_ = lean_string_dec_eq(v_str_2289_, v___x_2296_);
if (v___x_2297_ == 0)
{
return v___y_2273_;
}
else
{
return v_suppressElabErrors_2274_;
}
}
}
}
else
{
return v___y_2273_;
}
}
default: 
{
return v___y_2273_;
}
}
}
case 0:
{
lean_object* v_str_2298_; lean_object* v___x_2299_; uint8_t v___x_2300_; 
v_str_2298_ = lean_ctor_get(v_x_2275_, 1);
v___x_2299_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_2300_ = lean_string_dec_eq(v_str_2298_, v___x_2299_);
if (v___x_2300_ == 0)
{
return v___y_2273_;
}
else
{
return v_suppressElabErrors_2274_;
}
}
default: 
{
return v___y_2273_;
}
}
}
else
{
return v___y_2273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0___boxed(lean_object* v___y_2301_, lean_object* v_suppressElabErrors_2302_, lean_object* v_x_2303_){
_start:
{
uint8_t v___y_38323__boxed_2304_; uint8_t v_suppressElabErrors_boxed_2305_; uint8_t v_res_2306_; lean_object* v_r_2307_; 
v___y_38323__boxed_2304_ = lean_unbox(v___y_2301_);
v_suppressElabErrors_boxed_2305_ = lean_unbox(v_suppressElabErrors_2302_);
v_res_2306_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0(v___y_38323__boxed_2304_, v_suppressElabErrors_boxed_2305_, v_x_2303_);
lean_dec(v_x_2303_);
v_r_2307_ = lean_box(v_res_2306_);
return v_r_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(lean_object* v_ref_2308_, lean_object* v_msgData_2309_, uint8_t v_severity_2310_, uint8_t v_isSilent_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v___y_2316_; lean_object* v___y_2317_; uint8_t v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; uint8_t v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v___y_2324_; lean_object* v___y_2352_; lean_object* v___y_2353_; lean_object* v___y_2354_; lean_object* v___y_2355_; uint8_t v___y_2356_; uint8_t v___y_2357_; uint8_t v___y_2358_; lean_object* v___y_2359_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; uint8_t v___y_2381_; uint8_t v___y_2382_; uint8_t v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; uint8_t v___y_2391_; lean_object* v___y_2392_; uint8_t v___y_2393_; uint8_t v___y_2394_; uint8_t v___x_2399_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; uint8_t v___y_2404_; lean_object* v___y_2405_; uint8_t v___y_2406_; uint8_t v___y_2407_; uint8_t v___y_2409_; uint8_t v___x_2424_; 
v___x_2399_ = 2;
v___x_2424_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2310_, v___x_2399_);
if (v___x_2424_ == 0)
{
v___y_2409_ = v___x_2424_;
goto v___jp_2408_;
}
else
{
uint8_t v___x_2425_; 
lean_inc_ref(v_msgData_2309_);
v___x_2425_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2309_);
v___y_2409_ = v___x_2425_;
goto v___jp_2408_;
}
v___jp_2315_:
{
lean_object* v___x_2325_; lean_object* v_currNamespace_2326_; lean_object* v_openDecls_2327_; lean_object* v_env_2328_; lean_object* v_nextMacroScope_2329_; lean_object* v_ngen_2330_; lean_object* v_auxDeclNGen_2331_; lean_object* v_traceState_2332_; lean_object* v_cache_2333_; lean_object* v_messages_2334_; lean_object* v_infoState_2335_; lean_object* v_snapshotTasks_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2350_; 
v___x_2325_ = lean_st_ref_take(v___y_2324_);
v_currNamespace_2326_ = lean_ctor_get(v___y_2323_, 6);
v_openDecls_2327_ = lean_ctor_get(v___y_2323_, 7);
v_env_2328_ = lean_ctor_get(v___x_2325_, 0);
v_nextMacroScope_2329_ = lean_ctor_get(v___x_2325_, 1);
v_ngen_2330_ = lean_ctor_get(v___x_2325_, 2);
v_auxDeclNGen_2331_ = lean_ctor_get(v___x_2325_, 3);
v_traceState_2332_ = lean_ctor_get(v___x_2325_, 4);
v_cache_2333_ = lean_ctor_get(v___x_2325_, 5);
v_messages_2334_ = lean_ctor_get(v___x_2325_, 6);
v_infoState_2335_ = lean_ctor_get(v___x_2325_, 7);
v_snapshotTasks_2336_ = lean_ctor_get(v___x_2325_, 8);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2338_ = v___x_2325_;
v_isShared_2339_ = v_isSharedCheck_2350_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_snapshotTasks_2336_);
lean_inc(v_infoState_2335_);
lean_inc(v_messages_2334_);
lean_inc(v_cache_2333_);
lean_inc(v_traceState_2332_);
lean_inc(v_auxDeclNGen_2331_);
lean_inc(v_ngen_2330_);
lean_inc(v_nextMacroScope_2329_);
lean_inc(v_env_2328_);
lean_dec(v___x_2325_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2350_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2345_; 
lean_inc(v_openDecls_2327_);
lean_inc(v_currNamespace_2326_);
v___x_2340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2340_, 0, v_currNamespace_2326_);
lean_ctor_set(v___x_2340_, 1, v_openDecls_2327_);
v___x_2341_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2340_);
lean_ctor_set(v___x_2341_, 1, v___y_2322_);
lean_inc_ref(v___y_2316_);
lean_inc_ref(v___y_2317_);
v___x_2342_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2342_, 0, v___y_2317_);
lean_ctor_set(v___x_2342_, 1, v___y_2320_);
lean_ctor_set(v___x_2342_, 2, v___y_2319_);
lean_ctor_set(v___x_2342_, 3, v___y_2316_);
lean_ctor_set(v___x_2342_, 4, v___x_2341_);
lean_ctor_set_uint8(v___x_2342_, sizeof(void*)*5, v___y_2318_);
lean_ctor_set_uint8(v___x_2342_, sizeof(void*)*5 + 1, v___y_2321_);
lean_ctor_set_uint8(v___x_2342_, sizeof(void*)*5 + 2, v_isSilent_2311_);
v___x_2343_ = l_Lean_MessageLog_add(v___x_2342_, v_messages_2334_);
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 6, v___x_2343_);
v___x_2345_ = v___x_2338_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_env_2328_);
lean_ctor_set(v_reuseFailAlloc_2349_, 1, v_nextMacroScope_2329_);
lean_ctor_set(v_reuseFailAlloc_2349_, 2, v_ngen_2330_);
lean_ctor_set(v_reuseFailAlloc_2349_, 3, v_auxDeclNGen_2331_);
lean_ctor_set(v_reuseFailAlloc_2349_, 4, v_traceState_2332_);
lean_ctor_set(v_reuseFailAlloc_2349_, 5, v_cache_2333_);
lean_ctor_set(v_reuseFailAlloc_2349_, 6, v___x_2343_);
lean_ctor_set(v_reuseFailAlloc_2349_, 7, v_infoState_2335_);
lean_ctor_set(v_reuseFailAlloc_2349_, 8, v_snapshotTasks_2336_);
v___x_2345_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2346_ = lean_st_ref_set(v___y_2324_, v___x_2345_);
v___x_2347_ = lean_box(0);
v___x_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2347_);
return v___x_2348_;
}
}
}
v___jp_2351_:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2375_; 
v___x_2360_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2309_);
v___x_2361_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(v___x_2360_, v___y_2312_, v___y_2313_);
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2364_ = v___x_2361_;
v_isShared_2365_ = v_isSharedCheck_2375_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2361_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2375_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
lean_inc_ref_n(v___y_2354_, 2);
v___x_2366_ = l_Lean_FileMap_toPosition(v___y_2354_, v___y_2353_);
lean_dec(v___y_2353_);
v___x_2367_ = l_Lean_FileMap_toPosition(v___y_2354_, v___y_2359_);
lean_dec(v___y_2359_);
v___x_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2367_);
v___x_2369_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1));
if (v___y_2358_ == 0)
{
lean_del_object(v___x_2364_);
lean_dec_ref(v___y_2352_);
v___y_2316_ = v___x_2369_;
v___y_2317_ = v___y_2355_;
v___y_2318_ = v___y_2356_;
v___y_2319_ = v___x_2368_;
v___y_2320_ = v___x_2366_;
v___y_2321_ = v___y_2357_;
v___y_2322_ = v_a_2362_;
v___y_2323_ = v___y_2312_;
v___y_2324_ = v___y_2313_;
goto v___jp_2315_;
}
else
{
uint8_t v___x_2370_; 
lean_inc(v_a_2362_);
v___x_2370_ = l_Lean_MessageData_hasTag(v___y_2352_, v_a_2362_);
if (v___x_2370_ == 0)
{
lean_object* v___x_2371_; lean_object* v___x_2373_; 
lean_dec_ref_known(v___x_2368_, 1);
lean_dec_ref(v___x_2366_);
lean_dec(v_a_2362_);
v___x_2371_ = lean_box(0);
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 0, v___x_2371_);
v___x_2373_ = v___x_2364_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2371_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
else
{
lean_del_object(v___x_2364_);
v___y_2316_ = v___x_2369_;
v___y_2317_ = v___y_2355_;
v___y_2318_ = v___y_2356_;
v___y_2319_ = v___x_2368_;
v___y_2320_ = v___x_2366_;
v___y_2321_ = v___y_2357_;
v___y_2322_ = v_a_2362_;
v___y_2323_ = v___y_2312_;
v___y_2324_ = v___y_2313_;
goto v___jp_2315_;
}
}
}
}
v___jp_2376_:
{
lean_object* v___x_2385_; 
v___x_2385_ = l_Lean_Syntax_getTailPos_x3f(v___y_2379_, v___y_2381_);
lean_dec(v___y_2379_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_inc(v___y_2384_);
v___y_2352_ = v___y_2377_;
v___y_2353_ = v___y_2384_;
v___y_2354_ = v___y_2378_;
v___y_2355_ = v___y_2380_;
v___y_2356_ = v___y_2381_;
v___y_2357_ = v___y_2382_;
v___y_2358_ = v___y_2383_;
v___y_2359_ = v___y_2384_;
goto v___jp_2351_;
}
else
{
lean_object* v_val_2386_; 
v_val_2386_ = lean_ctor_get(v___x_2385_, 0);
lean_inc(v_val_2386_);
lean_dec_ref_known(v___x_2385_, 1);
v___y_2352_ = v___y_2377_;
v___y_2353_ = v___y_2384_;
v___y_2354_ = v___y_2378_;
v___y_2355_ = v___y_2380_;
v___y_2356_ = v___y_2381_;
v___y_2357_ = v___y_2382_;
v___y_2358_ = v___y_2383_;
v___y_2359_ = v_val_2386_;
goto v___jp_2351_;
}
}
v___jp_2387_:
{
lean_object* v_ref_2395_; lean_object* v___x_2396_; 
v_ref_2395_ = l_Lean_replaceRef(v_ref_2308_, v___y_2392_);
v___x_2396_ = l_Lean_Syntax_getPos_x3f(v_ref_2395_, v___y_2391_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v___x_2397_; 
v___x_2397_ = lean_unsigned_to_nat(0u);
v___y_2377_ = v___y_2388_;
v___y_2378_ = v___y_2389_;
v___y_2379_ = v_ref_2395_;
v___y_2380_ = v___y_2390_;
v___y_2381_ = v___y_2391_;
v___y_2382_ = v___y_2394_;
v___y_2383_ = v___y_2393_;
v___y_2384_ = v___x_2397_;
goto v___jp_2376_;
}
else
{
lean_object* v_val_2398_; 
v_val_2398_ = lean_ctor_get(v___x_2396_, 0);
lean_inc(v_val_2398_);
lean_dec_ref_known(v___x_2396_, 1);
v___y_2377_ = v___y_2388_;
v___y_2378_ = v___y_2389_;
v___y_2379_ = v_ref_2395_;
v___y_2380_ = v___y_2390_;
v___y_2381_ = v___y_2391_;
v___y_2382_ = v___y_2394_;
v___y_2383_ = v___y_2393_;
v___y_2384_ = v_val_2398_;
goto v___jp_2376_;
}
}
v___jp_2400_:
{
if (v___y_2407_ == 0)
{
v___y_2388_ = v___y_2405_;
v___y_2389_ = v___y_2401_;
v___y_2390_ = v___y_2402_;
v___y_2391_ = v___y_2406_;
v___y_2392_ = v___y_2403_;
v___y_2393_ = v___y_2404_;
v___y_2394_ = v_severity_2310_;
goto v___jp_2387_;
}
else
{
v___y_2388_ = v___y_2405_;
v___y_2389_ = v___y_2401_;
v___y_2390_ = v___y_2402_;
v___y_2391_ = v___y_2406_;
v___y_2392_ = v___y_2403_;
v___y_2393_ = v___y_2404_;
v___y_2394_ = v___x_2399_;
goto v___jp_2387_;
}
}
v___jp_2408_:
{
if (v___y_2409_ == 0)
{
lean_object* v_fileName_2410_; lean_object* v_fileMap_2411_; lean_object* v_options_2412_; lean_object* v_ref_2413_; uint8_t v_suppressElabErrors_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___f_2417_; uint8_t v___x_2418_; uint8_t v___x_2419_; 
v_fileName_2410_ = lean_ctor_get(v___y_2312_, 0);
v_fileMap_2411_ = lean_ctor_get(v___y_2312_, 1);
v_options_2412_ = lean_ctor_get(v___y_2312_, 2);
v_ref_2413_ = lean_ctor_get(v___y_2312_, 5);
v_suppressElabErrors_2414_ = lean_ctor_get_uint8(v___y_2312_, sizeof(void*)*14 + 1);
v___x_2415_ = lean_box(v___y_2409_);
v___x_2416_ = lean_box(v_suppressElabErrors_2414_);
v___f_2417_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2417_, 0, v___x_2415_);
lean_closure_set(v___f_2417_, 1, v___x_2416_);
v___x_2418_ = 1;
v___x_2419_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2310_, v___x_2418_);
if (v___x_2419_ == 0)
{
v___y_2401_ = v_fileMap_2411_;
v___y_2402_ = v_fileName_2410_;
v___y_2403_ = v_ref_2413_;
v___y_2404_ = v_suppressElabErrors_2414_;
v___y_2405_ = v___f_2417_;
v___y_2406_ = v___y_2409_;
v___y_2407_ = v___x_2419_;
goto v___jp_2400_;
}
else
{
lean_object* v___x_2420_; uint8_t v___x_2421_; 
v___x_2420_ = l_Lean_warningAsError;
v___x_2421_ = l_Lean_Option_get___at___00main_spec__8(v_options_2412_, v___x_2420_);
v___y_2401_ = v_fileMap_2411_;
v___y_2402_ = v_fileName_2410_;
v___y_2403_ = v_ref_2413_;
v___y_2404_ = v_suppressElabErrors_2414_;
v___y_2405_ = v___f_2417_;
v___y_2406_ = v___y_2409_;
v___y_2407_ = v___x_2421_;
goto v___jp_2400_;
}
}
else
{
lean_object* v___x_2422_; lean_object* v___x_2423_; 
lean_dec_ref(v_msgData_2309_);
v___x_2422_ = lean_box(0);
v___x_2423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2422_);
return v___x_2423_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___boxed(lean_object* v_ref_2426_, lean_object* v_msgData_2427_, lean_object* v_severity_2428_, lean_object* v_isSilent_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
uint8_t v_severity_boxed_2433_; uint8_t v_isSilent_boxed_2434_; lean_object* v_res_2435_; 
v_severity_boxed_2433_ = lean_unbox(v_severity_2428_);
v_isSilent_boxed_2434_ = lean_unbox(v_isSilent_2429_);
v_res_2435_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(v_ref_2426_, v_msgData_2427_, v_severity_boxed_2433_, v_isSilent_boxed_2434_, v___y_2430_, v___y_2431_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec(v_ref_2426_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(lean_object* v_msgData_2436_, uint8_t v_severity_2437_, uint8_t v_isSilent_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v_ref_2442_; lean_object* v___x_2443_; 
v_ref_2442_ = lean_ctor_get(v___y_2439_, 5);
v___x_2443_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(v_ref_2442_, v_msgData_2436_, v_severity_2437_, v_isSilent_2438_, v___y_2439_, v___y_2440_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30___boxed(lean_object* v_msgData_2444_, lean_object* v_severity_2445_, lean_object* v_isSilent_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
uint8_t v_severity_boxed_2450_; uint8_t v_isSilent_boxed_2451_; lean_object* v_res_2452_; 
v_severity_boxed_2450_ = lean_unbox(v_severity_2445_);
v_isSilent_boxed_2451_ = lean_unbox(v_isSilent_2446_);
v_res_2452_ = l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(v_msgData_2444_, v_severity_boxed_2450_, v_isSilent_boxed_2451_, v___y_2447_, v___y_2448_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__14(lean_object* v_msgData_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_){
_start:
{
uint8_t v___x_2457_; uint8_t v___x_2458_; lean_object* v___x_2459_; 
v___x_2457_ = 2;
v___x_2458_ = 0;
v___x_2459_ = l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(v_msgData_2453_, v___x_2457_, v___x_2458_, v___y_2454_, v___y_2455_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__14___boxed(lean_object* v_msgData_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_){
_start:
{
lean_object* v_res_2464_; 
v_res_2464_ = l_Lean_logError___at___00main_spec__14(v_msgData_2460_, v___y_2461_, v___y_2462_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(lean_object* v_x2_2465_, lean_object* v_as_2466_, size_t v_i_2467_, size_t v_stop_2468_, lean_object* v_b_2469_){
_start:
{
uint8_t v___x_2470_; 
v___x_2470_ = lean_usize_dec_eq(v_i_2467_, v_stop_2468_);
if (v___x_2470_ == 0)
{
lean_object* v___x_2471_; lean_object* v___x_2472_; size_t v___x_2473_; size_t v___x_2474_; 
v___x_2471_ = lean_array_uget_borrowed(v_as_2466_, v_i_2467_);
lean_inc_ref(v_x2_2465_);
lean_inc(v___x_2471_);
v___x_2472_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2471_, v_x2_2465_, v_b_2469_);
v___x_2473_ = ((size_t)1ULL);
v___x_2474_ = lean_usize_add(v_i_2467_, v___x_2473_);
v_i_2467_ = v___x_2474_;
v_b_2469_ = v___x_2472_;
goto _start;
}
else
{
lean_dec_ref(v_x2_2465_);
return v_b_2469_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2___boxed(lean_object* v_x2_2476_, lean_object* v_as_2477_, lean_object* v_i_2478_, lean_object* v_stop_2479_, lean_object* v_b_2480_){
_start:
{
size_t v_i_boxed_2481_; size_t v_stop_boxed_2482_; lean_object* v_res_2483_; 
v_i_boxed_2481_ = lean_unbox_usize(v_i_2478_);
lean_dec(v_i_2478_);
v_stop_boxed_2482_ = lean_unbox_usize(v_stop_2479_);
lean_dec(v_stop_2479_);
v_res_2483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v_x2_2476_, v_as_2477_, v_i_boxed_2481_, v_stop_boxed_2482_, v_b_2480_);
lean_dec_ref(v_as_2477_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(lean_object* v_as_2484_, size_t v_i_2485_, size_t v_stop_2486_, lean_object* v_b_2487_){
_start:
{
lean_object* v___y_2489_; uint8_t v___x_2493_; 
v___x_2493_ = lean_usize_dec_eq(v_i_2485_, v_stop_2486_);
if (v___x_2493_ == 0)
{
lean_object* v___x_2494_; lean_object* v_declNames_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; uint8_t v___x_2498_; 
v___x_2494_ = lean_array_uget_borrowed(v_as_2484_, v_i_2485_);
v_declNames_2495_ = lean_ctor_get(v___x_2494_, 0);
v___x_2496_ = lean_unsigned_to_nat(0u);
v___x_2497_ = lean_array_get_size(v_declNames_2495_);
v___x_2498_ = lean_nat_dec_lt(v___x_2496_, v___x_2497_);
if (v___x_2498_ == 0)
{
v___y_2489_ = v_b_2487_;
goto v___jp_2488_;
}
else
{
uint8_t v___x_2499_; 
v___x_2499_ = lean_nat_dec_le(v___x_2497_, v___x_2497_);
if (v___x_2499_ == 0)
{
if (v___x_2498_ == 0)
{
v___y_2489_ = v_b_2487_;
goto v___jp_2488_;
}
else
{
size_t v___x_2500_; size_t v___x_2501_; lean_object* v___x_2502_; 
v___x_2500_ = ((size_t)0ULL);
v___x_2501_ = lean_usize_of_nat(v___x_2497_);
lean_inc(v___x_2494_);
v___x_2502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_2494_, v_declNames_2495_, v___x_2500_, v___x_2501_, v_b_2487_);
v___y_2489_ = v___x_2502_;
goto v___jp_2488_;
}
}
else
{
size_t v___x_2503_; size_t v___x_2504_; lean_object* v___x_2505_; 
v___x_2503_ = ((size_t)0ULL);
v___x_2504_ = lean_usize_of_nat(v___x_2497_);
lean_inc(v___x_2494_);
v___x_2505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_2494_, v_declNames_2495_, v___x_2503_, v___x_2504_, v_b_2487_);
v___y_2489_ = v___x_2505_;
goto v___jp_2488_;
}
}
}
else
{
return v_b_2487_;
}
v___jp_2488_:
{
size_t v___x_2490_; size_t v___x_2491_; 
v___x_2490_ = ((size_t)1ULL);
v___x_2491_ = lean_usize_add(v_i_2485_, v___x_2490_);
v_i_2485_ = v___x_2491_;
v_b_2487_ = v___y_2489_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___boxed(lean_object* v_as_2506_, lean_object* v_i_2507_, lean_object* v_stop_2508_, lean_object* v_b_2509_){
_start:
{
size_t v_i_boxed_2510_; size_t v_stop_boxed_2511_; lean_object* v_res_2512_; 
v_i_boxed_2510_ = lean_unbox_usize(v_i_2507_);
lean_dec(v_i_2507_);
v_stop_boxed_2511_ = lean_unbox_usize(v_stop_2508_);
lean_dec(v_stop_2508_);
v_res_2512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v_as_2506_, v_i_boxed_2510_, v_stop_boxed_2511_, v_b_2509_);
lean_dec_ref(v_as_2506_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(lean_object* v_a_2513_, lean_object* v_as_2514_, size_t v_i_2515_, size_t v_stop_2516_, lean_object* v_b_2517_){
_start:
{
lean_object* v___y_2519_; uint8_t v___x_2523_; 
v___x_2523_ = lean_usize_dec_eq(v_i_2515_, v_stop_2516_);
if (v___x_2523_ == 0)
{
lean_object* v___x_2524_; lean_object* v_name_2525_; uint8_t v___x_2526_; 
v___x_2524_ = lean_array_uget_borrowed(v_as_2514_, v_i_2515_);
v_name_2525_ = lean_ctor_get(v___x_2524_, 0);
lean_inc(v_name_2525_);
lean_inc_ref(v_a_2513_);
v___x_2526_ = l_Lean_isExtern(v_a_2513_, v_name_2525_);
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
lean_dec_ref(v_a_2513_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19___boxed(lean_object* v_a_2528_, lean_object* v_as_2529_, lean_object* v_i_2530_, lean_object* v_stop_2531_, lean_object* v_b_2532_){
_start:
{
size_t v_i_boxed_2533_; size_t v_stop_boxed_2534_; lean_object* v_res_2535_; 
v_i_boxed_2533_ = lean_unbox_usize(v_i_2530_);
lean_dec(v_i_2530_);
v_stop_boxed_2534_ = lean_unbox_usize(v_stop_2531_);
lean_dec(v_stop_2531_);
v_res_2535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_2528_, v_as_2529_, v_i_boxed_2533_, v_stop_boxed_2534_, v_b_2532_);
lean_dec_ref(v_as_2529_);
return v_res_2535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(lean_object* v_as_2536_, size_t v_sz_2537_, size_t v_i_2538_, lean_object* v_b_2539_){
_start:
{
uint8_t v___x_2541_; 
v___x_2541_ = lean_usize_dec_lt(v_i_2538_, v_sz_2537_);
if (v___x_2541_ == 0)
{
lean_object* v___x_2542_; 
v___x_2542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2542_, 0, v_b_2539_);
return v___x_2542_;
}
else
{
uint8_t v___x_2543_; lean_object* v_a_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
lean_dec_ref(v_b_2539_);
v___x_2543_ = 0;
v_a_2544_ = lean_array_uget_borrowed(v_as_2536_, v_i_2538_);
lean_inc(v_a_2544_);
v___x_2545_ = l_Lean_Message_toString(v_a_2544_, v___x_2543_);
v___x_2546_ = l_IO_eprintln___at___00main_spec__6(v___x_2545_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v___x_2547_; size_t v___x_2548_; size_t v___x_2549_; 
lean_dec_ref_known(v___x_2546_, 1);
v___x_2547_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_2548_ = ((size_t)1ULL);
v___x_2549_ = lean_usize_add(v_i_2538_, v___x_2548_);
v_i_2538_ = v___x_2549_;
v_b_2539_ = v___x_2547_;
goto _start;
}
else
{
lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2558_; 
v_a_2551_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2553_ = v___x_2546_;
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v___x_2546_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2556_; 
if (v_isShared_2554_ == 0)
{
v___x_2556_ = v___x_2553_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_a_2551_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27___boxed(lean_object* v_as_2559_, lean_object* v_sz_2560_, lean_object* v_i_2561_, lean_object* v_b_2562_, lean_object* v___y_2563_){
_start:
{
size_t v_sz_boxed_2564_; size_t v_i_boxed_2565_; lean_object* v_res_2566_; 
v_sz_boxed_2564_ = lean_unbox_usize(v_sz_2560_);
lean_dec(v_sz_2560_);
v_i_boxed_2565_ = lean_unbox_usize(v_i_2561_);
lean_dec(v_i_2561_);
v_res_2566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(v_as_2559_, v_sz_boxed_2564_, v_i_boxed_2565_, v_b_2562_);
lean_dec_ref(v_as_2559_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(lean_object* v_as_2567_, size_t v_sz_2568_, size_t v_i_2569_, lean_object* v_b_2570_){
_start:
{
uint8_t v___x_2572_; 
v___x_2572_ = lean_usize_dec_lt(v_i_2569_, v_sz_2568_);
if (v___x_2572_ == 0)
{
lean_object* v___x_2573_; 
v___x_2573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2573_, 0, v_b_2570_);
return v___x_2573_;
}
else
{
uint8_t v___x_2574_; lean_object* v_a_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
lean_dec_ref(v_b_2570_);
v___x_2574_ = 0;
v_a_2575_ = lean_array_uget_borrowed(v_as_2567_, v_i_2569_);
lean_inc(v_a_2575_);
v___x_2576_ = l_Lean_Message_toString(v_a_2575_, v___x_2574_);
v___x_2577_ = l_IO_eprintln___at___00main_spec__6(v___x_2576_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v___x_2578_; size_t v___x_2579_; size_t v___x_2580_; lean_object* v___x_2581_; 
lean_dec_ref_known(v___x_2577_, 1);
v___x_2578_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_2579_ = ((size_t)1ULL);
v___x_2580_ = lean_usize_add(v_i_2569_, v___x_2579_);
v___x_2581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(v_as_2567_, v_sz_2568_, v___x_2580_, v___x_2578_);
return v___x_2581_;
}
else
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2589_; 
v_a_2582_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2584_ = v___x_2577_;
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2577_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2585_ == 0)
{
v___x_2587_ = v___x_2584_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_a_2582_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14___boxed(lean_object* v_as_2590_, lean_object* v_sz_2591_, lean_object* v_i_2592_, lean_object* v_b_2593_, lean_object* v___y_2594_){
_start:
{
size_t v_sz_boxed_2595_; size_t v_i_boxed_2596_; lean_object* v_res_2597_; 
v_sz_boxed_2595_ = lean_unbox_usize(v_sz_2591_);
lean_dec(v_sz_2591_);
v_i_boxed_2596_ = lean_unbox_usize(v_i_2592_);
lean_dec(v_i_2592_);
v_res_2597_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(v_as_2590_, v_sz_boxed_2595_, v_i_boxed_2596_, v_b_2593_);
lean_dec_ref(v_as_2590_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(lean_object* v_init_2598_, lean_object* v_n_2599_, lean_object* v_b_2600_){
_start:
{
if (lean_obj_tag(v_n_2599_) == 0)
{
lean_object* v_cs_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; size_t v_sz_2605_; size_t v___x_2606_; lean_object* v___x_2607_; 
v_cs_2602_ = lean_ctor_get(v_n_2599_, 0);
v___x_2603_ = lean_box(0);
v___x_2604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2603_);
lean_ctor_set(v___x_2604_, 1, v_b_2600_);
v_sz_2605_ = lean_array_size(v_cs_2602_);
v___x_2606_ = ((size_t)0ULL);
v___x_2607_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_init_2598_, v_cs_2602_, v_sz_2605_, v___x_2606_, v___x_2604_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2622_; 
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2610_ = v___x_2607_;
v_isShared_2611_ = v_isSharedCheck_2622_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2607_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2622_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v_fst_2612_; 
v_fst_2612_ = lean_ctor_get(v_a_2608_, 0);
if (lean_obj_tag(v_fst_2612_) == 0)
{
lean_object* v_snd_2613_; lean_object* v___x_2614_; lean_object* v___x_2616_; 
v_snd_2613_ = lean_ctor_get(v_a_2608_, 1);
lean_inc(v_snd_2613_);
lean_dec(v_a_2608_);
v___x_2614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2614_, 0, v_snd_2613_);
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 0, v___x_2614_);
v___x_2616_ = v___x_2610_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2614_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
else
{
lean_object* v_val_2618_; lean_object* v___x_2620_; 
lean_inc_ref(v_fst_2612_);
lean_dec(v_a_2608_);
v_val_2618_ = lean_ctor_get(v_fst_2612_, 0);
lean_inc(v_val_2618_);
lean_dec_ref_known(v_fst_2612_, 1);
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 0, v_val_2618_);
v___x_2620_ = v___x_2610_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_val_2618_);
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
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2630_; 
v_a_2623_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2625_ = v___x_2607_;
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2607_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2628_; 
if (v_isShared_2626_ == 0)
{
v___x_2628_ = v___x_2625_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_a_2623_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
else
{
lean_object* v_vs_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; size_t v_sz_2634_; size_t v___x_2635_; lean_object* v___x_2636_; 
v_vs_2631_ = lean_ctor_get(v_n_2599_, 0);
v___x_2632_ = lean_box(0);
v___x_2633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2632_);
lean_ctor_set(v___x_2633_, 1, v_b_2600_);
v_sz_2634_ = lean_array_size(v_vs_2631_);
v___x_2635_ = ((size_t)0ULL);
v___x_2636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(v_vs_2631_, v_sz_2634_, v___x_2635_, v___x_2633_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2651_; 
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2639_ = v___x_2636_;
v_isShared_2640_ = v_isSharedCheck_2651_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2636_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2651_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v_fst_2641_; 
v_fst_2641_ = lean_ctor_get(v_a_2637_, 0);
if (lean_obj_tag(v_fst_2641_) == 0)
{
lean_object* v_snd_2642_; lean_object* v___x_2643_; lean_object* v___x_2645_; 
v_snd_2642_ = lean_ctor_get(v_a_2637_, 1);
lean_inc(v_snd_2642_);
lean_dec(v_a_2637_);
v___x_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2643_, 0, v_snd_2642_);
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 0, v___x_2643_);
v___x_2645_ = v___x_2639_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v___x_2643_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
else
{
lean_object* v_val_2647_; lean_object* v___x_2649_; 
lean_inc_ref(v_fst_2641_);
lean_dec(v_a_2637_);
v_val_2647_ = lean_ctor_get(v_fst_2641_, 0);
lean_inc(v_val_2647_);
lean_dec_ref_known(v_fst_2641_, 1);
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 0, v_val_2647_);
v___x_2649_ = v___x_2639_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_val_2647_);
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
else
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
v_a_2652_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___x_2636_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2636_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2657_; 
if (v_isShared_2655_ == 0)
{
v___x_2657_ = v___x_2654_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_a_2652_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(lean_object* v_init_2660_, lean_object* v_as_2661_, size_t v_sz_2662_, size_t v_i_2663_, lean_object* v_b_2664_){
_start:
{
uint8_t v___x_2666_; 
v___x_2666_ = lean_usize_dec_lt(v_i_2663_, v_sz_2662_);
if (v___x_2666_ == 0)
{
lean_object* v___x_2667_; 
v___x_2667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2667_, 0, v_b_2664_);
return v___x_2667_;
}
else
{
lean_object* v_snd_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2702_; 
v_snd_2668_ = lean_ctor_get(v_b_2664_, 1);
v_isSharedCheck_2702_ = !lean_is_exclusive(v_b_2664_);
if (v_isSharedCheck_2702_ == 0)
{
lean_object* v_unused_2703_; 
v_unused_2703_ = lean_ctor_get(v_b_2664_, 0);
lean_dec(v_unused_2703_);
v___x_2670_ = v_b_2664_;
v_isShared_2671_ = v_isSharedCheck_2702_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_snd_2668_);
lean_dec(v_b_2664_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2702_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v_a_2672_; lean_object* v___x_2673_; 
v_a_2672_ = lean_array_uget_borrowed(v_as_2661_, v_i_2663_);
lean_inc(v_snd_2668_);
v___x_2673_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2660_, v_a_2672_, v_snd_2668_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v_a_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2693_; 
v_a_2674_ = lean_ctor_get(v___x_2673_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2676_ = v___x_2673_;
v_isShared_2677_ = v_isSharedCheck_2693_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_a_2674_);
lean_dec(v___x_2673_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2693_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
if (lean_obj_tag(v_a_2674_) == 0)
{
lean_object* v___x_2678_; lean_object* v___x_2680_; 
v___x_2678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2678_, 0, v_a_2674_);
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 0, v___x_2678_);
v___x_2680_ = v___x_2670_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2678_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v_snd_2668_);
v___x_2680_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
lean_object* v___x_2682_; 
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 0, v___x_2680_);
v___x_2682_ = v___x_2676_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2680_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
else
{
lean_object* v_a_2685_; lean_object* v___x_2686_; lean_object* v___x_2688_; 
lean_del_object(v___x_2676_);
lean_dec(v_snd_2668_);
v_a_2685_ = lean_ctor_get(v_a_2674_, 0);
lean_inc(v_a_2685_);
lean_dec_ref_known(v_a_2674_, 1);
v___x_2686_ = lean_box(0);
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 1, v_a_2685_);
lean_ctor_set(v___x_2670_, 0, v___x_2686_);
v___x_2688_ = v___x_2670_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v___x_2686_);
lean_ctor_set(v_reuseFailAlloc_2692_, 1, v_a_2685_);
v___x_2688_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
size_t v___x_2689_; size_t v___x_2690_; 
v___x_2689_ = ((size_t)1ULL);
v___x_2690_ = lean_usize_add(v_i_2663_, v___x_2689_);
v_i_2663_ = v___x_2690_;
v_b_2664_ = v___x_2688_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2701_; 
lean_del_object(v___x_2670_);
lean_dec(v_snd_2668_);
v_a_2694_ = lean_ctor_get(v___x_2673_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2696_ = v___x_2673_;
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2673_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2699_; 
if (v_isShared_2697_ == 0)
{
v___x_2699_ = v___x_2696_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2694_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13___boxed(lean_object* v_init_2704_, lean_object* v_as_2705_, lean_object* v_sz_2706_, lean_object* v_i_2707_, lean_object* v_b_2708_, lean_object* v___y_2709_){
_start:
{
size_t v_sz_boxed_2710_; size_t v_i_boxed_2711_; lean_object* v_res_2712_; 
v_sz_boxed_2710_ = lean_unbox_usize(v_sz_2706_);
lean_dec(v_sz_2706_);
v_i_boxed_2711_ = lean_unbox_usize(v_i_2707_);
lean_dec(v_i_2707_);
v_res_2712_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_init_2704_, v_as_2705_, v_sz_boxed_2710_, v_i_boxed_2711_, v_b_2708_);
lean_dec_ref(v_as_2705_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10___boxed(lean_object* v_init_2713_, lean_object* v_n_2714_, lean_object* v_b_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2713_, v_n_2714_, v_b_2715_);
lean_dec_ref(v_n_2714_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(lean_object* v_as_2718_, size_t v_sz_2719_, size_t v_i_2720_, lean_object* v_b_2721_){
_start:
{
uint8_t v___x_2723_; 
v___x_2723_ = lean_usize_dec_lt(v_i_2720_, v_sz_2719_);
if (v___x_2723_ == 0)
{
lean_object* v___x_2724_; 
v___x_2724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2724_, 0, v_b_2721_);
return v___x_2724_;
}
else
{
uint8_t v___x_2725_; lean_object* v_a_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
lean_dec_ref(v_b_2721_);
v___x_2725_ = 0;
v_a_2726_ = lean_array_uget_borrowed(v_as_2718_, v_i_2720_);
lean_inc(v_a_2726_);
v___x_2727_ = l_Lean_Message_toString(v_a_2726_, v___x_2725_);
v___x_2728_ = l_IO_eprintln___at___00main_spec__6(v___x_2727_);
if (lean_obj_tag(v___x_2728_) == 0)
{
lean_object* v___x_2729_; size_t v___x_2730_; size_t v___x_2731_; 
lean_dec_ref_known(v___x_2728_, 1);
v___x_2729_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_2730_ = ((size_t)1ULL);
v___x_2731_ = lean_usize_add(v_i_2720_, v___x_2730_);
v_i_2720_ = v___x_2731_;
v_b_2721_ = v___x_2729_;
goto _start;
}
else
{
lean_object* v_a_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2740_; 
v_a_2733_ = lean_ctor_get(v___x_2728_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2728_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2735_ = v___x_2728_;
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_a_2733_);
lean_dec(v___x_2728_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2738_; 
if (v_isShared_2736_ == 0)
{
v___x_2738_ = v___x_2735_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_a_2733_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16___boxed(lean_object* v_as_2741_, lean_object* v_sz_2742_, lean_object* v_i_2743_, lean_object* v_b_2744_, lean_object* v___y_2745_){
_start:
{
size_t v_sz_boxed_2746_; size_t v_i_boxed_2747_; lean_object* v_res_2748_; 
v_sz_boxed_2746_ = lean_unbox_usize(v_sz_2742_);
lean_dec(v_sz_2742_);
v_i_boxed_2747_ = lean_unbox_usize(v_i_2743_);
lean_dec(v_i_2743_);
v_res_2748_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(v_as_2741_, v_sz_boxed_2746_, v_i_boxed_2747_, v_b_2744_);
lean_dec_ref(v_as_2741_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(lean_object* v_as_2749_, size_t v_sz_2750_, size_t v_i_2751_, lean_object* v_b_2752_){
_start:
{
uint8_t v___x_2754_; 
v___x_2754_ = lean_usize_dec_lt(v_i_2751_, v_sz_2750_);
if (v___x_2754_ == 0)
{
lean_object* v___x_2755_; 
v___x_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2755_, 0, v_b_2752_);
return v___x_2755_;
}
else
{
uint8_t v___x_2756_; lean_object* v_a_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
lean_dec_ref(v_b_2752_);
v___x_2756_ = 0;
v_a_2757_ = lean_array_uget_borrowed(v_as_2749_, v_i_2751_);
lean_inc(v_a_2757_);
v___x_2758_ = l_Lean_Message_toString(v_a_2757_, v___x_2756_);
v___x_2759_ = l_IO_eprintln___at___00main_spec__6(v___x_2758_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v___x_2760_; size_t v___x_2761_; size_t v___x_2762_; lean_object* v___x_2763_; 
lean_dec_ref_known(v___x_2759_, 1);
v___x_2760_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_2761_ = ((size_t)1ULL);
v___x_2762_ = lean_usize_add(v_i_2751_, v___x_2761_);
v___x_2763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(v_as_2749_, v_sz_2750_, v___x_2762_, v___x_2760_);
return v___x_2763_;
}
else
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2771_; 
v_a_2764_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2766_ = v___x_2759_;
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2759_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2769_; 
if (v_isShared_2767_ == 0)
{
v___x_2769_ = v___x_2766_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2764_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11___boxed(lean_object* v_as_2772_, lean_object* v_sz_2773_, lean_object* v_i_2774_, lean_object* v_b_2775_, lean_object* v___y_2776_){
_start:
{
size_t v_sz_boxed_2777_; size_t v_i_boxed_2778_; lean_object* v_res_2779_; 
v_sz_boxed_2777_ = lean_unbox_usize(v_sz_2773_);
lean_dec(v_sz_2773_);
v_i_boxed_2778_ = lean_unbox_usize(v_i_2774_);
lean_dec(v_i_2774_);
v_res_2779_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_as_2772_, v_sz_boxed_2777_, v_i_boxed_2778_, v_b_2775_);
lean_dec_ref(v_as_2772_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7(lean_object* v_t_2780_, lean_object* v_init_2781_){
_start:
{
lean_object* v_root_2783_; lean_object* v_tail_2784_; lean_object* v___x_2785_; 
v_root_2783_ = lean_ctor_get(v_t_2780_, 0);
v_tail_2784_ = lean_ctor_get(v_t_2780_, 1);
v___x_2785_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2781_, v_root_2783_, v_init_2781_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2822_; 
v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2788_ = v___x_2785_;
v_isShared_2789_ = v_isSharedCheck_2822_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2785_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2822_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
if (lean_obj_tag(v_a_2786_) == 0)
{
lean_object* v_a_2790_; lean_object* v___x_2792_; 
v_a_2790_ = lean_ctor_get(v_a_2786_, 0);
lean_inc(v_a_2790_);
lean_dec_ref_known(v_a_2786_, 1);
if (v_isShared_2789_ == 0)
{
lean_ctor_set(v___x_2788_, 0, v_a_2790_);
v___x_2792_ = v___x_2788_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2790_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
else
{
lean_object* v_a_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; size_t v_sz_2797_; size_t v___x_2798_; lean_object* v___x_2799_; 
lean_del_object(v___x_2788_);
v_a_2794_ = lean_ctor_get(v_a_2786_, 0);
lean_inc(v_a_2794_);
lean_dec_ref_known(v_a_2786_, 1);
v___x_2795_ = lean_box(0);
v___x_2796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2795_);
lean_ctor_set(v___x_2796_, 1, v_a_2794_);
v_sz_2797_ = lean_array_size(v_tail_2784_);
v___x_2798_ = ((size_t)0ULL);
v___x_2799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_tail_2784_, v_sz_2797_, v___x_2798_, v___x_2796_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2813_; 
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2802_ = v___x_2799_;
v_isShared_2803_ = v_isSharedCheck_2813_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2799_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2813_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v_fst_2804_; 
v_fst_2804_ = lean_ctor_get(v_a_2800_, 0);
if (lean_obj_tag(v_fst_2804_) == 0)
{
lean_object* v_snd_2805_; lean_object* v___x_2807_; 
v_snd_2805_ = lean_ctor_get(v_a_2800_, 1);
lean_inc(v_snd_2805_);
lean_dec(v_a_2800_);
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 0, v_snd_2805_);
v___x_2807_ = v___x_2802_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_snd_2805_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
else
{
lean_object* v_val_2809_; lean_object* v___x_2811_; 
lean_inc_ref(v_fst_2804_);
lean_dec(v_a_2800_);
v_val_2809_ = lean_ctor_get(v_fst_2804_, 0);
lean_inc(v_val_2809_);
lean_dec_ref_known(v_fst_2804_, 1);
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 0, v_val_2809_);
v___x_2811_ = v___x_2802_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_val_2809_);
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
else
{
lean_object* v_a_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2821_; 
v_a_2814_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2821_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2816_ = v___x_2799_;
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_a_2814_);
lean_dec(v___x_2799_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v___x_2819_; 
if (v_isShared_2817_ == 0)
{
v___x_2819_ = v___x_2816_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_a_2814_);
v___x_2819_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
return v___x_2819_;
}
}
}
}
}
}
else
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
v_a_2823_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2825_ = v___x_2785_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2785_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
if (v_isShared_2826_ == 0)
{
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_a_2823_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7___boxed(lean_object* v_t_2831_, lean_object* v_init_2832_, lean_object* v___y_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_t_2831_, v_init_2832_);
lean_dec_ref(v_t_2831_);
return v_res_2834_;
}
}
static lean_object* _init_l_main___closed__3(void){
_start:
{
lean_object* v___x_2838_; 
v___x_2838_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(lean_box(0), lean_box(0), lean_box(0));
return v___x_2838_;
}
}
static lean_object* _init_l_main___closed__4(void){
_start:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2839_ = l_Lean_instInhabitedClassState_default;
v___x_2840_ = lean_box(0);
v___x_2841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2840_);
lean_ctor_set(v___x_2841_, 1, v___x_2839_);
return v___x_2841_;
}
}
static lean_object* _init_l_main___closed__5(void){
_start:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2842_ = l_Lean_Meta_Match_Extension_instInhabitedState;
v___x_2843_ = lean_box(0);
v___x_2844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2843_);
lean_ctor_set(v___x_2844_, 1, v___x_2842_);
return v___x_2844_;
}
}
static lean_object* _init_l_main___closed__6(void){
_start:
{
lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2845_ = ((lean_object*)(l_main___closed__2));
v___x_2846_ = ((lean_object*)(l_main___closed__1));
v___x_2847_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_2846_, v___x_2845_);
return v___x_2847_;
}
}
static lean_object* _init_l_main___closed__7(void){
_start:
{
lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2848_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_2849_ = lean_box(0);
v___x_2850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2849_);
lean_ctor_set(v___x_2850_, 1, v___x_2848_);
return v___x_2850_;
}
}
static lean_object* _init_l_main___closed__8(void){
_start:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2851_ = lean_obj_once(&l_main___closed__7, &l_main___closed__7_once, _init_l_main___closed__7);
v___x_2852_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2851_);
return v___x_2852_;
}
}
static lean_object* _init_l_main___closed__9(void){
_start:
{
lean_object* v___x_2853_; 
v___x_2853_ = l_Array_instInhabited(lean_box(0));
return v___x_2853_;
}
}
static lean_object* _init_l_main___closed__15(void){
_start:
{
lean_object* v___x_2862_; lean_object* v___x_2863_; 
v___x_2862_ = l_Lean_Options_empty;
v___x_2863_ = l_Lean_Core_getMaxHeartbeats(v___x_2862_);
return v___x_2863_;
}
}
static lean_object* _init_l_main___closed__20(void){
_start:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2868_ = ((lean_object*)(l_main___closed__19));
v___x_2869_ = lean_unsigned_to_nat(27u);
v___x_2870_ = lean_unsigned_to_nat(149u);
v___x_2871_ = ((lean_object*)(l_main___closed__18));
v___x_2872_ = ((lean_object*)(l_main___closed__17));
v___x_2873_ = l_mkPanicMessageWithDecl(v___x_2872_, v___x_2871_, v___x_2870_, v___x_2869_, v___x_2868_);
return v___x_2873_;
}
}
static lean_object* _init_l_main___closed__22(void){
_start:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2875_ = ((lean_object*)(l_main___closed__19));
v___x_2876_ = lean_unsigned_to_nat(51u);
v___x_2877_ = lean_unsigned_to_nat(122u);
v___x_2878_ = ((lean_object*)(l_main___closed__18));
v___x_2879_ = ((lean_object*)(l_main___closed__17));
v___x_2880_ = l_mkPanicMessageWithDecl(v___x_2879_, v___x_2878_, v___x_2877_, v___x_2876_, v___x_2875_);
return v___x_2880_;
}
}
static lean_object* _init_l_main___closed__23(void){
_start:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2881_ = lean_unsigned_to_nat(1u);
v___x_2882_ = l_Lean_firstFrontendMacroScope;
v___x_2883_ = lean_nat_add(v___x_2882_, v___x_2881_);
return v___x_2883_;
}
}
static lean_object* _init_l_main___closed__27(void){
_start:
{
lean_object* v___x_2890_; uint64_t v___x_2891_; lean_object* v___x_2892_; 
v___x_2890_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2891_ = 0ULL;
v___x_2892_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2892_, 0, v___x_2890_);
lean_ctor_set_uint64(v___x_2892_, sizeof(void*)*1, v___x_2891_);
return v___x_2892_;
}
}
static lean_object* _init_l_main___closed__28(void){
_start:
{
lean_object* v___x_2893_; 
v___x_2893_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2893_;
}
}
static lean_object* _init_l_main___closed__29(void){
_start:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2894_ = lean_obj_once(&l_main___closed__28, &l_main___closed__28_once, _init_l_main___closed__28);
v___x_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2894_);
return v___x_2895_;
}
}
static lean_object* _init_l_main___closed__30(void){
_start:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2896_ = lean_obj_once(&l_main___closed__29, &l_main___closed__29_once, _init_l_main___closed__29);
v___x_2897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2896_);
lean_ctor_set(v___x_2897_, 1, v___x_2896_);
return v___x_2897_;
}
}
static lean_object* _init_l_main___closed__31(void){
_start:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2898_ = l_Lean_NameSet_empty;
v___x_2899_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2900_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2899_);
lean_ctor_set(v___x_2900_, 1, v___x_2899_);
lean_ctor_set(v___x_2900_, 2, v___x_2898_);
return v___x_2900_;
}
}
static lean_object* _init_l_main___closed__32(void){
_start:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; uint8_t v___x_2903_; lean_object* v___x_2904_; 
v___x_2901_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2902_ = lean_obj_once(&l_main___closed__29, &l_main___closed__29_once, _init_l_main___closed__29);
v___x_2903_ = 1;
v___x_2904_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2904_, 0, v___x_2902_);
lean_ctor_set(v___x_2904_, 1, v___x_2902_);
lean_ctor_set(v___x_2904_, 2, v___x_2901_);
lean_ctor_set_uint8(v___x_2904_, sizeof(void*)*3, v___x_2903_);
return v___x_2904_;
}
}
static uint8_t _init_l_main___closed__37(void){
_start:
{
uint8_t v___x_2911_; uint8_t v___x_2912_; uint8_t v___x_2913_; 
v___x_2911_ = 2;
v___x_2912_ = 0;
v___x_2913_ = l_Lean_instOrdOLeanLevel_ord(v___x_2912_, v___x_2911_);
return v___x_2913_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_2914_; lean_object* v___x_2915_; 
v___x_2914_ = 1;
v___x_2915_ = lean_box_uint32(v___x_2914_);
return v___x_2915_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_2916_; lean_object* v___x_2917_; 
v___x_2916_ = 0;
v___x_2917_ = lean_box_uint32(v___x_2916_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_2918_){
_start:
{
if (lean_obj_tag(v_args_2918_) == 1)
{
lean_object* v_tail_2943_; 
v_tail_2943_ = lean_ctor_get(v_args_2918_, 1);
lean_inc(v_tail_2943_);
if (lean_obj_tag(v_tail_2943_) == 1)
{
lean_object* v_tail_2944_; 
v_tail_2944_ = lean_ctor_get(v_tail_2943_, 1);
lean_inc(v_tail_2944_);
if (lean_obj_tag(v_tail_2944_) == 1)
{
lean_object* v_head_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_3591_; 
v_head_2945_ = lean_ctor_get(v_args_2918_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v_args_2918_);
if (v_isSharedCheck_3591_ == 0)
{
lean_object* v_unused_3592_; 
v_unused_3592_ = lean_ctor_get(v_args_2918_, 1);
lean_dec(v_unused_3592_);
v___x_2947_ = v_args_2918_;
v_isShared_2948_ = v_isSharedCheck_3591_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_head_2945_);
lean_dec(v_args_2918_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_3591_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v_head_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_3589_; 
v_head_2949_ = lean_ctor_get(v_tail_2943_, 0);
v_isSharedCheck_3589_ = !lean_is_exclusive(v_tail_2943_);
if (v_isSharedCheck_3589_ == 0)
{
lean_object* v_unused_3590_; 
v_unused_3590_ = lean_ctor_get(v_tail_2943_, 1);
lean_dec(v_unused_3590_);
v___x_2951_ = v_tail_2943_;
v_isShared_2952_ = v_isSharedCheck_3589_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_head_2949_);
lean_dec(v_tail_2943_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_3589_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v_head_2953_; lean_object* v_tail_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_3588_; 
v_head_2953_ = lean_ctor_get(v_tail_2944_, 0);
v_tail_2954_ = lean_ctor_get(v_tail_2944_, 1);
v_isSharedCheck_3588_ = !lean_is_exclusive(v_tail_2944_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_2956_ = v_tail_2944_;
v_isShared_2957_ = v_isSharedCheck_3588_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_tail_2954_);
lean_inc(v_head_2953_);
lean_dec(v_tail_2944_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_3588_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2958_; 
v___x_2958_ = l_Lean_ModuleSetup_load(v_head_2945_);
lean_dec(v_head_2945_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; lean_object* v_name_2960_; lean_object* v_importArts_2961_; lean_object* v_options_2962_; uint8_t v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2967_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
lean_inc(v_a_2959_);
lean_dec_ref_known(v___x_2958_, 1);
v_name_2960_ = lean_ctor_get(v_a_2959_, 0);
lean_inc(v_name_2960_);
v_importArts_2961_ = lean_ctor_get(v_a_2959_, 3);
lean_inc(v_importArts_2961_);
v_options_2962_ = lean_ctor_get(v_a_2959_, 6);
lean_inc(v_options_2962_);
lean_dec(v_a_2959_);
v___x_2963_ = 0;
v___x_2964_ = l_Lean_LeanOptions_toOptions(v_options_2962_);
v___x_2965_ = lean_box(v___x_2963_);
if (v_isShared_2957_ == 0)
{
lean_ctor_set_tag(v___x_2956_, 0);
lean_ctor_set(v___x_2956_, 1, v___x_2964_);
lean_ctor_set(v___x_2956_, 0, v___x_2965_);
v___x_2967_ = v___x_2956_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_2965_);
lean_ctor_set(v_reuseFailAlloc_3579_, 1, v___x_2964_);
v___x_2967_ = v_reuseFailAlloc_3579_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
lean_object* v___x_2968_; 
v___x_2968_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_tail_2954_, v___x_2967_);
lean_dec(v_tail_2954_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v_a_2969_; lean_object* v___x_2970_; 
v_a_2969_ = lean_ctor_get(v___x_2968_, 0);
lean_inc(v_a_2969_);
lean_dec_ref_known(v___x_2968_, 1);
v___x_2970_ = lean_init_search_path();
if (lean_obj_tag(v___x_2970_) == 0)
{
lean_object* v_fst_2971_; lean_object* v_snd_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_3562_; 
lean_dec_ref_known(v___x_2970_, 1);
v_fst_2971_ = lean_ctor_get(v_a_2969_, 0);
v_snd_2972_ = lean_ctor_get(v_a_2969_, 1);
v_isSharedCheck_3562_ = !lean_is_exclusive(v_a_2969_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_2974_ = v_a_2969_;
v_isShared_2975_ = v_isSharedCheck_3562_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_snd_2972_);
lean_inc(v_fst_2971_);
lean_dec(v_a_2969_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_3562_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; uint8_t v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___y_2992_; uint8_t v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3146_; uint8_t v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v_nextMacroScope_3156_; lean_object* v_ngen_3157_; lean_object* v_auxDeclNGen_3158_; lean_object* v_traceState_3159_; lean_object* v_messages_3160_; lean_object* v_infoState_3161_; lean_object* v_snapshotTasks_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3189_; uint8_t v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; uint8_t v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3260_; uint8_t v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; uint8_t v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; uint8_t v___y_3283_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; uint8_t v___x_3308_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; uint8_t v___x_3465_; uint8_t v___y_3467_; uint8_t v___x_3561_; 
v___x_2976_ = lean_obj_once(&l_main___closed__3, &l_main___closed__3_once, _init_l_main___closed__3);
v___x_2977_ = lean_box(0);
v___x_2978_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_2979_ = lean_obj_once(&l_main___closed__5, &l_main___closed__5_once, _init_l_main___closed__5);
v___x_2980_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_2981_ = lean_obj_once(&l_main___closed__8, &l_main___closed__8_once, _init_l_main___closed__8);
v___x_2982_ = lean_obj_once(&l_main___closed__9, &l_main___closed__9_once, _init_l_main___closed__9);
v___x_2983_ = lean_box(1);
v___x_2984_ = ((lean_object*)(l_main___closed__10));
v___x_2985_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_2986_ = 1;
v___x_2987_ = l_Lean_Option_set___at___00Lean_Environment_realizeConst_spec__0(v_snd_2972_, v___x_2985_, v___x_2986_);
v___x_2988_ = l_Lean_maxHeartbeats;
v___x_2989_ = lean_unsigned_to_nat(0u);
v___x_2990_ = l_Lean_Option_set___at___00main_spec__3(v___x_2987_, v___x_2988_, v___x_2989_);
v___x_3303_ = ((lean_object*)(l_main___closed__21));
lean_inc(v_name_2960_);
v___x_3304_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_3304_, 0, v_name_2960_);
lean_ctor_set_uint8(v___x_3304_, sizeof(void*)*1, v___x_2986_);
lean_ctor_set_uint8(v___x_3304_, sizeof(void*)*1 + 1, v___x_2986_);
lean_ctor_set_uint8(v___x_3304_, sizeof(void*)*1 + 2, v___x_2963_);
v___x_3305_ = lean_unsigned_to_nat(1u);
v___x_3306_ = lean_mk_empty_array_with_capacity(v___x_3305_);
v___x_3307_ = lean_array_push(v___x_3306_, v___x_3304_);
v___x_3308_ = 0;
v___x_3465_ = 2;
v___x_3561_ = lean_uint8_once(&l_main___closed__37, &l_main___closed__37_once, _init_l_main___closed__37);
if (v___x_3561_ == 0)
{
v___y_3467_ = v___x_2986_;
goto v___jp_3466_;
}
else
{
v___y_3467_ = v___x_2963_;
goto v___jp_3466_;
}
v___jp_2991_:
{
lean_object* v___x_3011_; lean_object* v_messages_3012_; lean_object* v_env_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3137_; 
v___x_3011_ = lean_st_ref_get(v___y_3006_);
lean_dec(v___y_3006_);
v_messages_3012_ = lean_ctor_get(v___x_3011_, 6);
v_env_3013_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3137_ == 0)
{
lean_object* v_unused_3138_; lean_object* v_unused_3139_; lean_object* v_unused_3140_; lean_object* v_unused_3141_; lean_object* v_unused_3142_; lean_object* v_unused_3143_; lean_object* v_unused_3144_; 
v_unused_3138_ = lean_ctor_get(v___x_3011_, 8);
lean_dec(v_unused_3138_);
v_unused_3139_ = lean_ctor_get(v___x_3011_, 7);
lean_dec(v_unused_3139_);
v_unused_3140_ = lean_ctor_get(v___x_3011_, 5);
lean_dec(v_unused_3140_);
v_unused_3141_ = lean_ctor_get(v___x_3011_, 4);
lean_dec(v_unused_3141_);
v_unused_3142_ = lean_ctor_get(v___x_3011_, 3);
lean_dec(v_unused_3142_);
v_unused_3143_ = lean_ctor_get(v___x_3011_, 2);
lean_dec(v_unused_3143_);
v_unused_3144_ = lean_ctor_get(v___x_3011_, 1);
lean_dec(v_unused_3144_);
v___x_3015_ = v___x_3011_;
v_isShared_3016_ = v_isSharedCheck_3137_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_messages_3012_);
lean_inc(v_env_3013_);
lean_dec(v___x_3011_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3137_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v_unreported_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v_unreported_3017_ = lean_ctor_get(v_messages_3012_, 1);
v___x_3018_ = lean_box(0);
v___x_3019_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_unreported_3017_, v___x_3018_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3127_; 
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3127_ == 0)
{
lean_object* v_unused_3128_; 
v_unused_3128_ = lean_ctor_get(v___x_3019_, 0);
lean_dec(v_unused_3128_);
v___x_3021_ = v___x_3019_;
v_isShared_3022_ = v_isSharedCheck_3127_;
goto v_resetjp_3020_;
}
else
{
lean_dec(v___x_3019_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3127_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
uint8_t v___x_3023_; 
v___x_3023_ = l_Lean_MessageLog_hasErrors(v_messages_3012_);
lean_dec_ref(v_messages_3012_);
if (v___x_3023_ == 0)
{
lean_object* v___x_3024_; 
lean_del_object(v___x_3021_);
lean_inc_ref(v_env_3013_);
v___x_3024_ = l___private_LeanIR_0__mkIRSigData(v_env_3013_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; lean_object* v___x_3026_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_a_3025_);
lean_dec_ref_known(v___x_3024_, 1);
lean_inc_ref(v_env_3013_);
v___x_3026_ = l___private_LeanIR_0__mkIRData(v_env_3013_);
if (lean_obj_tag(v___x_3026_) == 0)
{
lean_object* v_a_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3034_; 
v_a_3027_ = lean_ctor_get(v___x_3026_, 0);
lean_inc(v_a_3027_);
lean_dec_ref_known(v___x_3026_, 1);
v___x_3028_ = ((lean_object*)(l_main___closed__11));
lean_inc(v_head_2949_);
v___x_3029_ = l_System_FilePath_addExtension(v_head_2949_, v___x_3028_);
v___x_3030_ = l_Lean_Environment_mainModule(v_env_3013_);
v___x_3031_ = ((lean_object*)(l_main___closed__13));
v___x_3032_ = l_Lean_Name_append(v___x_3030_, v___x_3031_);
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 1, v_a_3025_);
lean_ctor_set(v___x_2974_, 0, v___x_3029_);
v___x_3034_ = v___x_2974_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v___x_3029_);
lean_ctor_set(v_reuseFailAlloc_3106_, 1, v_a_3025_);
v___x_3034_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
lean_object* v___x_3036_; 
lean_inc(v_head_2949_);
if (v_isShared_2952_ == 0)
{
lean_ctor_set_tag(v___x_2951_, 0);
lean_ctor_set(v___x_2951_, 1, v_a_3027_);
v___x_3036_ = v___x_2951_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_head_2949_);
lean_ctor_set(v_reuseFailAlloc_3105_, 1, v_a_3027_);
v___x_3036_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
v___x_3037_ = lean_unsigned_to_nat(2u);
v___x_3038_ = lean_mk_empty_array_with_capacity(v___x_3037_);
v___x_3039_ = lean_array_push(v___x_3038_, v___x_3034_);
v___x_3040_ = lean_array_push(v___x_3039_, v___x_3036_);
v___x_3041_ = l_Lean_saveModuleDataParts(v___x_3032_, v___x_3040_);
lean_dec_ref(v___x_3040_);
lean_dec(v___x_3032_);
if (lean_obj_tag(v___x_3041_) == 0)
{
uint8_t v___x_3042_; lean_object* v___x_3043_; 
lean_dec_ref_known(v___x_3041_, 1);
v___x_3042_ = 1;
v___x_3043_ = lean_io_prim_handle_mk(v_head_2953_, v___x_3042_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_object* v_a_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3049_; 
lean_dec(v_head_2953_);
v_a_3044_ = lean_ctor_get(v___x_3043_, 0);
lean_inc(v_a_3044_);
lean_dec_ref_known(v___x_3043_, 1);
v___x_3045_ = ((lean_object*)(l_main___closed__14));
v___x_3046_ = l_Lean_Options_empty;
v___x_3047_ = lean_obj_once(&l_main___closed__15, &l_main___closed__15_once, _init_l_main___closed__15);
lean_inc_ref(v___y_3001_);
lean_inc_ref(v___y_3007_);
lean_inc_ref(v___y_3005_);
lean_inc_ref(v___y_3003_);
lean_inc_ref(v___y_3002_);
lean_inc_ref(v___y_3008_);
lean_inc(v___y_3010_);
lean_inc_ref(v_env_3013_);
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 8, v___y_3001_);
lean_ctor_set(v___x_3015_, 7, v___y_3007_);
lean_ctor_set(v___x_3015_, 6, v___y_3005_);
lean_ctor_set(v___x_3015_, 5, v___y_3003_);
lean_ctor_set(v___x_3015_, 4, v___y_3002_);
lean_ctor_set(v___x_3015_, 3, v___y_3009_);
lean_ctor_set(v___x_3015_, 2, v___y_3008_);
lean_ctor_set(v___x_3015_, 1, v___y_3010_);
v___x_3049_ = v___x_3015_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_env_3013_);
lean_ctor_set(v_reuseFailAlloc_3074_, 1, v___y_3010_);
lean_ctor_set(v_reuseFailAlloc_3074_, 2, v___y_3008_);
lean_ctor_set(v_reuseFailAlloc_3074_, 3, v___y_3009_);
lean_ctor_set(v_reuseFailAlloc_3074_, 4, v___y_3002_);
lean_ctor_set(v_reuseFailAlloc_3074_, 5, v___y_3003_);
lean_ctor_set(v_reuseFailAlloc_3074_, 6, v___y_3005_);
lean_ctor_set(v_reuseFailAlloc_3074_, 7, v___y_3007_);
lean_ctor_set(v_reuseFailAlloc_3074_, 8, v___y_3001_);
v___x_3049_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___f_3053_; lean_object* v___x_3054_; 
v___x_3050_ = lean_box(v___x_2986_);
v___x_3051_ = lean_box(v___x_2963_);
v___x_3052_ = lean_box(v___y_2993_);
lean_inc(v___y_3000_);
lean_inc(v___y_2998_);
lean_inc(v___y_2996_);
lean_inc(v___y_2992_);
lean_inc_ref(v___y_2994_);
lean_inc_ref(v___y_2997_);
lean_inc(v___y_2995_);
v___f_3053_ = lean_alloc_closure((void*)(l_main___lam__1___boxed), 19, 18);
lean_closure_set(v___f_3053_, 0, v___x_3049_);
lean_closure_set(v___f_3053_, 1, v___y_2995_);
lean_closure_set(v___f_3053_, 2, v___x_3046_);
lean_closure_set(v___f_3053_, 3, v_name_2960_);
lean_closure_set(v___f_3053_, 4, v_a_3044_);
lean_closure_set(v___f_3053_, 5, v___x_3050_);
lean_closure_set(v___f_3053_, 6, v___y_2997_);
lean_closure_set(v___f_3053_, 7, v_head_2949_);
lean_closure_set(v___f_3053_, 8, v___y_2994_);
lean_closure_set(v___f_3053_, 9, v___x_2989_);
lean_closure_set(v___f_3053_, 10, v___y_2992_);
lean_closure_set(v___f_3053_, 11, v___y_2999_);
lean_closure_set(v___f_3053_, 12, v___y_2996_);
lean_closure_set(v___f_3053_, 13, v___x_3047_);
lean_closure_set(v___f_3053_, 14, v___y_2998_);
lean_closure_set(v___f_3053_, 15, v___y_3000_);
lean_closure_set(v___f_3053_, 16, v___x_3051_);
lean_closure_set(v___f_3053_, 17, v___x_3052_);
v___x_3054_ = l_Lean_profileitIOUnsafe___redArg(v___x_3045_, v___x_2990_, v___f_3053_, v___y_3004_);
lean_dec_ref(v___x_2990_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_object* v___x_3055_; uint8_t v___x_3056_; 
lean_dec_ref_known(v___x_3054_, 1);
v___x_3055_ = lean_display_cumulative_profiling_times();
v___x_3056_ = lean_unbox(v_fst_2971_);
lean_dec(v_fst_2971_);
if (v___x_3056_ == 0)
{
lean_dec_ref(v_env_3013_);
goto v___jp_2940_;
}
else
{
lean_object* v___x_3057_; 
v___x_3057_ = l_Lean_Environment_displayStats(v_env_3013_);
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_dec_ref_known(v___x_3057_, 1);
goto v___jp_2940_;
}
else
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3065_; 
v_a_3058_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3060_ = v___x_3057_;
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3057_);
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
else
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3073_; 
lean_dec_ref(v_env_3013_);
lean_dec(v_fst_2971_);
v_a_3066_ = lean_ctor_get(v___x_3054_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3068_ = v___x_3054_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_3054_);
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
}
else
{
lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
lean_dec_ref_known(v___x_3043_, 1);
lean_del_object(v___x_3015_);
lean_dec_ref(v_env_3013_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3004_);
lean_dec(v___y_2999_);
lean_dec_ref(v___x_2990_);
lean_dec(v_fst_2971_);
lean_dec(v_name_2960_);
lean_dec(v_head_2949_);
v___x_3075_ = ((lean_object*)(l_main___closed__16));
v___x_3076_ = lean_string_append(v___x_3075_, v_head_2953_);
lean_dec(v_head_2953_);
v___x_3077_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__1));
v___x_3078_ = lean_string_append(v___x_3076_, v___x_3077_);
v___x_3079_ = l_IO_eprintln___at___00main_spec__6(v___x_3078_);
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3087_; 
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3087_ == 0)
{
lean_object* v_unused_3088_; 
v_unused_3088_ = lean_ctor_get(v___x_3079_, 0);
lean_dec(v_unused_3088_);
v___x_3081_ = v___x_3079_;
v_isShared_3082_ = v_isSharedCheck_3087_;
goto v_resetjp_3080_;
}
else
{
lean_dec(v___x_3079_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3087_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3083_; lean_object* v___x_3085_; 
v___x_3083_ = l_main___boxed__const__1;
if (v_isShared_3082_ == 0)
{
lean_ctor_set(v___x_3081_, 0, v___x_3083_);
v___x_3085_ = v___x_3081_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v___x_3083_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
else
{
lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3096_; 
v_a_3089_ = lean_ctor_get(v___x_3079_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3091_ = v___x_3079_;
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3079_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3094_; 
if (v_isShared_3092_ == 0)
{
v___x_3094_ = v___x_3091_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_a_3089_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
}
}
else
{
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3104_; 
lean_del_object(v___x_3015_);
lean_dec_ref(v_env_3013_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3004_);
lean_dec(v___y_2999_);
lean_dec_ref(v___x_2990_);
lean_dec(v_fst_2971_);
lean_dec(v_name_2960_);
lean_dec(v_head_2953_);
lean_dec(v_head_2949_);
v_a_3097_ = lean_ctor_get(v___x_3041_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3099_ = v___x_3041_;
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3041_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3102_; 
if (v_isShared_3100_ == 0)
{
v___x_3102_ = v___x_3099_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_a_3097_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
}
}
}
}
else
{
lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3114_; 
lean_dec(v_a_3025_);
lean_del_object(v___x_3015_);
lean_dec_ref(v_env_3013_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3004_);
lean_dec(v___y_2999_);
lean_dec_ref(v___x_2990_);
lean_del_object(v___x_2974_);
lean_dec(v_fst_2971_);
lean_dec(v_name_2960_);
lean_dec(v_head_2953_);
lean_del_object(v___x_2951_);
lean_dec(v_head_2949_);
v_a_3107_ = lean_ctor_get(v___x_3026_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3109_ = v___x_3026_;
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_3026_);
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
else
{
lean_object* v_a_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3122_; 
lean_del_object(v___x_3015_);
lean_dec_ref(v_env_3013_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3004_);
lean_dec(v___y_2999_);
lean_dec_ref(v___x_2990_);
lean_del_object(v___x_2974_);
lean_dec(v_fst_2971_);
lean_dec(v_name_2960_);
lean_dec(v_head_2953_);
lean_del_object(v___x_2951_);
lean_dec(v_head_2949_);
v_a_3115_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3117_ = v___x_3024_;
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_a_3115_);
lean_dec(v___x_3024_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3120_; 
if (v_isShared_3118_ == 0)
{
v___x_3120_ = v___x_3117_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_a_3115_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
}
else
{
lean_object* v___x_3123_; lean_object* v___x_3125_; 
lean_del_object(v___x_3015_);
lean_dec_ref(v_env_3013_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3004_);
lean_dec(v___y_2999_);
lean_dec_ref(v___x_2990_);
lean_del_object(v___x_2974_);
lean_dec(v_fst_2971_);
lean_dec(v_name_2960_);
lean_dec(v_head_2953_);
lean_del_object(v___x_2951_);
lean_dec(v_head_2949_);
v___x_3123_ = l_main___boxed__const__1;
if (v_isShared_3022_ == 0)
{
lean_ctor_set(v___x_3021_, 0, v___x_3123_);
v___x_3125_ = v___x_3021_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v___x_3123_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
}
else
{
lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3136_; 
lean_del_object(v___x_3015_);
lean_dec_ref(v_env_3013_);
lean_dec_ref(v_messages_3012_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3004_);
lean_dec(v___y_2999_);
lean_dec_ref(v___x_2990_);
lean_del_object(v___x_2974_);
lean_dec(v_fst_2971_);
lean_dec(v_name_2960_);
lean_dec(v_head_2953_);
lean_del_object(v___x_2951_);
lean_dec(v_head_2949_);
v_a_3129_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3131_ = v___x_3019_;
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_3019_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3134_; 
if (v_isShared_3132_ == 0)
{
v___x_3134_ = v___x_3131_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_a_3129_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
}
}
v___jp_3145_:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; size_t v_sz_3179_; size_t v___x_3180_; lean_object* v___x_3181_; 
lean_inc_ref(v___y_3163_);
v___x_3176_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3176_, 0, v___y_3175_);
lean_ctor_set(v___x_3176_, 1, v_nextMacroScope_3156_);
lean_ctor_set(v___x_3176_, 2, v_ngen_3157_);
lean_ctor_set(v___x_3176_, 3, v_auxDeclNGen_3158_);
lean_ctor_set(v___x_3176_, 4, v_traceState_3159_);
lean_ctor_set(v___x_3176_, 5, v___y_3163_);
lean_ctor_set(v___x_3176_, 6, v_messages_3160_);
lean_ctor_set(v___x_3176_, 7, v_infoState_3161_);
lean_ctor_set(v___x_3176_, 8, v_snapshotTasks_3162_);
v___x_3177_ = lean_st_ref_set(v___y_3174_, v___x_3176_);
v___x_3178_ = lean_box(0);
v_sz_3179_ = lean_array_size(v___y_3164_);
v___x_3180_ = ((size_t)0ULL);
v___x_3181_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(v___y_3164_, v_sz_3179_, v___x_3180_, v___x_3178_, v___y_3169_, v___y_3174_);
lean_dec_ref(v___y_3164_);
if (lean_obj_tag(v___x_3181_) == 0)
{
lean_dec_ref_known(v___x_3181_, 1);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3169_);
v___y_2992_ = v___y_3146_;
v___y_2993_ = v___y_3147_;
v___y_2994_ = v___y_3149_;
v___y_2995_ = v___y_3148_;
v___y_2996_ = v___y_3151_;
v___y_2997_ = v___y_3150_;
v___y_2998_ = v___y_3152_;
v___y_2999_ = v___y_3153_;
v___y_3000_ = v___y_3154_;
v___y_3001_ = v___y_3170_;
v___y_3002_ = v___y_3155_;
v___y_3003_ = v___y_3163_;
v___y_3004_ = v___y_3165_;
v___y_3005_ = v___y_3171_;
v___y_3006_ = v___y_3166_;
v___y_3007_ = v___y_3167_;
v___y_3008_ = v___y_3168_;
v___y_3009_ = v___y_3173_;
v___y_3010_ = v___y_3172_;
goto v___jp_2991_;
}
else
{
if (lean_obj_tag(v___x_3181_) == 0)
{
lean_dec_ref_known(v___x_3181_, 1);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3169_);
v___y_2992_ = v___y_3146_;
v___y_2993_ = v___y_3147_;
v___y_2994_ = v___y_3149_;
v___y_2995_ = v___y_3148_;
v___y_2996_ = v___y_3151_;
v___y_2997_ = v___y_3150_;
v___y_2998_ = v___y_3152_;
v___y_2999_ = v___y_3153_;
v___y_3000_ = v___y_3154_;
v___y_3001_ = v___y_3170_;
v___y_3002_ = v___y_3155_;
v___y_3003_ = v___y_3163_;
v___y_3004_ = v___y_3165_;
v___y_3005_ = v___y_3171_;
v___y_3006_ = v___y_3166_;
v___y_3007_ = v___y_3167_;
v___y_3008_ = v___y_3168_;
v___y_3009_ = v___y_3173_;
v___y_3010_ = v___y_3172_;
goto v___jp_2991_;
}
else
{
lean_object* v_a_3182_; uint8_t v___x_3183_; 
v_a_3182_ = lean_ctor_get(v___x_3181_, 0);
lean_inc(v_a_3182_);
lean_dec_ref_known(v___x_3181_, 1);
v___x_3183_ = l_Lean_Exception_isInterrupt(v_a_3182_);
if (v___x_3183_ == 0)
{
lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3184_ = l_Lean_Exception_toMessageData(v_a_3182_);
v___x_3185_ = l_Lean_logError___at___00main_spec__14(v___x_3184_, v___y_3169_, v___y_3174_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3169_);
if (lean_obj_tag(v___x_3185_) == 0)
{
lean_dec_ref_known(v___x_3185_, 1);
v___y_2992_ = v___y_3146_;
v___y_2993_ = v___y_3147_;
v___y_2994_ = v___y_3149_;
v___y_2995_ = v___y_3148_;
v___y_2996_ = v___y_3151_;
v___y_2997_ = v___y_3150_;
v___y_2998_ = v___y_3152_;
v___y_2999_ = v___y_3153_;
v___y_3000_ = v___y_3154_;
v___y_3001_ = v___y_3170_;
v___y_3002_ = v___y_3155_;
v___y_3003_ = v___y_3163_;
v___y_3004_ = v___y_3165_;
v___y_3005_ = v___y_3171_;
v___y_3006_ = v___y_3166_;
v___y_3007_ = v___y_3167_;
v___y_3008_ = v___y_3168_;
v___y_3009_ = v___y_3173_;
v___y_3010_ = v___y_3172_;
goto v___jp_2991_;
}
else
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
lean_dec_ref_known(v___x_3185_, 1);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec(v___y_3153_);
lean_dec_ref(v___x_2990_);
lean_del_object(v___x_2974_);
lean_dec(v_fst_2971_);
lean_dec(v_name_2960_);
lean_dec(v_head_2953_);
lean_del_object(v___x_2951_);
lean_dec(v_head_2949_);
v___x_3186_ = lean_obj_once(&l_main___closed__20, &l_main___closed__20_once, _init_l_main___closed__20);
v___x_3187_ = l_panic___at___00main_spec__5(v___x_3186_);
return v___x_3187_;
}
}
else
{
lean_dec(v_a_3182_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3169_);
v___y_2992_ = v___y_3146_;
v___y_2993_ = v___y_3147_;
v___y_2994_ = v___y_3149_;
v___y_2995_ = v___y_3148_;
v___y_2996_ = v___y_3151_;
v___y_2997_ = v___y_3150_;
v___y_2998_ = v___y_3152_;
v___y_2999_ = v___y_3153_;
v___y_3000_ = v___y_3154_;
v___y_3001_ = v___y_3170_;
v___y_3002_ = v___y_3155_;
v___y_3003_ = v___y_3163_;
v___y_3004_ = v___y_3165_;
v___y_3005_ = v___y_3171_;
v___y_3006_ = v___y_3166_;
v___y_3007_ = v___y_3167_;
v___y_3008_ = v___y_3168_;
v___y_3009_ = v___y_3173_;
v___y_3010_ = v___y_3172_;
goto v___jp_2991_;
}
}
}
}
v___jp_3188_:
{
lean_object* v___x_3213_; lean_object* v_fileName_3214_; lean_object* v_fileMap_3215_; lean_object* v_currRecDepth_3216_; lean_object* v_ref_3217_; lean_object* v_currNamespace_3218_; lean_object* v_openDecls_3219_; lean_object* v_initHeartbeats_3220_; lean_object* v_maxHeartbeats_3221_; lean_object* v_quotContext_3222_; lean_object* v_currMacroScope_3223_; lean_object* v_cancelTk_x3f_3224_; uint8_t v_suppressElabErrors_3225_; lean_object* v_inheritedTraceOptions_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3256_; 
v___x_3213_ = lean_st_ref_take(v___y_3212_);
v_fileName_3214_ = lean_ctor_get(v___y_3211_, 0);
v_fileMap_3215_ = lean_ctor_get(v___y_3211_, 1);
v_currRecDepth_3216_ = lean_ctor_get(v___y_3211_, 3);
v_ref_3217_ = lean_ctor_get(v___y_3211_, 5);
v_currNamespace_3218_ = lean_ctor_get(v___y_3211_, 6);
v_openDecls_3219_ = lean_ctor_get(v___y_3211_, 7);
v_initHeartbeats_3220_ = lean_ctor_get(v___y_3211_, 8);
v_maxHeartbeats_3221_ = lean_ctor_get(v___y_3211_, 9);
v_quotContext_3222_ = lean_ctor_get(v___y_3211_, 10);
v_currMacroScope_3223_ = lean_ctor_get(v___y_3211_, 11);
v_cancelTk_x3f_3224_ = lean_ctor_get(v___y_3211_, 12);
v_suppressElabErrors_3225_ = lean_ctor_get_uint8(v___y_3211_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3226_ = lean_ctor_get(v___y_3211_, 13);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___y_3211_);
if (v_isSharedCheck_3256_ == 0)
{
lean_object* v_unused_3257_; lean_object* v_unused_3258_; 
v_unused_3257_ = lean_ctor_get(v___y_3211_, 4);
lean_dec(v_unused_3257_);
v_unused_3258_ = lean_ctor_get(v___y_3211_, 2);
lean_dec(v_unused_3258_);
v___x_3228_ = v___y_3211_;
v_isShared_3229_ = v_isSharedCheck_3256_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_inheritedTraceOptions_3226_);
lean_inc(v_cancelTk_x3f_3224_);
lean_inc(v_currMacroScope_3223_);
lean_inc(v_quotContext_3222_);
lean_inc(v_maxHeartbeats_3221_);
lean_inc(v_initHeartbeats_3220_);
lean_inc(v_openDecls_3219_);
lean_inc(v_currNamespace_3218_);
lean_inc(v_ref_3217_);
lean_inc(v_currRecDepth_3216_);
lean_inc(v_fileMap_3215_);
lean_inc(v_fileName_3214_);
lean_dec(v___y_3211_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3256_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v_env_3230_; lean_object* v_nextMacroScope_3231_; lean_object* v_ngen_3232_; lean_object* v_auxDeclNGen_3233_; lean_object* v_traceState_3234_; lean_object* v_messages_3235_; lean_object* v_infoState_3236_; lean_object* v_snapshotTasks_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3241_; 
v_env_3230_ = lean_ctor_get(v___x_3213_, 0);
lean_inc_ref(v_env_3230_);
v_nextMacroScope_3231_ = lean_ctor_get(v___x_3213_, 1);
lean_inc(v_nextMacroScope_3231_);
v_ngen_3232_ = lean_ctor_get(v___x_3213_, 2);
lean_inc_ref(v_ngen_3232_);
v_auxDeclNGen_3233_ = lean_ctor_get(v___x_3213_, 3);
lean_inc_ref(v_auxDeclNGen_3233_);
v_traceState_3234_ = lean_ctor_get(v___x_3213_, 4);
lean_inc_ref(v_traceState_3234_);
v_messages_3235_ = lean_ctor_get(v___x_3213_, 6);
lean_inc_ref(v_messages_3235_);
v_infoState_3236_ = lean_ctor_get(v___x_3213_, 7);
lean_inc_ref(v_infoState_3236_);
v_snapshotTasks_3237_ = lean_ctor_get(v___x_3213_, 8);
lean_inc_ref(v_snapshotTasks_3237_);
lean_dec(v___x_3213_);
v___x_3238_ = l_Lean_maxRecDepth;
v___x_3239_ = l_Lean_Option_get___at___00main_spec__9(v___x_2990_, v___x_3238_);
lean_inc_ref(v___x_2990_);
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 4, v___x_3239_);
lean_ctor_set(v___x_3228_, 2, v___x_2990_);
v___x_3241_ = v___x_3228_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_fileName_3214_);
lean_ctor_set(v_reuseFailAlloc_3255_, 1, v_fileMap_3215_);
lean_ctor_set(v_reuseFailAlloc_3255_, 2, v___x_2990_);
lean_ctor_set(v_reuseFailAlloc_3255_, 3, v_currRecDepth_3216_);
lean_ctor_set(v_reuseFailAlloc_3255_, 4, v___x_3239_);
lean_ctor_set(v_reuseFailAlloc_3255_, 5, v_ref_3217_);
lean_ctor_set(v_reuseFailAlloc_3255_, 6, v_currNamespace_3218_);
lean_ctor_set(v_reuseFailAlloc_3255_, 7, v_openDecls_3219_);
lean_ctor_set(v_reuseFailAlloc_3255_, 8, v_initHeartbeats_3220_);
lean_ctor_set(v_reuseFailAlloc_3255_, 9, v_maxHeartbeats_3221_);
lean_ctor_set(v_reuseFailAlloc_3255_, 10, v_quotContext_3222_);
lean_ctor_set(v_reuseFailAlloc_3255_, 11, v_currMacroScope_3223_);
lean_ctor_set(v_reuseFailAlloc_3255_, 12, v_cancelTk_x3f_3224_);
lean_ctor_set(v_reuseFailAlloc_3255_, 13, v_inheritedTraceOptions_3226_);
lean_ctor_set_uint8(v_reuseFailAlloc_3255_, sizeof(void*)*14 + 1, v_suppressElabErrors_3225_);
v___x_3241_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
lean_object* v___x_3242_; uint8_t v___x_3243_; 
lean_ctor_set_uint8(v___x_3241_, sizeof(void*)*14, v___y_3208_);
v___x_3242_ = lean_array_get_size(v___y_3200_);
v___x_3243_ = lean_nat_dec_lt(v___x_2989_, v___x_3242_);
if (v___x_3243_ == 0)
{
lean_object* v___x_3244_; 
lean_inc_ref(v___y_3205_);
v___x_3244_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3205_, v_env_3230_, v___x_2983_);
v___y_3146_ = v___y_3189_;
v___y_3147_ = v___y_3190_;
v___y_3148_ = v___y_3192_;
v___y_3149_ = v___y_3191_;
v___y_3150_ = v___y_3194_;
v___y_3151_ = v___y_3193_;
v___y_3152_ = v___y_3195_;
v___y_3153_ = v___y_3196_;
v___y_3154_ = v___y_3197_;
v___y_3155_ = v___y_3198_;
v_nextMacroScope_3156_ = v_nextMacroScope_3231_;
v_ngen_3157_ = v_ngen_3232_;
v_auxDeclNGen_3158_ = v_auxDeclNGen_3233_;
v_traceState_3159_ = v_traceState_3234_;
v_messages_3160_ = v_messages_3235_;
v_infoState_3161_ = v_infoState_3236_;
v_snapshotTasks_3162_ = v_snapshotTasks_3237_;
v___y_3163_ = v___y_3199_;
v___y_3164_ = v___y_3200_;
v___y_3165_ = v___y_3201_;
v___y_3166_ = v___y_3202_;
v___y_3167_ = v___y_3203_;
v___y_3168_ = v___y_3204_;
v___y_3169_ = v___x_3241_;
v___y_3170_ = v___y_3206_;
v___y_3171_ = v___y_3207_;
v___y_3172_ = v___y_3209_;
v___y_3173_ = v___y_3210_;
v___y_3174_ = v___y_3212_;
v___y_3175_ = v___x_3244_;
goto v___jp_3145_;
}
else
{
uint8_t v___x_3245_; 
v___x_3245_ = lean_nat_dec_le(v___x_3242_, v___x_3242_);
if (v___x_3245_ == 0)
{
if (v___x_3243_ == 0)
{
lean_object* v___x_3246_; 
lean_inc_ref(v___y_3205_);
v___x_3246_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3205_, v_env_3230_, v___x_2983_);
v___y_3146_ = v___y_3189_;
v___y_3147_ = v___y_3190_;
v___y_3148_ = v___y_3192_;
v___y_3149_ = v___y_3191_;
v___y_3150_ = v___y_3194_;
v___y_3151_ = v___y_3193_;
v___y_3152_ = v___y_3195_;
v___y_3153_ = v___y_3196_;
v___y_3154_ = v___y_3197_;
v___y_3155_ = v___y_3198_;
v_nextMacroScope_3156_ = v_nextMacroScope_3231_;
v_ngen_3157_ = v_ngen_3232_;
v_auxDeclNGen_3158_ = v_auxDeclNGen_3233_;
v_traceState_3159_ = v_traceState_3234_;
v_messages_3160_ = v_messages_3235_;
v_infoState_3161_ = v_infoState_3236_;
v_snapshotTasks_3162_ = v_snapshotTasks_3237_;
v___y_3163_ = v___y_3199_;
v___y_3164_ = v___y_3200_;
v___y_3165_ = v___y_3201_;
v___y_3166_ = v___y_3202_;
v___y_3167_ = v___y_3203_;
v___y_3168_ = v___y_3204_;
v___y_3169_ = v___x_3241_;
v___y_3170_ = v___y_3206_;
v___y_3171_ = v___y_3207_;
v___y_3172_ = v___y_3209_;
v___y_3173_ = v___y_3210_;
v___y_3174_ = v___y_3212_;
v___y_3175_ = v___x_3246_;
goto v___jp_3145_;
}
else
{
size_t v___x_3247_; size_t v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3247_ = ((size_t)0ULL);
v___x_3248_ = lean_usize_of_nat(v___x_3242_);
v___x_3249_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3200_, v___x_3247_, v___x_3248_, v___x_2983_);
lean_inc_ref(v___y_3205_);
v___x_3250_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3205_, v_env_3230_, v___x_3249_);
v___y_3146_ = v___y_3189_;
v___y_3147_ = v___y_3190_;
v___y_3148_ = v___y_3192_;
v___y_3149_ = v___y_3191_;
v___y_3150_ = v___y_3194_;
v___y_3151_ = v___y_3193_;
v___y_3152_ = v___y_3195_;
v___y_3153_ = v___y_3196_;
v___y_3154_ = v___y_3197_;
v___y_3155_ = v___y_3198_;
v_nextMacroScope_3156_ = v_nextMacroScope_3231_;
v_ngen_3157_ = v_ngen_3232_;
v_auxDeclNGen_3158_ = v_auxDeclNGen_3233_;
v_traceState_3159_ = v_traceState_3234_;
v_messages_3160_ = v_messages_3235_;
v_infoState_3161_ = v_infoState_3236_;
v_snapshotTasks_3162_ = v_snapshotTasks_3237_;
v___y_3163_ = v___y_3199_;
v___y_3164_ = v___y_3200_;
v___y_3165_ = v___y_3201_;
v___y_3166_ = v___y_3202_;
v___y_3167_ = v___y_3203_;
v___y_3168_ = v___y_3204_;
v___y_3169_ = v___x_3241_;
v___y_3170_ = v___y_3206_;
v___y_3171_ = v___y_3207_;
v___y_3172_ = v___y_3209_;
v___y_3173_ = v___y_3210_;
v___y_3174_ = v___y_3212_;
v___y_3175_ = v___x_3250_;
goto v___jp_3145_;
}
}
else
{
size_t v___x_3251_; size_t v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
v___x_3251_ = ((size_t)0ULL);
v___x_3252_ = lean_usize_of_nat(v___x_3242_);
v___x_3253_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3200_, v___x_3251_, v___x_3252_, v___x_2983_);
lean_inc_ref(v___y_3205_);
v___x_3254_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3205_, v_env_3230_, v___x_3253_);
v___y_3146_ = v___y_3189_;
v___y_3147_ = v___y_3190_;
v___y_3148_ = v___y_3192_;
v___y_3149_ = v___y_3191_;
v___y_3150_ = v___y_3194_;
v___y_3151_ = v___y_3193_;
v___y_3152_ = v___y_3195_;
v___y_3153_ = v___y_3196_;
v___y_3154_ = v___y_3197_;
v___y_3155_ = v___y_3198_;
v_nextMacroScope_3156_ = v_nextMacroScope_3231_;
v_ngen_3157_ = v_ngen_3232_;
v_auxDeclNGen_3158_ = v_auxDeclNGen_3233_;
v_traceState_3159_ = v_traceState_3234_;
v_messages_3160_ = v_messages_3235_;
v_infoState_3161_ = v_infoState_3236_;
v_snapshotTasks_3162_ = v_snapshotTasks_3237_;
v___y_3163_ = v___y_3199_;
v___y_3164_ = v___y_3200_;
v___y_3165_ = v___y_3201_;
v___y_3166_ = v___y_3202_;
v___y_3167_ = v___y_3203_;
v___y_3168_ = v___y_3204_;
v___y_3169_ = v___x_3241_;
v___y_3170_ = v___y_3206_;
v___y_3171_ = v___y_3207_;
v___y_3172_ = v___y_3209_;
v___y_3173_ = v___y_3210_;
v___y_3174_ = v___y_3212_;
v___y_3175_ = v___x_3254_;
goto v___jp_3145_;
}
}
}
}
}
v___jp_3259_:
{
if (v___y_3283_ == 0)
{
lean_object* v___x_3284_; lean_object* v_env_3285_; lean_object* v_nextMacroScope_3286_; lean_object* v_ngen_3287_; lean_object* v_auxDeclNGen_3288_; lean_object* v_traceState_3289_; lean_object* v_messages_3290_; lean_object* v_infoState_3291_; lean_object* v_snapshotTasks_3292_; lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3301_; 
v___x_3284_ = lean_st_ref_take(v___y_3273_);
v_env_3285_ = lean_ctor_get(v___x_3284_, 0);
v_nextMacroScope_3286_ = lean_ctor_get(v___x_3284_, 1);
v_ngen_3287_ = lean_ctor_get(v___x_3284_, 2);
v_auxDeclNGen_3288_ = lean_ctor_get(v___x_3284_, 3);
v_traceState_3289_ = lean_ctor_get(v___x_3284_, 4);
v_messages_3290_ = lean_ctor_get(v___x_3284_, 6);
v_infoState_3291_ = lean_ctor_get(v___x_3284_, 7);
v_snapshotTasks_3292_ = lean_ctor_get(v___x_3284_, 8);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3284_);
if (v_isSharedCheck_3301_ == 0)
{
lean_object* v_unused_3302_; 
v_unused_3302_ = lean_ctor_get(v___x_3284_, 5);
lean_dec(v_unused_3302_);
v___x_3294_ = v___x_3284_;
v_isShared_3295_ = v_isSharedCheck_3301_;
goto v_resetjp_3293_;
}
else
{
lean_inc(v_snapshotTasks_3292_);
lean_inc(v_infoState_3291_);
lean_inc(v_messages_3290_);
lean_inc(v_traceState_3289_);
lean_inc(v_auxDeclNGen_3288_);
lean_inc(v_ngen_3287_);
lean_inc(v_nextMacroScope_3286_);
lean_inc(v_env_3285_);
lean_dec(v___x_3284_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3301_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
lean_object* v___x_3296_; lean_object* v___x_3298_; 
v___x_3296_ = l_Lean_Kernel_enableDiag(v_env_3285_, v___y_3280_);
lean_inc_ref(v___y_3270_);
if (v_isShared_3295_ == 0)
{
lean_ctor_set(v___x_3294_, 5, v___y_3270_);
lean_ctor_set(v___x_3294_, 0, v___x_3296_);
v___x_3298_ = v___x_3294_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v___x_3296_);
lean_ctor_set(v_reuseFailAlloc_3300_, 1, v_nextMacroScope_3286_);
lean_ctor_set(v_reuseFailAlloc_3300_, 2, v_ngen_3287_);
lean_ctor_set(v_reuseFailAlloc_3300_, 3, v_auxDeclNGen_3288_);
lean_ctor_set(v_reuseFailAlloc_3300_, 4, v_traceState_3289_);
lean_ctor_set(v_reuseFailAlloc_3300_, 5, v___y_3270_);
lean_ctor_set(v_reuseFailAlloc_3300_, 6, v_messages_3290_);
lean_ctor_set(v_reuseFailAlloc_3300_, 7, v_infoState_3291_);
lean_ctor_set(v_reuseFailAlloc_3300_, 8, v_snapshotTasks_3292_);
v___x_3298_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
lean_object* v___x_3299_; 
v___x_3299_ = lean_st_ref_set(v___y_3273_, v___x_3298_);
lean_inc(v___y_3273_);
v___y_3189_ = v___y_3260_;
v___y_3190_ = v___y_3261_;
v___y_3191_ = v___y_3263_;
v___y_3192_ = v___y_3262_;
v___y_3193_ = v___y_3265_;
v___y_3194_ = v___y_3264_;
v___y_3195_ = v___y_3266_;
v___y_3196_ = v___y_3267_;
v___y_3197_ = v___y_3268_;
v___y_3198_ = v___y_3269_;
v___y_3199_ = v___y_3270_;
v___y_3200_ = v___y_3271_;
v___y_3201_ = v___y_3272_;
v___y_3202_ = v___y_3273_;
v___y_3203_ = v___y_3274_;
v___y_3204_ = v___y_3275_;
v___y_3205_ = v___y_3277_;
v___y_3206_ = v___y_3278_;
v___y_3207_ = v___y_3279_;
v___y_3208_ = v___y_3280_;
v___y_3209_ = v___y_3282_;
v___y_3210_ = v___y_3281_;
v___y_3211_ = v___y_3276_;
v___y_3212_ = v___y_3273_;
goto v___jp_3188_;
}
}
}
else
{
lean_inc(v___y_3273_);
v___y_3189_ = v___y_3260_;
v___y_3190_ = v___y_3261_;
v___y_3191_ = v___y_3263_;
v___y_3192_ = v___y_3262_;
v___y_3193_ = v___y_3265_;
v___y_3194_ = v___y_3264_;
v___y_3195_ = v___y_3266_;
v___y_3196_ = v___y_3267_;
v___y_3197_ = v___y_3268_;
v___y_3198_ = v___y_3269_;
v___y_3199_ = v___y_3270_;
v___y_3200_ = v___y_3271_;
v___y_3201_ = v___y_3272_;
v___y_3202_ = v___y_3273_;
v___y_3203_ = v___y_3274_;
v___y_3204_ = v___y_3275_;
v___y_3205_ = v___y_3277_;
v___y_3206_ = v___y_3278_;
v___y_3207_ = v___y_3279_;
v___y_3208_ = v___y_3280_;
v___y_3209_ = v___y_3282_;
v___y_3210_ = v___y_3281_;
v___y_3211_ = v___y_3276_;
v___y_3212_ = v___y_3273_;
goto v___jp_3188_;
}
}
v___jp_3309_:
{
lean_object* v___x_3318_; 
if (v_isShared_2948_ == 0)
{
lean_ctor_set_tag(v___x_2947_, 0);
lean_ctor_set(v___x_2947_, 1, v___y_3316_);
lean_ctor_set(v___x_2947_, 0, v___y_3315_);
v___x_3318_ = v___x_2947_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v___y_3315_);
lean_ctor_set(v_reuseFailAlloc_3413_, 1, v___y_3316_);
v___x_3318_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v_moduleData_3322_; lean_object* v___x_3323_; uint8_t v___x_3324_; 
v___x_3319_ = lean_box(0);
lean_inc_ref(v___y_3314_);
v___x_3320_ = l_Lean_EnvExtension_setState___redArg(v___y_3314_, v___y_3311_, v___x_3318_, v___x_3319_);
v___x_3321_ = l_Lean_Environment_header(v___x_3320_);
v_moduleData_3322_ = lean_ctor_get(v___x_3321_, 6);
lean_inc_ref(v_moduleData_3322_);
lean_dec_ref(v___x_3321_);
v___x_3323_ = lean_array_get_size(v_moduleData_3322_);
v___x_3324_ = lean_nat_dec_lt(v___y_3312_, v___x_3323_);
if (v___x_3324_ == 0)
{
lean_object* v___x_3325_; lean_object* v___x_3326_; 
lean_dec_ref(v_moduleData_3322_);
lean_dec_ref(v___x_3320_);
lean_dec(v___y_3313_);
lean_dec(v___y_3312_);
lean_dec(v___y_3310_);
lean_dec_ref(v___x_2990_);
lean_del_object(v___x_2974_);
lean_dec(v_fst_2971_);
lean_dec(v_name_2960_);
lean_dec(v_head_2953_);
lean_del_object(v___x_2951_);
lean_dec(v_head_2949_);
v___x_3325_ = lean_obj_once(&l_main___closed__22, &l_main___closed__22_once, _init_l_main___closed__22);
v___x_3326_ = l_panic___at___00main_spec__5(v___x_3325_);
return v___x_3326_;
}
else
{
lean_object* v_base_3327_; lean_object* v_private_3328_; lean_object* v_header_3329_; lean_object* v_serverBaseExts_3330_; lean_object* v_checked_3331_; lean_object* v_asyncConstsMap_3332_; lean_object* v_asyncCtx_x3f_3333_; lean_object* v_importRealizationCtx_x3f_3334_; lean_object* v_localRealizationCtxMap_3335_; lean_object* v_allRealizations_3336_; uint8_t v_isExporting_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3411_; 
v_base_3327_ = lean_ctor_get(v___x_3320_, 0);
lean_inc_ref(v_base_3327_);
v_private_3328_ = lean_ctor_get(v_base_3327_, 0);
lean_inc(v_private_3328_);
v_header_3329_ = lean_ctor_get(v_private_3328_, 5);
lean_inc_ref(v_header_3329_);
v_serverBaseExts_3330_ = lean_ctor_get(v___x_3320_, 1);
v_checked_3331_ = lean_ctor_get(v___x_3320_, 2);
v_asyncConstsMap_3332_ = lean_ctor_get(v___x_3320_, 3);
v_asyncCtx_x3f_3333_ = lean_ctor_get(v___x_3320_, 4);
v_importRealizationCtx_x3f_3334_ = lean_ctor_get(v___x_3320_, 5);
v_localRealizationCtxMap_3335_ = lean_ctor_get(v___x_3320_, 6);
v_allRealizations_3336_ = lean_ctor_get(v___x_3320_, 7);
v_isExporting_3337_ = lean_ctor_get_uint8(v___x_3320_, sizeof(void*)*8);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3320_);
if (v_isSharedCheck_3411_ == 0)
{
lean_object* v_unused_3412_; 
v_unused_3412_ = lean_ctor_get(v___x_3320_, 0);
lean_dec(v_unused_3412_);
v___x_3339_ = v___x_3320_;
v_isShared_3340_ = v_isSharedCheck_3411_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_allRealizations_3336_);
lean_inc(v_localRealizationCtxMap_3335_);
lean_inc(v_importRealizationCtx_x3f_3334_);
lean_inc(v_asyncCtx_x3f_3333_);
lean_inc(v_asyncConstsMap_3332_);
lean_inc(v_checked_3331_);
lean_inc(v_serverBaseExts_3330_);
lean_dec(v___x_3320_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3411_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v_public_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3409_; 
v_public_3341_ = lean_ctor_get(v_base_3327_, 1);
v_isSharedCheck_3409_ = !lean_is_exclusive(v_base_3327_);
if (v_isSharedCheck_3409_ == 0)
{
lean_object* v_unused_3410_; 
v_unused_3410_ = lean_ctor_get(v_base_3327_, 0);
lean_dec(v_unused_3410_);
v___x_3343_ = v_base_3327_;
v_isShared_3344_ = v_isSharedCheck_3409_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_public_3341_);
lean_dec(v_base_3327_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3409_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v_constants_3345_; uint8_t v_quotInit_3346_; lean_object* v_diagnostics_3347_; lean_object* v_const2ModIdx_3348_; lean_object* v_extensions_3349_; lean_object* v_irBaseExts_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3407_; 
v_constants_3345_ = lean_ctor_get(v_private_3328_, 0);
v_quotInit_3346_ = lean_ctor_get_uint8(v_private_3328_, sizeof(void*)*6);
v_diagnostics_3347_ = lean_ctor_get(v_private_3328_, 1);
v_const2ModIdx_3348_ = lean_ctor_get(v_private_3328_, 2);
v_extensions_3349_ = lean_ctor_get(v_private_3328_, 3);
v_irBaseExts_3350_ = lean_ctor_get(v_private_3328_, 4);
v_isSharedCheck_3407_ = !lean_is_exclusive(v_private_3328_);
if (v_isSharedCheck_3407_ == 0)
{
lean_object* v_unused_3408_; 
v_unused_3408_ = lean_ctor_get(v_private_3328_, 5);
lean_dec(v_unused_3408_);
v___x_3352_ = v_private_3328_;
v_isShared_3353_ = v_isSharedCheck_3407_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_irBaseExts_3350_);
lean_inc(v_extensions_3349_);
lean_inc(v_const2ModIdx_3348_);
lean_inc(v_diagnostics_3347_);
lean_inc(v_constants_3345_);
lean_dec(v_private_3328_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3407_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
uint32_t v_trustLevel_3354_; lean_object* v_mainModule_3355_; uint8_t v_isModule_3356_; lean_object* v_regions_3357_; lean_object* v_modules_3358_; lean_object* v_moduleName2Idx_3359_; lean_object* v_importAllModules_3360_; lean_object* v_moduleData_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3405_; 
v_trustLevel_3354_ = lean_ctor_get_uint32(v_header_3329_, sizeof(void*)*7);
v_mainModule_3355_ = lean_ctor_get(v_header_3329_, 0);
v_isModule_3356_ = lean_ctor_get_uint8(v_header_3329_, sizeof(void*)*7 + 4);
v_regions_3357_ = lean_ctor_get(v_header_3329_, 2);
v_modules_3358_ = lean_ctor_get(v_header_3329_, 3);
v_moduleName2Idx_3359_ = lean_ctor_get(v_header_3329_, 4);
v_importAllModules_3360_ = lean_ctor_get(v_header_3329_, 5);
v_moduleData_3361_ = lean_ctor_get(v_header_3329_, 6);
v_isSharedCheck_3405_ = !lean_is_exclusive(v_header_3329_);
if (v_isSharedCheck_3405_ == 0)
{
lean_object* v_unused_3406_; 
v_unused_3406_ = lean_ctor_get(v_header_3329_, 1);
lean_dec(v_unused_3406_);
v___x_3363_ = v_header_3329_;
v_isShared_3364_ = v_isSharedCheck_3405_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_moduleData_3361_);
lean_inc(v_importAllModules_3360_);
lean_inc(v_moduleName2Idx_3359_);
lean_inc(v_modules_3358_);
lean_inc(v_regions_3357_);
lean_inc(v_mainModule_3355_);
lean_dec(v_header_3329_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3405_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3365_; lean_object* v_imports_3366_; lean_object* v___x_3368_; 
v___x_3365_ = lean_array_fget(v_moduleData_3322_, v___y_3312_);
lean_dec_ref(v_moduleData_3322_);
v_imports_3366_ = lean_ctor_get(v___x_3365_, 0);
lean_inc_ref(v_imports_3366_);
lean_dec(v___x_3365_);
if (v_isShared_3364_ == 0)
{
lean_ctor_set(v___x_3363_, 1, v_imports_3366_);
v___x_3368_ = v___x_3363_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(0, 7, 5);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_mainModule_3355_);
lean_ctor_set(v_reuseFailAlloc_3404_, 1, v_imports_3366_);
lean_ctor_set(v_reuseFailAlloc_3404_, 2, v_regions_3357_);
lean_ctor_set(v_reuseFailAlloc_3404_, 3, v_modules_3358_);
lean_ctor_set(v_reuseFailAlloc_3404_, 4, v_moduleName2Idx_3359_);
lean_ctor_set(v_reuseFailAlloc_3404_, 5, v_importAllModules_3360_);
lean_ctor_set(v_reuseFailAlloc_3404_, 6, v_moduleData_3361_);
lean_ctor_set_uint32(v_reuseFailAlloc_3404_, sizeof(void*)*7, v_trustLevel_3354_);
lean_ctor_set_uint8(v_reuseFailAlloc_3404_, sizeof(void*)*7 + 4, v_isModule_3356_);
v___x_3368_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
lean_object* v___x_3370_; 
if (v_isShared_3353_ == 0)
{
lean_ctor_set(v___x_3352_, 5, v___x_3368_);
v___x_3370_ = v___x_3352_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v_constants_3345_);
lean_ctor_set(v_reuseFailAlloc_3403_, 1, v_diagnostics_3347_);
lean_ctor_set(v_reuseFailAlloc_3403_, 2, v_const2ModIdx_3348_);
lean_ctor_set(v_reuseFailAlloc_3403_, 3, v_extensions_3349_);
lean_ctor_set(v_reuseFailAlloc_3403_, 4, v_irBaseExts_3350_);
lean_ctor_set(v_reuseFailAlloc_3403_, 5, v___x_3368_);
lean_ctor_set_uint8(v_reuseFailAlloc_3403_, sizeof(void*)*6, v_quotInit_3346_);
v___x_3370_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
lean_object* v___x_3372_; 
if (v_isShared_3344_ == 0)
{
lean_ctor_set(v___x_3343_, 0, v___x_3370_);
v___x_3372_ = v___x_3343_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v___x_3370_);
lean_ctor_set(v_reuseFailAlloc_3402_, 1, v_public_3341_);
v___x_3372_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
lean_object* v___x_3374_; 
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 0, v___x_3372_);
v___x_3374_ = v___x_3339_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v___x_3372_);
lean_ctor_set(v_reuseFailAlloc_3401_, 1, v_serverBaseExts_3330_);
lean_ctor_set(v_reuseFailAlloc_3401_, 2, v_checked_3331_);
lean_ctor_set(v_reuseFailAlloc_3401_, 3, v_asyncConstsMap_3332_);
lean_ctor_set(v_reuseFailAlloc_3401_, 4, v_asyncCtx_x3f_3333_);
lean_ctor_set(v_reuseFailAlloc_3401_, 5, v_importRealizationCtx_x3f_3334_);
lean_ctor_set(v_reuseFailAlloc_3401_, 6, v_localRealizationCtxMap_3335_);
lean_ctor_set(v_reuseFailAlloc_3401_, 7, v_allRealizations_3336_);
lean_ctor_set_uint8(v_reuseFailAlloc_3401_, sizeof(void*)*8, v_isExporting_3337_);
v___x_3374_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v_env_3397_; lean_object* v___x_3398_; uint8_t v___x_3399_; uint8_t v___x_3400_; 
v___x_3375_ = l_Lean_Compiler_LCNF_postponedCompileDeclsExt;
v___x_3376_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2984_, v___x_3375_, v___x_3374_, v___y_3312_, v___x_3308_);
lean_dec(v___y_3312_);
v___x_3377_ = l_Lean_firstFrontendMacroScope;
v___x_3378_ = lean_obj_once(&l_main___closed__23, &l_main___closed__23_once, _init_l_main___closed__23);
v___x_3379_ = ((lean_object*)(l_main___closed__26));
lean_inc_n(v___y_3313_, 3);
v___x_3380_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3380_, 0, v___y_3313_);
lean_ctor_set(v___x_3380_, 1, v___x_3305_);
lean_ctor_set(v___x_3380_, 2, v___x_2977_);
v___x_3381_ = lean_obj_once(&l_main___closed__27, &l_main___closed__27_once, _init_l_main___closed__27);
v___x_3382_ = lean_obj_once(&l_main___closed__30, &l_main___closed__30_once, _init_l_main___closed__30);
v___x_3383_ = lean_obj_once(&l_main___closed__31, &l_main___closed__31_once, _init_l_main___closed__31);
v___x_3384_ = lean_obj_once(&l_main___closed__32, &l_main___closed__32_once, _init_l_main___closed__32);
v___x_3385_ = ((lean_object*)(l_main___closed__33));
lean_inc_ref(v___x_3380_);
v___x_3386_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3374_);
lean_ctor_set(v___x_3386_, 1, v___x_3378_);
lean_ctor_set(v___x_3386_, 2, v___x_3379_);
lean_ctor_set(v___x_3386_, 3, v___x_3380_);
lean_ctor_set(v___x_3386_, 4, v___x_3381_);
lean_ctor_set(v___x_3386_, 5, v___x_3382_);
lean_ctor_set(v___x_3386_, 6, v___x_3383_);
lean_ctor_set(v___x_3386_, 7, v___x_3384_);
lean_ctor_set(v___x_3386_, 8, v___x_3385_);
v___x_3387_ = lean_st_mk_ref(v___x_3386_);
v___x_3388_ = l_Lean_inheritedTraceOptions;
v___x_3389_ = lean_st_ref_get(v___x_3388_);
v___x_3390_ = lean_st_ref_get(v___x_3387_);
v___x_3391_ = l_Lean_instInhabitedFileMap_default;
v___x_3392_ = lean_unsigned_to_nat(1000u);
v___x_3393_ = lean_box(0);
v___x_3394_ = l_Lean_Core_getMaxHeartbeats(v___x_2990_);
v___x_3395_ = lean_box(0);
lean_inc_ref(v___x_2990_);
lean_inc(v_head_2949_);
v___x_3396_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3396_, 0, v_head_2949_);
lean_ctor_set(v___x_3396_, 1, v___x_3391_);
lean_ctor_set(v___x_3396_, 2, v___x_2990_);
lean_ctor_set(v___x_3396_, 3, v___x_2989_);
lean_ctor_set(v___x_3396_, 4, v___x_3392_);
lean_ctor_set(v___x_3396_, 5, v___x_3393_);
lean_ctor_set(v___x_3396_, 6, v___y_3313_);
lean_ctor_set(v___x_3396_, 7, v___x_2977_);
lean_ctor_set(v___x_3396_, 8, v___x_2989_);
lean_ctor_set(v___x_3396_, 9, v___x_3394_);
lean_ctor_set(v___x_3396_, 10, v___y_3313_);
lean_ctor_set(v___x_3396_, 11, v___x_3377_);
lean_ctor_set(v___x_3396_, 12, v___x_3395_);
lean_ctor_set(v___x_3396_, 13, v___x_3389_);
lean_ctor_set_uint8(v___x_3396_, sizeof(void*)*14, v___x_2963_);
lean_ctor_set_uint8(v___x_3396_, sizeof(void*)*14 + 1, v___x_2963_);
v_env_3397_ = lean_ctor_get(v___x_3390_, 0);
lean_inc_ref(v_env_3397_);
lean_dec(v___x_3390_);
v___x_3398_ = l_Lean_diagnostics;
v___x_3399_ = l_Lean_Option_get___at___00main_spec__8(v___x_2990_, v___x_3398_);
v___x_3400_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3397_);
lean_dec_ref(v_env_3397_);
if (v___x_3400_ == 0)
{
if (v___x_3399_ == 0)
{
v___y_3260_ = v___x_3393_;
v___y_3261_ = v___x_3324_;
v___y_3262_ = v___x_3388_;
v___y_3263_ = v___x_3391_;
v___y_3264_ = v___x_3382_;
v___y_3265_ = v___x_2977_;
v___y_3266_ = v___x_3377_;
v___y_3267_ = v___y_3310_;
v___y_3268_ = v___x_3395_;
v___y_3269_ = v___x_3381_;
v___y_3270_ = v___x_3382_;
v___y_3271_ = v___x_3376_;
v___y_3272_ = v___y_3313_;
v___y_3273_ = v___x_3387_;
v___y_3274_ = v___x_3384_;
v___y_3275_ = v___x_3379_;
v___y_3276_ = v___x_3396_;
v___y_3277_ = v___x_3375_;
v___y_3278_ = v___x_3385_;
v___y_3279_ = v___x_3383_;
v___y_3280_ = v___x_3399_;
v___y_3281_ = v___x_3380_;
v___y_3282_ = v___x_3378_;
v___y_3283_ = v___x_3324_;
goto v___jp_3259_;
}
else
{
v___y_3260_ = v___x_3393_;
v___y_3261_ = v___x_3324_;
v___y_3262_ = v___x_3388_;
v___y_3263_ = v___x_3391_;
v___y_3264_ = v___x_3382_;
v___y_3265_ = v___x_2977_;
v___y_3266_ = v___x_3377_;
v___y_3267_ = v___y_3310_;
v___y_3268_ = v___x_3395_;
v___y_3269_ = v___x_3381_;
v___y_3270_ = v___x_3382_;
v___y_3271_ = v___x_3376_;
v___y_3272_ = v___y_3313_;
v___y_3273_ = v___x_3387_;
v___y_3274_ = v___x_3384_;
v___y_3275_ = v___x_3379_;
v___y_3276_ = v___x_3396_;
v___y_3277_ = v___x_3375_;
v___y_3278_ = v___x_3385_;
v___y_3279_ = v___x_3383_;
v___y_3280_ = v___x_3399_;
v___y_3281_ = v___x_3380_;
v___y_3282_ = v___x_3378_;
v___y_3283_ = v___x_3400_;
goto v___jp_3259_;
}
}
else
{
v___y_3260_ = v___x_3393_;
v___y_3261_ = v___x_3324_;
v___y_3262_ = v___x_3388_;
v___y_3263_ = v___x_3391_;
v___y_3264_ = v___x_3382_;
v___y_3265_ = v___x_2977_;
v___y_3266_ = v___x_3377_;
v___y_3267_ = v___y_3310_;
v___y_3268_ = v___x_3395_;
v___y_3269_ = v___x_3381_;
v___y_3270_ = v___x_3382_;
v___y_3271_ = v___x_3376_;
v___y_3272_ = v___y_3313_;
v___y_3273_ = v___x_3387_;
v___y_3274_ = v___x_3384_;
v___y_3275_ = v___x_3379_;
v___y_3276_ = v___x_3396_;
v___y_3277_ = v___x_3375_;
v___y_3278_ = v___x_3385_;
v___y_3279_ = v___x_3383_;
v___y_3280_ = v___x_3399_;
v___y_3281_ = v___x_3380_;
v___y_3282_ = v___x_3378_;
v___y_3283_ = v___x_3399_;
goto v___jp_3259_;
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
v___jp_3414_:
{
lean_object* v___x_3419_; lean_object* v_toEnvExtension_3420_; lean_object* v_asyncMode_3421_; lean_object* v___x_3422_; lean_object* v_importedEntries_3423_; lean_object* v_state_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; uint8_t v___x_3427_; 
v___x_3419_ = l_Lean_IR_declMapExt;
v_toEnvExtension_3420_ = lean_ctor_get(v___x_3419_, 0);
v_asyncMode_3421_ = lean_ctor_get(v_toEnvExtension_3420_, 2);
lean_inc(v___y_3417_);
lean_inc_ref(v___y_3418_);
v___x_3422_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2981_, v_toEnvExtension_3420_, v___y_3418_, v_asyncMode_3421_, v___y_3417_);
v_importedEntries_3423_ = lean_ctor_get(v___x_3422_, 0);
lean_inc_ref(v_importedEntries_3423_);
v_state_3424_ = lean_ctor_get(v___x_3422_, 1);
lean_inc(v_state_3424_);
lean_dec(v___x_3422_);
v___x_3425_ = lean_array_get_borrowed(v___x_2982_, v_importedEntries_3423_, v___y_3416_);
v___x_3426_ = lean_array_get_size(v___x_3425_);
v___x_3427_ = lean_nat_dec_lt(v___x_2989_, v___x_3426_);
if (v___x_3427_ == 0)
{
v___y_3310_ = v___y_3415_;
v___y_3311_ = v___y_3418_;
v___y_3312_ = v___y_3416_;
v___y_3313_ = v___y_3417_;
v___y_3314_ = v_toEnvExtension_3420_;
v___y_3315_ = v_importedEntries_3423_;
v___y_3316_ = v_state_3424_;
goto v___jp_3309_;
}
else
{
uint8_t v___x_3428_; 
v___x_3428_ = lean_nat_dec_le(v___x_3426_, v___x_3426_);
if (v___x_3428_ == 0)
{
if (v___x_3427_ == 0)
{
v___y_3310_ = v___y_3415_;
v___y_3311_ = v___y_3418_;
v___y_3312_ = v___y_3416_;
v___y_3313_ = v___y_3417_;
v___y_3314_ = v_toEnvExtension_3420_;
v___y_3315_ = v_importedEntries_3423_;
v___y_3316_ = v_state_3424_;
goto v___jp_3309_;
}
else
{
size_t v___x_3429_; size_t v___x_3430_; lean_object* v___x_3431_; 
v___x_3429_ = ((size_t)0ULL);
v___x_3430_ = lean_usize_of_nat(v___x_3426_);
lean_inc_ref(v___y_3418_);
v___x_3431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3418_, v___x_3425_, v___x_3429_, v___x_3430_, v_state_3424_);
v___y_3310_ = v___y_3415_;
v___y_3311_ = v___y_3418_;
v___y_3312_ = v___y_3416_;
v___y_3313_ = v___y_3417_;
v___y_3314_ = v_toEnvExtension_3420_;
v___y_3315_ = v_importedEntries_3423_;
v___y_3316_ = v___x_3431_;
goto v___jp_3309_;
}
}
else
{
size_t v___x_3432_; size_t v___x_3433_; lean_object* v___x_3434_; 
v___x_3432_ = ((size_t)0ULL);
v___x_3433_ = lean_usize_of_nat(v___x_3426_);
lean_inc_ref(v___y_3418_);
v___x_3434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3418_, v___x_3425_, v___x_3432_, v___x_3433_, v_state_3424_);
v___y_3310_ = v___y_3415_;
v___y_3311_ = v___y_3418_;
v___y_3312_ = v___y_3416_;
v___y_3313_ = v___y_3417_;
v___y_3314_ = v_toEnvExtension_3420_;
v___y_3315_ = v_importedEntries_3423_;
v___y_3316_ = v___x_3434_;
goto v___jp_3309_;
}
}
}
v___jp_3435_:
{
uint8_t v___x_3442_; 
v___x_3442_ = lean_nat_dec_lt(v___x_2989_, v___y_3438_);
if (v___x_3442_ == 0)
{
lean_dec(v___y_3438_);
lean_dec_ref(v___y_3437_);
v___y_3415_ = v___y_3436_;
v___y_3416_ = v___y_3439_;
v___y_3417_ = v___y_3440_;
v___y_3418_ = v___y_3441_;
goto v___jp_3414_;
}
else
{
uint8_t v___x_3443_; 
v___x_3443_ = lean_nat_dec_le(v___y_3438_, v___y_3438_);
if (v___x_3443_ == 0)
{
if (v___x_3442_ == 0)
{
lean_dec(v___y_3438_);
lean_dec_ref(v___y_3437_);
v___y_3415_ = v___y_3436_;
v___y_3416_ = v___y_3439_;
v___y_3417_ = v___y_3440_;
v___y_3418_ = v___y_3441_;
goto v___jp_3414_;
}
else
{
size_t v___x_3444_; size_t v___x_3445_; lean_object* v___x_3446_; 
v___x_3444_ = ((size_t)0ULL);
v___x_3445_ = lean_usize_of_nat(v___y_3438_);
lean_dec(v___y_3438_);
v___x_3446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3437_, v___x_3444_, v___x_3445_, v___y_3441_);
lean_dec_ref(v___y_3437_);
v___y_3415_ = v___y_3436_;
v___y_3416_ = v___y_3439_;
v___y_3417_ = v___y_3440_;
v___y_3418_ = v___x_3446_;
goto v___jp_3414_;
}
}
else
{
size_t v___x_3447_; size_t v___x_3448_; lean_object* v___x_3449_; 
v___x_3447_ = ((size_t)0ULL);
v___x_3448_ = lean_usize_of_nat(v___y_3438_);
lean_dec(v___y_3438_);
v___x_3449_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3437_, v___x_3447_, v___x_3448_, v___y_3441_);
lean_dec_ref(v___y_3437_);
v___y_3415_ = v___y_3436_;
v___y_3416_ = v___y_3439_;
v___y_3417_ = v___y_3440_;
v___y_3418_ = v___x_3449_;
goto v___jp_3414_;
}
}
}
v___jp_3450_:
{
lean_object* v___x_3456_; uint8_t v___x_3457_; 
v___x_3456_ = lean_array_get_size(v___y_3455_);
v___x_3457_ = lean_nat_dec_lt(v___x_2989_, v___x_3456_);
if (v___x_3457_ == 0)
{
v___y_3436_ = v___y_3452_;
v___y_3437_ = v___y_3455_;
v___y_3438_ = v___x_3456_;
v___y_3439_ = v___y_3451_;
v___y_3440_ = v___y_3453_;
v___y_3441_ = v___y_3454_;
goto v___jp_3435_;
}
else
{
uint8_t v___x_3458_; 
v___x_3458_ = lean_nat_dec_le(v___x_3456_, v___x_3456_);
if (v___x_3458_ == 0)
{
if (v___x_3457_ == 0)
{
v___y_3436_ = v___y_3452_;
v___y_3437_ = v___y_3455_;
v___y_3438_ = v___x_3456_;
v___y_3439_ = v___y_3451_;
v___y_3440_ = v___y_3453_;
v___y_3441_ = v___y_3454_;
goto v___jp_3435_;
}
else
{
size_t v___x_3459_; size_t v___x_3460_; lean_object* v___x_3461_; 
v___x_3459_ = ((size_t)0ULL);
v___x_3460_ = lean_usize_of_nat(v___x_3456_);
v___x_3461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v___y_3455_, v___x_3459_, v___x_3460_, v___y_3454_);
v___y_3436_ = v___y_3452_;
v___y_3437_ = v___y_3455_;
v___y_3438_ = v___x_3456_;
v___y_3439_ = v___y_3451_;
v___y_3440_ = v___y_3453_;
v___y_3441_ = v___x_3461_;
goto v___jp_3435_;
}
}
else
{
size_t v___x_3462_; size_t v___x_3463_; lean_object* v___x_3464_; 
v___x_3462_ = ((size_t)0ULL);
v___x_3463_ = lean_usize_of_nat(v___x_3456_);
v___x_3464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v___y_3455_, v___x_3462_, v___x_3463_, v___y_3454_);
v___y_3436_ = v___y_3452_;
v___y_3437_ = v___y_3455_;
v___y_3438_ = v___x_3456_;
v___y_3439_ = v___y_3451_;
v___y_3440_ = v___y_3453_;
v___y_3441_ = v___x_3464_;
goto v___jp_3435_;
}
}
}
v___jp_3466_:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___f_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v___x_3468_ = l_Lean_instInhabitedImportState_default;
v___x_3469_ = lean_box(v___x_3308_);
v___x_3470_ = lean_box(v___y_3467_);
v___x_3471_ = lean_box(v___x_2986_);
v___x_3472_ = lean_box(v___x_3465_);
v___x_3473_ = lean_box(v___x_2963_);
lean_inc_ref(v___x_2990_);
lean_inc(v_name_2960_);
v___f_3474_ = lean_alloc_closure((void*)(l_main___lam__0___boxed), 11, 10);
lean_closure_set(v___f_3474_, 0, v___x_3468_);
lean_closure_set(v___f_3474_, 1, v___x_3307_);
lean_closure_set(v___f_3474_, 2, v___x_3469_);
lean_closure_set(v___f_3474_, 3, v_importArts_2961_);
lean_closure_set(v___f_3474_, 4, v___x_3470_);
lean_closure_set(v___f_3474_, 5, v___x_3471_);
lean_closure_set(v___f_3474_, 6, v_name_2960_);
lean_closure_set(v___f_3474_, 7, v___x_3472_);
lean_closure_set(v___f_3474_, 8, v___x_2990_);
lean_closure_set(v___f_3474_, 9, v___x_3473_);
v___x_3475_ = lean_alloc_closure((void*)(l_Lean_withImporting___boxed), 3, 2);
lean_closure_set(v___x_3475_, 0, lean_box(0));
lean_closure_set(v___x_3475_, 1, v___f_3474_);
v___x_3476_ = lean_box(0);
v___x_3477_ = l_Lean_profileitIOUnsafe___redArg(v___x_3303_, v___x_2990_, v___x_3475_, v___x_3476_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v_a_3478_; lean_object* v___x_3479_; lean_object* v_ext_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; 
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_a_3478_);
lean_dec_ref_known(v___x_3477_, 1);
v___x_3479_ = l_Lean_Compiler_CSimp_ext;
v_ext_3480_ = lean_ctor_get(v___x_3479_, 1);
lean_inc(v_name_2960_);
v___x_3481_ = l_Lean_Environment_setMainModule(v_a_3478_, v_name_2960_);
lean_inc_ref(v_ext_3480_);
v___x_3482_ = l_main___elam__0___redArg(v___x_3476_, v___x_2976_, v_ext_3480_, v___x_3481_);
if (lean_obj_tag(v___x_3482_) == 0)
{
lean_object* v_a_3483_; lean_object* v___x_3484_; lean_object* v_ext_3485_; lean_object* v___x_3486_; 
v_a_3483_ = lean_ctor_get(v___x_3482_, 0);
lean_inc(v_a_3483_);
lean_dec_ref_known(v___x_3482_, 1);
v___x_3484_ = l_Lean_Meta_instanceExtension;
v_ext_3485_ = lean_ctor_get(v___x_3484_, 1);
lean_inc_ref(v_ext_3485_);
v___x_3486_ = l_main___elam__0___redArg(v___x_3476_, v___x_2976_, v_ext_3485_, v_a_3483_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v_a_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; 
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
lean_inc(v_a_3487_);
lean_dec_ref_known(v___x_3486_, 1);
v___x_3488_ = l_Lean_classExtension;
v___x_3489_ = l_main___elam__0___redArg(v___x_3476_, v___x_2978_, v___x_3488_, v_a_3487_);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v_a_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; 
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
lean_inc(v_a_3490_);
lean_dec_ref_known(v___x_3489_, 1);
v___x_3491_ = l_Lean_Meta_Match_Extension_extension;
v___x_3492_ = l_main___elam__0___redArg(v___x_3476_, v___x_2979_, v___x_3491_, v_a_3490_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3520_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3495_ = v___x_3492_;
v_isShared_3496_ = v_isSharedCheck_3520_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3492_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3520_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3497_; 
v___x_3497_ = l_Lean_Environment_getModuleIdx_x3f(v_a_3493_, v_name_2960_);
if (lean_obj_tag(v___x_3497_) == 1)
{
lean_object* v_val_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; uint8_t v___x_3503_; 
lean_del_object(v___x_3495_);
v_val_3498_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_val_3498_);
lean_dec_ref_known(v___x_3497_, 1);
v___x_3499_ = l_Lean_Compiler_LCNF_impureSigExt;
v___x_3500_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2980_, v___x_3499_, v_a_3493_, v_val_3498_, v___x_3308_);
v___x_3501_ = lean_array_get_size(v___x_3500_);
v___x_3502_ = ((lean_object*)(l_main___closed__34));
v___x_3503_ = lean_nat_dec_lt(v___x_2989_, v___x_3501_);
if (v___x_3503_ == 0)
{
lean_dec_ref(v___x_3500_);
v___y_3451_ = v_val_3498_;
v___y_3452_ = v___x_3476_;
v___y_3453_ = v___x_3476_;
v___y_3454_ = v_a_3493_;
v___y_3455_ = v___x_3502_;
goto v___jp_3450_;
}
else
{
uint8_t v___x_3504_; 
v___x_3504_ = lean_nat_dec_le(v___x_3501_, v___x_3501_);
if (v___x_3504_ == 0)
{
if (v___x_3503_ == 0)
{
lean_dec_ref(v___x_3500_);
v___y_3451_ = v_val_3498_;
v___y_3452_ = v___x_3476_;
v___y_3453_ = v___x_3476_;
v___y_3454_ = v_a_3493_;
v___y_3455_ = v___x_3502_;
goto v___jp_3450_;
}
else
{
size_t v___x_3505_; size_t v___x_3506_; lean_object* v___x_3507_; 
v___x_3505_ = ((size_t)0ULL);
v___x_3506_ = lean_usize_of_nat(v___x_3501_);
lean_inc(v_a_3493_);
v___x_3507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_3493_, v___x_3500_, v___x_3505_, v___x_3506_, v___x_3502_);
lean_dec_ref(v___x_3500_);
v___y_3451_ = v_val_3498_;
v___y_3452_ = v___x_3476_;
v___y_3453_ = v___x_3476_;
v___y_3454_ = v_a_3493_;
v___y_3455_ = v___x_3507_;
goto v___jp_3450_;
}
}
else
{
size_t v___x_3508_; size_t v___x_3509_; lean_object* v___x_3510_; 
v___x_3508_ = ((size_t)0ULL);
v___x_3509_ = lean_usize_of_nat(v___x_3501_);
lean_inc(v_a_3493_);
v___x_3510_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_3493_, v___x_3500_, v___x_3508_, v___x_3509_, v___x_3502_);
lean_dec_ref(v___x_3500_);
v___y_3451_ = v_val_3498_;
v___y_3452_ = v___x_3476_;
v___y_3453_ = v___x_3476_;
v___y_3454_ = v_a_3493_;
v___y_3455_ = v___x_3510_;
goto v___jp_3450_;
}
}
}
else
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3518_; 
lean_dec(v___x_3497_);
lean_dec(v_a_3493_);
lean_dec_ref(v___x_2990_);
lean_del_object(v___x_2974_);
lean_dec(v_fst_2971_);
lean_dec(v_head_2953_);
lean_del_object(v___x_2951_);
lean_dec(v_head_2949_);
lean_del_object(v___x_2947_);
v___x_3511_ = ((lean_object*)(l_main___closed__35));
v___x_3512_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2960_, v___x_2986_);
v___x_3513_ = lean_string_append(v___x_3511_, v___x_3512_);
lean_dec_ref(v___x_3512_);
v___x_3514_ = ((lean_object*)(l_main___closed__36));
v___x_3515_ = lean_string_append(v___x_3513_, v___x_3514_);
v___x_3516_ = lean_mk_io_user_error(v___x_3515_);
if (v_isShared_3496_ == 0)
{
lean_ctor_set_tag(v___x_3495_, 1);
lean_ctor_set(v___x_3495_, 0, v___x_3516_);
v___x_3518_ = v___x_3495_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v___x_3516_);
v___x_3518_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
return v___x_3518_;
}
}
}
}
else
{
lean_object* v_a_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3528_; 
lean_dec_ref(v___x_2990_);
lean_del_object(v___x_2974_);
lean_dec(v_fst_2971_);
lean_dec(v_name_2960_);
lean_dec(v_head_2953_);
lean_del_object(v___x_2951_);
lean_dec(v_head_2949_);
lean_del_object(v___x_2947_);
v_a_3521_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3523_ = v___x_3492_;
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_a_3521_);
lean_dec(v___x_3492_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3526_; 
if (v_isShared_3524_ == 0)
{
v___x_3526_ = v___x_3523_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_a_3521_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
}
}
else
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3536_; 
lean_dec_ref(v___x_2990_);
lean_del_object(v___x_2974_);
lean_dec(v_fst_2971_);
lean_dec(v_name_2960_);
lean_dec(v_head_2953_);
lean_del_object(v___x_2951_);
lean_dec(v_head_2949_);
lean_del_object(v___x_2947_);
v_a_3529_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3531_ = v___x_3489_;
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3489_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3534_; 
if (v_isShared_3532_ == 0)
{
v___x_3534_ = v___x_3531_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_a_3529_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
}
}
else
{
lean_object* v_a_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3544_; 
lean_dec_ref(v___x_2990_);
lean_del_object(v___x_2974_);
lean_dec(v_fst_2971_);
lean_dec(v_name_2960_);
lean_dec(v_head_2953_);
lean_del_object(v___x_2951_);
lean_dec(v_head_2949_);
lean_del_object(v___x_2947_);
v_a_3537_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3544_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3539_ = v___x_3486_;
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_a_3537_);
lean_dec(v___x_3486_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3542_; 
if (v_isShared_3540_ == 0)
{
v___x_3542_ = v___x_3539_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_a_3537_);
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
else
{
lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3552_; 
lean_dec_ref(v___x_2990_);
lean_del_object(v___x_2974_);
lean_dec(v_fst_2971_);
lean_dec(v_name_2960_);
lean_dec(v_head_2953_);
lean_del_object(v___x_2951_);
lean_dec(v_head_2949_);
lean_del_object(v___x_2947_);
v_a_3545_ = lean_ctor_get(v___x_3482_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3482_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3547_ = v___x_3482_;
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_dec(v___x_3482_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3550_; 
if (v_isShared_3548_ == 0)
{
v___x_3550_ = v___x_3547_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_a_3545_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
}
}
}
}
else
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3560_; 
lean_dec_ref(v___x_2990_);
lean_del_object(v___x_2974_);
lean_dec(v_fst_2971_);
lean_dec(v_name_2960_);
lean_dec(v_head_2953_);
lean_del_object(v___x_2951_);
lean_dec(v_head_2949_);
lean_del_object(v___x_2947_);
v_a_3553_ = lean_ctor_get(v___x_3477_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3555_ = v___x_3477_;
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___x_3477_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3558_; 
if (v_isShared_3556_ == 0)
{
v___x_3558_ = v___x_3555_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3553_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
}
}
}
else
{
lean_object* v_a_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3570_; 
lean_dec(v_a_2969_);
lean_dec(v_importArts_2961_);
lean_dec(v_name_2960_);
lean_dec(v_head_2953_);
lean_del_object(v___x_2951_);
lean_dec(v_head_2949_);
lean_del_object(v___x_2947_);
v_a_3563_ = lean_ctor_get(v___x_2970_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3565_ = v___x_2970_;
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_a_3563_);
lean_dec(v___x_2970_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3568_; 
if (v_isShared_3566_ == 0)
{
v___x_3568_ = v___x_3565_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3563_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
}
else
{
lean_object* v_a_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3578_; 
lean_dec(v_importArts_2961_);
lean_dec(v_name_2960_);
lean_dec(v_head_2953_);
lean_del_object(v___x_2951_);
lean_dec(v_head_2949_);
lean_del_object(v___x_2947_);
v_a_3571_ = lean_ctor_get(v___x_2968_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3573_ = v___x_2968_;
v_isShared_3574_ = v_isSharedCheck_3578_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_a_3571_);
lean_dec(v___x_2968_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3578_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3576_; 
if (v_isShared_3574_ == 0)
{
v___x_3576_ = v___x_3573_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_a_3571_);
v___x_3576_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
return v___x_3576_;
}
}
}
}
}
else
{
lean_object* v_a_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3587_; 
lean_del_object(v___x_2956_);
lean_dec(v_tail_2954_);
lean_dec(v_head_2953_);
lean_del_object(v___x_2951_);
lean_dec(v_head_2949_);
lean_del_object(v___x_2947_);
v_a_3580_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3582_ = v___x_2958_;
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_a_3580_);
lean_dec(v___x_2958_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___x_3585_; 
if (v_isShared_3583_ == 0)
{
v___x_3585_ = v___x_3582_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_a_3580_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
}
}
}
}
else
{
lean_dec(v_tail_2944_);
lean_dec_ref_known(v_tail_2943_, 2);
lean_dec_ref_known(v_args_2918_, 2);
goto v___jp_2920_;
}
}
else
{
lean_dec_ref_known(v_args_2918_, 2);
lean_dec(v_tail_2943_);
goto v___jp_2920_;
}
}
else
{
lean_dec(v_args_2918_);
goto v___jp_2920_;
}
v___jp_2920_:
{
lean_object* v___x_2921_; lean_object* v___x_2922_; 
v___x_2921_ = ((lean_object*)(l_main___closed__0));
v___x_2922_ = l_IO_println___at___00Lean_Environment_displayStats_spec__1(v___x_2921_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2930_; 
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2930_ == 0)
{
lean_object* v_unused_2931_; 
v_unused_2931_ = lean_ctor_get(v___x_2922_, 0);
lean_dec(v_unused_2931_);
v___x_2924_ = v___x_2922_;
v_isShared_2925_ = v_isSharedCheck_2930_;
goto v_resetjp_2923_;
}
else
{
lean_dec(v___x_2922_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2930_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2926_; lean_object* v___x_2928_; 
v___x_2926_ = l_main___boxed__const__1;
if (v_isShared_2925_ == 0)
{
lean_ctor_set(v___x_2924_, 0, v___x_2926_);
v___x_2928_ = v___x_2924_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v___x_2926_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
else
{
lean_object* v_a_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2939_; 
v_a_2932_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_2939_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2934_ = v___x_2922_;
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_a_2932_);
lean_dec(v___x_2922_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2937_; 
if (v_isShared_2935_ == 0)
{
v___x_2937_ = v___x_2934_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_a_2932_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
}
}
v___jp_2940_:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2941_ = l_main___boxed__const__2;
v___x_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
return v___x_2942_;
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_3593_, lean_object* v_a_3594_){
_start:
{
lean_object* v_res_3595_; 
v_res_3595_ = _lean_main(v_args_3593_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1(lean_object* v_as_3596_, lean_object* v_as_x27_3597_, lean_object* v_b_3598_, lean_object* v_a_3599_){
_start:
{
lean_object* v___x_3601_; 
v___x_3601_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_3597_, v_b_3598_);
return v___x_3601_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___boxed(lean_object* v_as_3602_, lean_object* v_as_x27_3603_, lean_object* v_b_3604_, lean_object* v_a_3605_, lean_object* v___y_3606_){
_start:
{
lean_object* v_res_3607_; 
v_res_3607_ = l_List_forIn_x27_loop___at___00main_spec__1(v_as_3602_, v_as_x27_3603_, v_b_3604_, v_a_3605_);
lean_dec(v_as_x27_3603_);
lean_dec(v_as_3602_);
return v_res_3607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16(lean_object* v___y_3608_, lean_object* v___y_3609_){
_start:
{
lean_object* v___x_3611_; 
v___x_3611_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_3609_);
return v___x_3611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___boxed(lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_){
_start:
{
lean_object* v_res_3615_; 
v_res_3615_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16(v___y_3612_, v___y_3613_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
return v_res_3615_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17(lean_object* v_00_u03b2_3616_, lean_object* v_m_3617_, lean_object* v_a_3618_, lean_object* v_fallback_3619_){
_start:
{
lean_object* v___x_3620_; 
v___x_3620_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_m_3617_, v_a_3618_, v_fallback_3619_);
return v___x_3620_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___boxed(lean_object* v_00_u03b2_3621_, lean_object* v_m_3622_, lean_object* v_a_3623_, lean_object* v_fallback_3624_){
_start:
{
lean_object* v_res_3625_; 
v_res_3625_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17(v_00_u03b2_3621_, v_m_3622_, v_a_3623_, v_fallback_3624_);
lean_dec(v_fallback_3624_);
lean_dec_ref(v_a_3623_);
lean_dec_ref(v_m_3622_);
return v_res_3625_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18(lean_object* v_00_u03b2_3626_, lean_object* v_m_3627_, lean_object* v_a_3628_, lean_object* v_b_3629_){
_start:
{
lean_object* v___x_3630_; 
v___x_3630_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_m_3627_, v_a_3628_, v_b_3629_);
return v___x_3630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21(lean_object* v_n_3631_, lean_object* v_as_3632_, lean_object* v_lo_3633_, lean_object* v_hi_3634_, lean_object* v_w_3635_, lean_object* v_hlo_3636_, lean_object* v_hhi_3637_){
_start:
{
lean_object* v___x_3638_; 
v___x_3638_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_3631_, v_as_3632_, v_lo_3633_, v_hi_3634_);
return v___x_3638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___boxed(lean_object* v_n_3639_, lean_object* v_as_3640_, lean_object* v_lo_3641_, lean_object* v_hi_3642_, lean_object* v_w_3643_, lean_object* v_hlo_3644_, lean_object* v_hhi_3645_){
_start:
{
lean_object* v_res_3646_; 
v_res_3646_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21(v_n_3639_, v_as_3640_, v_lo_3641_, v_hi_3642_, v_w_3643_, v_hlo_3644_, v_hhi_3645_);
lean_dec(v_hi_3642_);
lean_dec(v_n_3639_);
return v_res_3646_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21(lean_object* v_00_u03b2_3647_, lean_object* v_a_3648_, lean_object* v_fallback_3649_, lean_object* v_x_3650_){
_start:
{
lean_object* v___x_3651_; 
v___x_3651_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_3648_, v_fallback_3649_, v_x_3650_);
return v___x_3651_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___boxed(lean_object* v_00_u03b2_3652_, lean_object* v_a_3653_, lean_object* v_fallback_3654_, lean_object* v_x_3655_){
_start:
{
lean_object* v_res_3656_; 
v_res_3656_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21(v_00_u03b2_3652_, v_a_3653_, v_fallback_3654_, v_x_3655_);
lean_dec(v_x_3655_);
lean_dec(v_fallback_3654_);
lean_dec_ref(v_a_3653_);
return v_res_3656_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23(lean_object* v_00_u03b2_3657_, lean_object* v_a_3658_, lean_object* v_x_3659_){
_start:
{
uint8_t v___x_3660_; 
v___x_3660_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_3658_, v_x_3659_);
return v___x_3660_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___boxed(lean_object* v_00_u03b2_3661_, lean_object* v_a_3662_, lean_object* v_x_3663_){
_start:
{
uint8_t v_res_3664_; lean_object* v_r_3665_; 
v_res_3664_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23(v_00_u03b2_3661_, v_a_3662_, v_x_3663_);
lean_dec(v_x_3663_);
lean_dec_ref(v_a_3662_);
v_r_3665_ = lean_box(v_res_3664_);
return v_r_3665_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24(lean_object* v_00_u03b2_3666_, lean_object* v_data_3667_){
_start:
{
lean_object* v___x_3668_; 
v___x_3668_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(v_data_3667_);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25(lean_object* v_00_u03b2_3669_, lean_object* v_a_3670_, lean_object* v_b_3671_, lean_object* v_x_3672_){
_start:
{
lean_object* v___x_3673_; 
v___x_3673_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_3670_, v_b_3671_, v_x_3672_);
return v___x_3673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31(lean_object* v_n_3674_, lean_object* v_lo_3675_, lean_object* v_hi_3676_, lean_object* v_hhi_3677_, lean_object* v_pivot_3678_, lean_object* v_as_3679_, lean_object* v_i_3680_, lean_object* v_k_3681_, lean_object* v_ilo_3682_, lean_object* v_ik_3683_, lean_object* v_w_3684_){
_start:
{
lean_object* v___x_3685_; 
v___x_3685_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_3676_, v_pivot_3678_, v_as_3679_, v_i_3680_, v_k_3681_);
return v___x_3685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___boxed(lean_object* v_n_3686_, lean_object* v_lo_3687_, lean_object* v_hi_3688_, lean_object* v_hhi_3689_, lean_object* v_pivot_3690_, lean_object* v_as_3691_, lean_object* v_i_3692_, lean_object* v_k_3693_, lean_object* v_ilo_3694_, lean_object* v_ik_3695_, lean_object* v_w_3696_){
_start:
{
lean_object* v_res_3697_; 
v_res_3697_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31(v_n_3686_, v_lo_3687_, v_hi_3688_, v_hhi_3689_, v_pivot_3690_, v_as_3691_, v_i_3692_, v_k_3693_, v_ilo_3694_, v_ik_3695_, v_w_3696_);
lean_dec_ref(v_pivot_3690_);
lean_dec(v_hi_3688_);
lean_dec(v_lo_3687_);
lean_dec(v_n_3686_);
return v_res_3697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40(lean_object* v_as_3698_, size_t v_sz_3699_, size_t v_i_3700_, lean_object* v_b_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_){
_start:
{
lean_object* v___x_3705_; 
v___x_3705_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_3698_, v_sz_3699_, v_i_3700_, v_b_3701_, v___y_3702_);
return v___x_3705_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___boxed(lean_object* v_as_3706_, lean_object* v_sz_3707_, lean_object* v_i_3708_, lean_object* v_b_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_){
_start:
{
size_t v_sz_boxed_3713_; size_t v_i_boxed_3714_; lean_object* v_res_3715_; 
v_sz_boxed_3713_ = lean_unbox_usize(v_sz_3707_);
lean_dec(v_sz_3707_);
v_i_boxed_3714_ = lean_unbox_usize(v_i_3708_);
lean_dec(v_i_3708_);
v_res_3715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40(v_as_3706_, v_sz_boxed_3713_, v_i_boxed_3714_, v_b_3709_, v___y_3710_, v___y_3711_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec_ref(v_as_3706_);
return v_res_3715_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35(lean_object* v_00_u03b2_3716_, lean_object* v_i_3717_, lean_object* v_source_3718_, lean_object* v_target_3719_){
_start:
{
lean_object* v___x_3720_; 
v___x_3720_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(v_i_3717_, v_source_3718_, v_target_3719_);
return v___x_3720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42(uint8_t v___x_3721_, lean_object* v_as_3722_, size_t v_sz_3723_, size_t v_i_3724_, lean_object* v_b_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_){
_start:
{
lean_object* v___x_3729_; 
v___x_3729_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_3721_, v_as_3722_, v_sz_3723_, v_i_3724_, v_b_3725_, v___y_3726_);
return v___x_3729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___boxed(lean_object* v___x_3730_, lean_object* v_as_3731_, lean_object* v_sz_3732_, lean_object* v_i_3733_, lean_object* v_b_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_){
_start:
{
uint8_t v___x_40696__boxed_3738_; size_t v_sz_boxed_3739_; size_t v_i_boxed_3740_; lean_object* v_res_3741_; 
v___x_40696__boxed_3738_ = lean_unbox(v___x_3730_);
v_sz_boxed_3739_ = lean_unbox_usize(v_sz_3732_);
lean_dec(v_sz_3732_);
v_i_boxed_3740_ = lean_unbox_usize(v_i_3733_);
lean_dec(v_i_3733_);
v_res_3741_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42(v___x_40696__boxed_3738_, v_as_3731_, v_sz_boxed_3739_, v_i_boxed_3740_, v_b_3734_, v___y_3735_, v___y_3736_);
lean_dec(v___y_3736_);
lean_dec_ref(v___y_3735_);
lean_dec_ref(v_as_3731_);
return v_res_3741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51(lean_object* v_as_3742_, size_t v_sz_3743_, size_t v_i_3744_, lean_object* v_b_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_){
_start:
{
lean_object* v___x_3749_; 
v___x_3749_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_3742_, v_sz_3743_, v_i_3744_, v_b_3745_, v___y_3746_);
return v___x_3749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___boxed(lean_object* v_as_3750_, lean_object* v_sz_3751_, lean_object* v_i_3752_, lean_object* v_b_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_){
_start:
{
size_t v_sz_boxed_3757_; size_t v_i_boxed_3758_; lean_object* v_res_3759_; 
v_sz_boxed_3757_ = lean_unbox_usize(v_sz_3751_);
lean_dec(v_sz_3751_);
v_i_boxed_3758_ = lean_unbox_usize(v_i_3752_);
lean_dec(v_i_3752_);
v_res_3759_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51(v_as_3750_, v_sz_boxed_3757_, v_i_boxed_3758_, v_b_3753_, v___y_3754_, v___y_3755_);
lean_dec(v___y_3755_);
lean_dec_ref(v___y_3754_);
lean_dec_ref(v_as_3750_);
return v_res_3759_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44(lean_object* v_00_u03b2_3760_, lean_object* v_x_3761_, lean_object* v_x_3762_){
_start:
{
lean_object* v___x_3763_; 
v___x_3763_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(v_x_3761_, v_x_3762_);
return v___x_3763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49(uint8_t v___x_3764_, lean_object* v_as_3765_, size_t v_sz_3766_, size_t v_i_3767_, lean_object* v_b_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_){
_start:
{
lean_object* v___x_3772_; 
v___x_3772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_3764_, v_as_3765_, v_sz_3766_, v_i_3767_, v_b_3768_, v___y_3769_);
return v___x_3772_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___boxed(lean_object* v___x_3773_, lean_object* v_as_3774_, lean_object* v_sz_3775_, lean_object* v_i_3776_, lean_object* v_b_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_){
_start:
{
uint8_t v___x_40727__boxed_3781_; size_t v_sz_boxed_3782_; size_t v_i_boxed_3783_; lean_object* v_res_3784_; 
v___x_40727__boxed_3781_ = lean_unbox(v___x_3773_);
v_sz_boxed_3782_ = lean_unbox_usize(v_sz_3775_);
lean_dec(v_sz_3775_);
v_i_boxed_3783_ = lean_unbox_usize(v_i_3776_);
lean_dec(v_i_3776_);
v_res_3784_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49(v___x_40727__boxed_3781_, v_as_3774_, v_sz_boxed_3782_, v_i_boxed_3783_, v_b_3777_, v___y_3778_, v___y_3779_);
lean_dec(v___y_3779_);
lean_dec_ref(v___y_3778_);
lean_dec_ref(v_as_3774_);
return v_res_3784_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_LeanIR(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
void lean_initialize();
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
  lean_initialize();
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
