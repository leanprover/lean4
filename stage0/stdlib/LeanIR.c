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
uint8_t lean_bool_not(uint8_t);
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
LEAN_EXPORT lean_object* l_main___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t);
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
lean_object* v___x_74_; lean_object* v_fst_75_; uint8_t v___x_76_; uint8_t v___x_77_; 
v___x_74_ = lean_array_uget_borrowed(v_as_64_, v_i_65_);
v_fst_75_ = lean_ctor_get(v___x_74_, 0);
v___x_76_ = l_Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1(v_irExtNames_63_, v_fst_75_);
v___x_77_ = lean_bool_not(v___x_76_);
if (v___x_77_ == 0)
{
v___y_69_ = v_b_67_;
goto v___jp_68_;
}
else
{
lean_object* v___x_78_; 
lean_inc(v___x_74_);
v___x_78_ = lean_array_push(v_b_67_, v___x_74_);
v___y_69_ = v___x_78_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2___boxed(lean_object* v_irExtNames_79_, lean_object* v_as_80_, lean_object* v_i_81_, lean_object* v_stop_82_, lean_object* v_b_83_){
_start:
{
size_t v_i_boxed_84_; size_t v_stop_boxed_85_; lean_object* v_res_86_; 
v_i_boxed_84_ = lean_unbox_usize(v_i_81_);
lean_dec(v_i_81_);
v_stop_boxed_85_ = lean_unbox_usize(v_stop_82_);
lean_dec(v_stop_82_);
v_res_86_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2(v_irExtNames_79_, v_as_80_, v_i_boxed_84_, v_stop_boxed_85_, v_b_83_);
lean_dec_ref(v_as_80_);
lean_dec_ref(v_irExtNames_79_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0(size_t v_sz_87_, size_t v_i_88_, lean_object* v_bs_89_){
_start:
{
uint8_t v___x_90_; 
v___x_90_ = lean_usize_dec_lt(v_i_88_, v_sz_87_);
if (v___x_90_ == 0)
{
return v_bs_89_;
}
else
{
lean_object* v_v_91_; lean_object* v_fst_92_; lean_object* v___x_93_; lean_object* v_bs_x27_94_; size_t v___x_95_; size_t v___x_96_; lean_object* v___x_97_; 
v_v_91_ = lean_array_uget_borrowed(v_bs_89_, v_i_88_);
v_fst_92_ = lean_ctor_get(v_v_91_, 0);
lean_inc(v_fst_92_);
v___x_93_ = lean_unsigned_to_nat(0u);
v_bs_x27_94_ = lean_array_uset(v_bs_89_, v_i_88_, v___x_93_);
v___x_95_ = ((size_t)1ULL);
v___x_96_ = lean_usize_add(v_i_88_, v___x_95_);
v___x_97_ = lean_array_uset(v_bs_x27_94_, v_i_88_, v_fst_92_);
v_i_88_ = v___x_96_;
v_bs_89_ = v___x_97_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0___boxed(lean_object* v_sz_99_, lean_object* v_i_100_, lean_object* v_bs_101_){
_start:
{
size_t v_sz_boxed_102_; size_t v_i_boxed_103_; lean_object* v_res_104_; 
v_sz_boxed_102_ = lean_unbox_usize(v_sz_99_);
lean_dec(v_sz_99_);
v_i_boxed_103_ = lean_unbox_usize(v_i_100_);
lean_dec(v_i_100_);
v_res_104_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0(v_sz_boxed_102_, v_i_boxed_103_, v_bs_101_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__mkIRData(lean_object* v_env_109_){
_start:
{
lean_object* v_irEntries_111_; uint8_t v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
lean_inc_ref_n(v_env_109_, 2);
v_irEntries_111_ = lean_ir_export_entries(v_env_109_);
v___x_112_ = 2;
v___x_113_ = lean_box(0);
v___x_114_ = l_Lean_mkModuleData(v_env_109_, v___x_112_, v___x_113_);
if (lean_obj_tag(v___x_114_) == 0)
{
lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_145_; 
v_a_115_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_145_ == 0)
{
v___x_117_ = v___x_114_;
v_isShared_118_ = v_isSharedCheck_145_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_114_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_145_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___y_120_; lean_object* v_entries_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v_entries_132_ = lean_ctor_get(v_a_115_, 4);
lean_inc_ref(v_entries_132_);
lean_dec(v_a_115_);
v___x_133_ = lean_unsigned_to_nat(0u);
v___x_134_ = lean_array_get_size(v_entries_132_);
v___x_135_ = ((lean_object*)(l___private_LeanIR_0__mkIRData___closed__1));
v___x_136_ = lean_nat_dec_lt(v___x_133_, v___x_134_);
if (v___x_136_ == 0)
{
lean_dec_ref(v_entries_132_);
v___y_120_ = v___x_135_;
goto v___jp_119_;
}
else
{
size_t v_sz_137_; size_t v___x_138_; lean_object* v_irExtNames_139_; uint8_t v___x_140_; 
v_sz_137_ = lean_array_size(v_irEntries_111_);
v___x_138_ = ((size_t)0ULL);
lean_inc_ref(v_irEntries_111_);
v_irExtNames_139_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0(v_sz_137_, v___x_138_, v_irEntries_111_);
v___x_140_ = lean_nat_dec_le(v___x_134_, v___x_134_);
if (v___x_140_ == 0)
{
if (v___x_136_ == 0)
{
lean_dec_ref(v_irExtNames_139_);
lean_dec_ref(v_entries_132_);
v___y_120_ = v___x_135_;
goto v___jp_119_;
}
else
{
size_t v___x_141_; lean_object* v___x_142_; 
v___x_141_ = lean_usize_of_nat(v___x_134_);
v___x_142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2(v_irExtNames_139_, v_entries_132_, v___x_138_, v___x_141_, v___x_135_);
lean_dec_ref(v_entries_132_);
lean_dec_ref(v_irExtNames_139_);
v___y_120_ = v___x_142_;
goto v___jp_119_;
}
}
else
{
size_t v___x_143_; lean_object* v___x_144_; 
v___x_143_ = lean_usize_of_nat(v___x_134_);
v___x_144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2(v_irExtNames_139_, v_entries_132_, v___x_138_, v___x_143_, v___x_135_);
lean_dec_ref(v_entries_132_);
lean_dec_ref(v_irExtNames_139_);
v___y_120_ = v___x_144_;
goto v___jp_119_;
}
}
v___jp_119_:
{
lean_object* v___x_121_; uint8_t v_isModule_122_; lean_object* v_imports_123_; lean_object* v___x_124_; uint8_t v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_130_; 
v___x_121_ = l_Lean_Environment_header(v_env_109_);
v_isModule_122_ = lean_ctor_get_uint8(v___x_121_, sizeof(void*)*7 + 4);
v_imports_123_ = lean_ctor_get(v___x_121_, 1);
lean_inc_ref(v_imports_123_);
lean_dec_ref(v___x_121_);
v___x_124_ = ((lean_object*)(l___private_LeanIR_0__mkIRData___closed__0));
v___x_125_ = 1;
v___x_126_ = lean_get_ir_extra_const_names(v_env_109_, v___x_112_, v___x_125_);
v___x_127_ = l_Array_append___redArg(v_irEntries_111_, v___y_120_);
lean_dec_ref(v___y_120_);
v___x_128_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_128_, 0, v_imports_123_);
lean_ctor_set(v___x_128_, 1, v___x_124_);
lean_ctor_set(v___x_128_, 2, v___x_124_);
lean_ctor_set(v___x_128_, 3, v___x_126_);
lean_ctor_set(v___x_128_, 4, v___x_127_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*5, v_isModule_122_);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 0, v___x_128_);
v___x_130_ = v___x_117_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_128_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
else
{
lean_dec_ref(v_irEntries_111_);
lean_dec_ref(v_env_109_);
return v___x_114_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__mkIRData___boxed(lean_object* v_env_146_, lean_object* v_a_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l___private_LeanIR_0__mkIRData(v_env_146_);
return v_res_148_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__0));
v___x_151_ = lean_string_utf8_byte_size(v___x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(lean_object* v_s_152_){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_153_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__0));
v___x_154_ = lean_string_utf8_byte_size(v_s_152_);
v___x_155_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__1, &l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__1);
v___x_156_ = lean_nat_dec_le(v___x_155_, v___x_154_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; 
lean_dec_ref(v_s_152_);
v___x_157_ = lean_box(0);
return v___x_157_;
}
else
{
lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_158_ = lean_unsigned_to_nat(0u);
v___x_159_ = lean_string_memcmp(v_s_152_, v___x_153_, v___x_158_, v___x_158_, v___x_155_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; 
lean_dec_ref(v_s_152_);
v___x_160_ = lean_box(0);
return v___x_160_;
}
else
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
lean_inc_ref(v_s_152_);
v___x_161_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_161_, 0, v_s_152_);
lean_ctor_set(v___x_161_, 1, v___x_158_);
lean_ctor_set(v___x_161_, 2, v___x_154_);
v___x_162_ = l_String_Slice_pos_x21(v___x_161_, v___x_155_);
lean_dec_ref_known(v___x_161_, 3);
v___x_163_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_163_, 0, v_s_152_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
lean_ctor_set(v___x_163_, 2, v___x_154_);
v___x_164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
return v___x_164_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0(lean_object* v_s_165_, lean_object* v_pat_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(v_s_165_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___boxed(lean_object* v_s_168_, lean_object* v_pat_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0(v_s_168_, v_pat_169_);
lean_dec_ref(v_pat_169_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg(lean_object* v_val_171_, lean_object* v_a_172_, lean_object* v_b_173_){
_start:
{
lean_object* v_str_174_; lean_object* v_startInclusive_175_; lean_object* v_endExclusive_176_; lean_object* v___x_177_; uint8_t v___x_178_; 
v_str_174_ = lean_ctor_get(v_val_171_, 0);
v_startInclusive_175_ = lean_ctor_get(v_val_171_, 1);
v_endExclusive_176_ = lean_ctor_get(v_val_171_, 2);
v___x_177_ = lean_nat_sub(v_endExclusive_176_, v_startInclusive_175_);
v___x_178_ = lean_nat_dec_eq(v_a_172_, v___x_177_);
lean_dec(v___x_177_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; uint32_t v___x_180_; uint32_t v___x_181_; uint8_t v___x_182_; 
v___x_179_ = lean_nat_add(v_startInclusive_175_, v_a_172_);
v___x_180_ = lean_string_utf8_get_fast(v_str_174_, v___x_179_);
v___x_181_ = 61;
v___x_182_ = lean_uint32_dec_eq(v___x_180_, v___x_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
lean_dec(v_a_172_);
v___x_183_ = lean_box(0);
v___x_184_ = lean_string_utf8_next_fast(v_str_174_, v___x_179_);
lean_dec(v___x_179_);
v___x_185_ = lean_nat_sub(v___x_184_, v_startInclusive_175_);
v_a_172_ = v___x_185_;
v_b_173_ = v___x_183_;
goto _start;
}
else
{
lean_object* v___x_187_; 
lean_dec(v___x_179_);
v___x_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_187_, 0, v_a_172_);
return v___x_187_;
}
}
else
{
lean_dec(v_a_172_);
lean_inc(v_b_173_);
return v_b_173_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg___boxed(lean_object* v_val_188_, lean_object* v_a_189_, lean_object* v_b_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg(v_val_188_, v_a_189_, v_b_190_);
lean_dec(v_b_190_);
lean_dec_ref(v_val_188_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__setConfigOption(lean_object* v_opts_199_, lean_object* v_arg_200_){
_start:
{
lean_object* v___x_202_; 
lean_inc_ref(v_arg_200_);
v___x_202_ = l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(v_arg_200_);
if (lean_obj_tag(v___x_202_) == 1)
{
lean_object* v_val_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_267_; 
lean_dec_ref(v_arg_200_);
v_val_203_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_267_ == 0)
{
v___x_205_ = v___x_202_;
v_isShared_206_ = v_isSharedCheck_267_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_val_203_);
lean_dec(v___x_202_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_267_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___y_208_; lean_object* v_searcher_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v_searcher_260_ = lean_unsigned_to_nat(0u);
v___x_261_ = lean_box(0);
v___x_262_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg(v_val_203_, v_searcher_260_, v___x_261_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_startInclusive_263_; lean_object* v_endExclusive_264_; lean_object* v___x_265_; 
v_startInclusive_263_ = lean_ctor_get(v_val_203_, 1);
v_endExclusive_264_ = lean_ctor_get(v_val_203_, 2);
v___x_265_ = lean_nat_sub(v_endExclusive_264_, v_startInclusive_263_);
v___y_208_ = v___x_265_;
goto v___jp_207_;
}
else
{
lean_object* v_val_266_; 
v_val_266_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_val_266_);
lean_dec_ref_known(v___x_262_, 1);
v___y_208_ = v_val_266_;
goto v___jp_207_;
}
v___jp_207_:
{
lean_object* v_str_209_; lean_object* v_startInclusive_210_; lean_object* v_endExclusive_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_259_; 
v_str_209_ = lean_ctor_get(v_val_203_, 0);
v_startInclusive_210_ = lean_ctor_get(v_val_203_, 1);
v_endExclusive_211_ = lean_ctor_get(v_val_203_, 2);
v_isSharedCheck_259_ = !lean_is_exclusive(v_val_203_);
if (v_isSharedCheck_259_ == 0)
{
v___x_213_ = v_val_203_;
v_isShared_214_ = v_isSharedCheck_259_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_endExclusive_211_);
lean_inc(v_startInclusive_210_);
lean_inc(v_str_209_);
lean_dec(v_val_203_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_259_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_215_ = lean_nat_sub(v_endExclusive_211_, v_startInclusive_210_);
v___x_216_ = lean_nat_dec_eq(v___y_208_, v___x_215_);
lean_dec(v___x_215_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_246_; 
v_a_218_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_246_ == 0)
{
v___x_220_ = v___x_217_;
v_isShared_221_ = v_isSharedCheck_246_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___x_217_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_246_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_222_; lean_object* v___x_224_; 
v___x_222_ = lean_nat_add(v_startInclusive_210_, v___y_208_);
lean_dec(v___y_208_);
lean_inc(v___x_222_);
lean_inc(v_startInclusive_210_);
lean_inc_ref(v_str_209_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 2, v___x_222_);
v___x_224_ = v___x_213_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_str_209_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v_startInclusive_210_);
lean_ctor_set(v_reuseFailAlloc_245_, 2, v___x_222_);
v___x_224_ = v_reuseFailAlloc_245_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
lean_object* v_name_225_; lean_object* v___x_226_; 
v_name_225_ = l_String_Slice_toName(v___x_224_);
lean_dec_ref(v___x_224_);
v___x_226_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_218_, v_name_225_);
lean_dec(v_a_218_);
if (lean_obj_tag(v___x_226_) == 1)
{
lean_object* v_val_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v_val_231_; lean_object* v___x_232_; 
lean_del_object(v___x_220_);
lean_del_object(v___x_205_);
v_val_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_val_227_);
lean_dec_ref_known(v___x_226_, 1);
v___x_228_ = lean_string_utf8_next_fast(v_str_209_, v___x_222_);
lean_dec(v___x_222_);
v___x_229_ = lean_nat_sub(v___x_228_, v_startInclusive_210_);
v___x_230_ = lean_nat_add(v_startInclusive_210_, v___x_229_);
lean_dec(v___x_229_);
lean_dec(v_startInclusive_210_);
v_val_231_ = lean_string_utf8_extract(v_str_209_, v___x_230_, v_endExclusive_211_);
lean_dec(v_endExclusive_211_);
lean_dec(v___x_230_);
lean_dec_ref(v_str_209_);
v___x_232_ = l_Lean_Language_Lean_setOption(v_opts_199_, v_val_227_, v_name_225_, v_val_231_);
return v___x_232_;
}
else
{
lean_object* v___x_233_; uint8_t v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_240_; 
lean_dec(v___x_226_);
lean_dec(v___x_222_);
lean_dec(v_endExclusive_211_);
lean_dec(v_startInclusive_210_);
lean_dec_ref(v_str_209_);
lean_dec_ref(v_opts_199_);
v___x_233_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__0));
v___x_234_ = 1;
v___x_235_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_225_, v___x_234_);
v___x_236_ = lean_string_append(v___x_233_, v___x_235_);
lean_dec_ref(v___x_235_);
v___x_237_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__1));
v___x_238_ = lean_string_append(v___x_236_, v___x_237_);
if (v_isShared_206_ == 0)
{
lean_ctor_set_tag(v___x_205_, 18);
lean_ctor_set(v___x_205_, 0, v___x_238_);
v___x_240_ = v___x_205_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_238_);
v___x_240_ = v_reuseFailAlloc_244_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
lean_object* v___x_242_; 
if (v_isShared_221_ == 0)
{
lean_ctor_set_tag(v___x_220_, 1);
lean_ctor_set(v___x_220_, 0, v___x_240_);
v___x_242_ = v___x_220_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_240_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
}
}
else
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
lean_del_object(v___x_213_);
lean_dec(v_endExclusive_211_);
lean_dec(v_startInclusive_210_);
lean_dec_ref(v_str_209_);
lean_dec(v___y_208_);
lean_del_object(v___x_205_);
lean_dec_ref(v_opts_199_);
v_a_247_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v___x_217_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_217_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_247_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
else
{
lean_object* v___x_255_; lean_object* v___x_257_; 
lean_del_object(v___x_213_);
lean_dec(v_endExclusive_211_);
lean_dec(v_startInclusive_210_);
lean_dec_ref(v_str_209_);
lean_dec(v___y_208_);
lean_dec_ref(v_opts_199_);
v___x_255_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__3));
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 0, v___x_255_);
v___x_257_ = v___x_205_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_255_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
}
}
else
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
lean_dec(v___x_202_);
lean_dec_ref(v_opts_199_);
v___x_268_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__4));
v___x_269_ = lean_string_append(v___x_268_, v_arg_200_);
lean_dec_ref(v_arg_200_);
v___x_270_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__5));
v___x_271_ = lean_string_append(v___x_269_, v___x_270_);
v___x_272_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
v___x_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
return v___x_273_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__setConfigOption___boxed(lean_object* v_opts_274_, lean_object* v_arg_275_, lean_object* v_a_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l___private_LeanIR_0__setConfigOption(v_opts_274_, v_arg_275_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1(lean_object* v_val_278_, lean_object* v_inst_279_, lean_object* v_R_280_, lean_object* v_a_281_, lean_object* v_b_282_, lean_object* v_c_283_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg(v_val_278_, v_a_281_, v_b_282_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___boxed(lean_object* v_val_285_, lean_object* v_inst_286_, lean_object* v_R_287_, lean_object* v_a_288_, lean_object* v_b_289_, lean_object* v_c_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1(v_val_285_, v_inst_286_, v_R_287_, v_a_288_, v_b_289_, v_c_290_);
lean_dec(v_b_289_);
lean_dec_ref(v_val_285_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0___redArg(lean_object* v___x_292_, lean_object* v_inst_293_, lean_object* v_ext_294_, lean_object* v_env_295_){
_start:
{
lean_object* v_toEnvExtension_297_; lean_object* v_addImportedFn_298_; lean_object* v_asyncMode_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v_importedEntries_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_330_; 
v_toEnvExtension_297_ = lean_ctor_get(v_ext_294_, 0);
lean_inc_ref(v_toEnvExtension_297_);
v_addImportedFn_298_ = lean_ctor_get(v_ext_294_, 2);
lean_inc_ref(v_addImportedFn_298_);
lean_dec_ref(v_ext_294_);
v_asyncMode_299_ = lean_ctor_get(v_toEnvExtension_297_, 2);
v___x_300_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v_inst_293_);
lean_inc_ref(v_env_295_);
v___x_301_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_300_, v_toEnvExtension_297_, v_env_295_, v_asyncMode_299_, v___x_292_);
lean_dec_ref(v___x_300_);
v_importedEntries_302_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_330_ == 0)
{
lean_object* v_unused_331_; 
v_unused_331_ = lean_ctor_get(v___x_301_, 1);
lean_dec(v_unused_331_);
v___x_304_ = v___x_301_;
v_isShared_305_ = v_isSharedCheck_330_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_importedEntries_302_);
lean_dec(v___x_301_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_330_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_306_ = l_Lean_Options_empty;
lean_inc_ref(v_env_295_);
v___x_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_307_, 0, v_env_295_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
lean_inc_ref(v_importedEntries_302_);
v___x_308_ = lean_apply_3(v_addImportedFn_298_, v_importedEntries_302_, v___x_307_, lean_box(0));
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_321_; 
v_a_309_ = lean_ctor_get(v___x_308_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_321_ == 0)
{
v___x_311_ = v___x_308_;
v_isShared_312_ = v_isSharedCheck_321_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___x_308_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_321_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 1, v_a_309_);
v___x_314_ = v___x_304_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_importedEntries_302_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v_a_309_);
v___x_314_ = v_reuseFailAlloc_320_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_318_; 
v___x_315_ = lean_box(0);
v___x_316_ = l_Lean_EnvExtension_setState___redArg(v_toEnvExtension_297_, v_env_295_, v___x_314_, v___x_315_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v___x_316_);
v___x_318_ = v___x_311_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_316_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
else
{
lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_329_; 
lean_del_object(v___x_304_);
lean_dec_ref(v_importedEntries_302_);
lean_dec_ref(v_toEnvExtension_297_);
lean_dec_ref(v_env_295_);
v_a_322_ = lean_ctor_get(v___x_308_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_329_ == 0)
{
v___x_324_ = v___x_308_;
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v___x_308_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_a_322_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___elam__0___redArg___boxed(lean_object* v___x_332_, lean_object* v_inst_333_, lean_object* v_ext_334_, lean_object* v_env_335_, lean_object* v___y_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_main___elam__0___redArg(v___x_332_, v_inst_333_, v_ext_334_, v_env_335_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0(lean_object* v___x_338_, lean_object* v_00_u03b1_339_, lean_object* v_00_u03b2_340_, lean_object* v_00_u03c3_341_, lean_object* v_inst_342_, lean_object* v_ext_343_, lean_object* v_env_344_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_main___elam__0___redArg(v___x_338_, v_inst_342_, v_ext_343_, v_env_344_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0___boxed(lean_object* v___x_347_, lean_object* v_00_u03b1_348_, lean_object* v_00_u03b2_349_, lean_object* v_00_u03c3_350_, lean_object* v_inst_351_, lean_object* v_ext_352_, lean_object* v_env_353_, lean_object* v___y_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_main___elam__0(v___x_347_, v_00_u03b1_348_, v_00_u03b2_349_, v_00_u03c3_350_, v_inst_351_, v_ext_352_, v_env_353_);
return v_res_355_;
}
}
static lean_object* _init_l_panic___at___00main_spec__5___closed__0(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = l_instInhabitedError;
v___x_357_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_357_, 0, lean_box(0));
lean_closure_set(v___x_357_, 1, lean_box(0));
lean_closure_set(v___x_357_, 2, v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00main_spec__5(lean_object* v_msg_358_){
_start:
{
lean_object* v___x_360_; lean_object* v___x_19542__overap_361_; lean_object* v___x_362_; 
v___x_360_ = lean_obj_once(&l_panic___at___00main_spec__5___closed__0, &l_panic___at___00main_spec__5___closed__0_once, _init_l_panic___at___00main_spec__5___closed__0);
v___x_19542__overap_361_ = lean_panic_fn_borrowed(v___x_360_, v_msg_358_);
v___x_362_ = lean_apply_1(v___x_19542__overap_361_, lean_box(0));
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00main_spec__5___boxed(lean_object* v_msg_363_, lean_object* v___y_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_panic___at___00main_spec__5(v_msg_363_);
return v_res_365_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00main_spec__8(lean_object* v_opts_366_, lean_object* v_opt_367_){
_start:
{
lean_object* v_name_368_; lean_object* v_defValue_369_; lean_object* v_map_370_; lean_object* v___x_371_; 
v_name_368_ = lean_ctor_get(v_opt_367_, 0);
v_defValue_369_ = lean_ctor_get(v_opt_367_, 1);
v_map_370_ = lean_ctor_get(v_opts_366_, 0);
v___x_371_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_370_, v_name_368_);
if (lean_obj_tag(v___x_371_) == 0)
{
uint8_t v___x_372_; 
v___x_372_ = lean_unbox(v_defValue_369_);
return v___x_372_;
}
else
{
lean_object* v_val_373_; 
v_val_373_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_val_373_);
lean_dec_ref_known(v___x_371_, 1);
if (lean_obj_tag(v_val_373_) == 1)
{
uint8_t v_v_374_; 
v_v_374_ = lean_ctor_get_uint8(v_val_373_, 0);
lean_dec_ref_known(v_val_373_, 0);
return v_v_374_;
}
else
{
uint8_t v___x_375_; 
lean_dec(v_val_373_);
v___x_375_ = lean_unbox(v_defValue_369_);
return v___x_375_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__8___boxed(lean_object* v_opts_376_, lean_object* v_opt_377_){
_start:
{
uint8_t v_res_378_; lean_object* v_r_379_; 
v_res_378_ = l_Lean_Option_get___at___00main_spec__8(v_opts_376_, v_opt_377_);
lean_dec_ref(v_opt_377_);
lean_dec_ref(v_opts_376_);
v_r_379_ = lean_box(v_res_378_);
return v_r_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__9(lean_object* v_opts_380_, lean_object* v_opt_381_){
_start:
{
lean_object* v_name_382_; lean_object* v_defValue_383_; lean_object* v_map_384_; lean_object* v___x_385_; 
v_name_382_ = lean_ctor_get(v_opt_381_, 0);
v_defValue_383_ = lean_ctor_get(v_opt_381_, 1);
v_map_384_ = lean_ctor_get(v_opts_380_, 0);
v___x_385_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_384_, v_name_382_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_inc(v_defValue_383_);
return v_defValue_383_;
}
else
{
lean_object* v_val_386_; 
v_val_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_val_386_);
lean_dec_ref_known(v___x_385_, 1);
if (lean_obj_tag(v_val_386_) == 3)
{
lean_object* v_v_387_; 
v_v_387_ = lean_ctor_get(v_val_386_, 0);
lean_inc(v_v_387_);
lean_dec_ref_known(v_val_386_, 1);
return v_v_387_;
}
else
{
lean_dec(v_val_386_);
lean_inc(v_defValue_383_);
return v_defValue_383_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__9___boxed(lean_object* v_opts_388_, lean_object* v_opt_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Option_get___at___00main_spec__9(v_opts_388_, v_opt_389_);
lean_dec_ref(v_opt_389_);
lean_dec_ref(v_opts_388_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(lean_object* v_a_391_, lean_object* v_x_392_){
_start:
{
if (lean_obj_tag(v_x_392_) == 0)
{
lean_dec(v_a_391_);
return v_x_392_;
}
else
{
lean_object* v_key_393_; lean_object* v_value_394_; lean_object* v_tail_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_428_; 
v_key_393_ = lean_ctor_get(v_x_392_, 0);
v_value_394_ = lean_ctor_get(v_x_392_, 1);
v_tail_395_ = lean_ctor_get(v_x_392_, 2);
v_isSharedCheck_428_ = !lean_is_exclusive(v_x_392_);
if (v_isSharedCheck_428_ == 0)
{
v___x_397_ = v_x_392_;
v_isShared_398_ = v_isSharedCheck_428_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_tail_395_);
lean_inc(v_value_394_);
lean_inc(v_key_393_);
lean_dec(v_x_392_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_428_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
uint8_t v___x_399_; 
v___x_399_ = lean_name_eq(v_key_393_, v_a_391_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_400_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(v_a_391_, v_tail_395_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 2, v___x_400_);
v___x_402_ = v___x_397_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_key_393_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_value_394_);
lean_ctor_set(v_reuseFailAlloc_403_, 2, v___x_400_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
else
{
lean_object* v_toEffectiveImport_404_; lean_object* v_parts_405_; lean_object* v_irParts_406_; uint8_t v_needsIRTrans_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_427_; 
lean_dec(v_key_393_);
v_toEffectiveImport_404_ = lean_ctor_get(v_value_394_, 0);
v_parts_405_ = lean_ctor_get(v_value_394_, 1);
v_irParts_406_ = lean_ctor_get(v_value_394_, 2);
v_needsIRTrans_407_ = lean_ctor_get_uint8(v_value_394_, sizeof(void*)*3);
v_isSharedCheck_427_ = !lean_is_exclusive(v_value_394_);
if (v_isSharedCheck_427_ == 0)
{
v___x_409_ = v_value_394_;
v_isShared_410_ = v_isSharedCheck_427_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_irParts_406_);
lean_inc(v_parts_405_);
lean_inc(v_toEffectiveImport_404_);
lean_dec(v_value_394_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_427_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v_toImport_411_; uint8_t v_hasData_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_426_; 
v_toImport_411_ = lean_ctor_get(v_toEffectiveImport_404_, 0);
v_hasData_412_ = lean_ctor_get_uint8(v_toEffectiveImport_404_, sizeof(void*)*1 + 1);
v_isSharedCheck_426_ = !lean_is_exclusive(v_toEffectiveImport_404_);
if (v_isSharedCheck_426_ == 0)
{
v___x_414_ = v_toEffectiveImport_404_;
v_isShared_415_ = v_isSharedCheck_426_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_toImport_411_);
lean_dec(v_toEffectiveImport_404_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_426_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
uint8_t v___x_416_; lean_object* v___x_418_; 
v___x_416_ = 0;
if (v_isShared_415_ == 0)
{
v___x_418_ = v___x_414_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_toImport_411_);
lean_ctor_set_uint8(v_reuseFailAlloc_425_, sizeof(void*)*1 + 1, v_hasData_412_);
v___x_418_ = v_reuseFailAlloc_425_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_420_; 
lean_ctor_set_uint8(v___x_418_, sizeof(void*)*1, v___x_416_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v___x_418_);
v___x_420_ = v___x_409_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_418_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v_parts_405_);
lean_ctor_set(v_reuseFailAlloc_424_, 2, v_irParts_406_);
lean_ctor_set_uint8(v_reuseFailAlloc_424_, sizeof(void*)*3, v_needsIRTrans_407_);
v___x_420_ = v_reuseFailAlloc_424_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
lean_object* v___x_422_; 
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 1, v___x_420_);
lean_ctor_set(v___x_397_, 0, v_a_391_);
v___x_422_ = v___x_397_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_391_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v___x_420_);
lean_ctor_set(v_reuseFailAlloc_423_, 2, v_tail_395_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
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
lean_object* v___x_429_; uint64_t v___x_430_; 
v___x_429_ = lean_unsigned_to_nat(1723u);
v___x_430_ = lean_uint64_of_nat(v___x_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(lean_object* v_m_431_, lean_object* v_a_432_){
_start:
{
lean_object* v_size_433_; lean_object* v_buckets_434_; lean_object* v___x_435_; uint64_t v___y_437_; 
v_size_433_ = lean_ctor_get(v_m_431_, 0);
v_buckets_434_ = lean_ctor_get(v_m_431_, 1);
v___x_435_ = lean_array_get_size(v_buckets_434_);
if (lean_obj_tag(v_a_432_) == 0)
{
uint64_t v___x_464_; 
v___x_464_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0);
v___y_437_ = v___x_464_;
goto v___jp_436_;
}
else
{
uint64_t v_hash_465_; 
v_hash_465_ = lean_ctor_get_uint64(v_a_432_, sizeof(void*)*2);
v___y_437_ = v_hash_465_;
goto v___jp_436_;
}
v___jp_436_:
{
uint64_t v___x_438_; uint64_t v___x_439_; uint64_t v_fold_440_; uint64_t v___x_441_; uint64_t v___x_442_; uint64_t v___x_443_; size_t v___x_444_; size_t v___x_445_; size_t v___x_446_; size_t v___x_447_; size_t v___x_448_; lean_object* v_bucket_449_; uint8_t v___x_450_; 
v___x_438_ = 32ULL;
v___x_439_ = lean_uint64_shift_right(v___y_437_, v___x_438_);
v_fold_440_ = lean_uint64_xor(v___y_437_, v___x_439_);
v___x_441_ = 16ULL;
v___x_442_ = lean_uint64_shift_right(v_fold_440_, v___x_441_);
v___x_443_ = lean_uint64_xor(v_fold_440_, v___x_442_);
v___x_444_ = lean_uint64_to_usize(v___x_443_);
v___x_445_ = lean_usize_of_nat(v___x_435_);
v___x_446_ = ((size_t)1ULL);
v___x_447_ = lean_usize_sub(v___x_445_, v___x_446_);
v___x_448_ = lean_usize_land(v___x_444_, v___x_447_);
v_bucket_449_ = lean_array_uget_borrowed(v_buckets_434_, v___x_448_);
v___x_450_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_a_432_, v_bucket_449_);
if (v___x_450_ == 0)
{
lean_dec(v_a_432_);
return v_m_431_;
}
else
{
lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_461_; 
lean_inc(v_bucket_449_);
lean_inc_ref(v_buckets_434_);
lean_inc(v_size_433_);
v_isSharedCheck_461_ = !lean_is_exclusive(v_m_431_);
if (v_isSharedCheck_461_ == 0)
{
lean_object* v_unused_462_; lean_object* v_unused_463_; 
v_unused_462_ = lean_ctor_get(v_m_431_, 1);
lean_dec(v_unused_462_);
v_unused_463_ = lean_ctor_get(v_m_431_, 0);
lean_dec(v_unused_463_);
v___x_452_ = v_m_431_;
v_isShared_453_ = v_isSharedCheck_461_;
goto v_resetjp_451_;
}
else
{
lean_dec(v_m_431_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_461_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_454_; lean_object* v_buckets_455_; lean_object* v_bucket_456_; lean_object* v___x_457_; lean_object* v___x_459_; 
v___x_454_ = lean_box(0);
v_buckets_455_ = lean_array_uset(v_buckets_434_, v___x_448_, v___x_454_);
v_bucket_456_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(v_a_432_, v_bucket_449_);
v___x_457_ = lean_array_uset(v_buckets_455_, v___x_448_, v_bucket_456_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 1, v___x_457_);
v___x_459_ = v___x_452_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_size_433_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__0(lean_object* v___x_466_, lean_object* v___x_467_, uint8_t v___x_468_, lean_object* v_importArts_469_, uint8_t v___y_470_, uint8_t v___x_471_, lean_object* v_name_472_, uint8_t v___x_473_, lean_object* v___x_474_, uint8_t v___x_475_){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = lean_st_mk_ref(v___x_466_);
v___x_478_ = l_Lean_importModulesCore(v___x_467_, v___x_468_, v_importArts_469_, v___y_470_, v___x_471_, v___x_477_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v___x_479_; lean_object* v_moduleNameMap_480_; lean_object* v_moduleNames_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_493_; 
lean_dec_ref_known(v___x_478_, 1);
v___x_479_ = lean_st_ref_get(v___x_477_);
lean_dec(v___x_477_);
v_moduleNameMap_480_ = lean_ctor_get(v___x_479_, 0);
v_moduleNames_481_ = lean_ctor_get(v___x_479_, 1);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_493_ == 0)
{
v___x_483_ = v___x_479_;
v_isShared_484_ = v_isSharedCheck_493_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_moduleNames_481_);
lean_inc(v_moduleNameMap_480_);
lean_dec(v___x_479_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_493_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___x_487_; 
v___x_485_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(v_moduleNameMap_480_, v_name_472_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 0, v___x_485_);
v___x_487_ = v___x_483_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_moduleNames_481_);
v___x_487_ = v_reuseFailAlloc_492_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
uint32_t v___x_488_; uint8_t v___x_489_; uint8_t v___x_490_; lean_object* v___x_491_; 
v___x_488_ = 0;
v___x_489_ = l_Lean_instDecidableEqOLeanLevel(v___x_468_, v___x_473_);
v___x_490_ = lean_bool_not(v___x_489_);
v___x_491_ = l_Lean_finalizeImport(v___x_487_, v___x_467_, v___x_474_, v___x_488_, v___x_471_, v___x_475_, v___x_468_, v___x_490_, v___x_471_);
lean_dec_ref(v___x_487_);
return v___x_491_;
}
}
}
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
lean_dec(v___x_477_);
lean_dec_ref(v___x_474_);
lean_dec(v_name_472_);
lean_dec_ref(v___x_467_);
v_a_494_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_478_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_478_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__0___boxed(lean_object* v___x_502_, lean_object* v___x_503_, lean_object* v___x_504_, lean_object* v_importArts_505_, lean_object* v___y_506_, lean_object* v___x_507_, lean_object* v_name_508_, lean_object* v___x_509_, lean_object* v___x_510_, lean_object* v___x_511_, lean_object* v___y_512_){
_start:
{
uint8_t v___x_35659__boxed_513_; uint8_t v___y_35660__boxed_514_; uint8_t v___x_35661__boxed_515_; uint8_t v___x_35662__boxed_516_; uint8_t v___x_35664__boxed_517_; lean_object* v_res_518_; 
v___x_35659__boxed_513_ = lean_unbox(v___x_504_);
v___y_35660__boxed_514_ = lean_unbox(v___y_506_);
v___x_35661__boxed_515_ = lean_unbox(v___x_507_);
v___x_35662__boxed_516_ = lean_unbox(v___x_509_);
v___x_35664__boxed_517_ = lean_unbox(v___x_511_);
v_res_518_ = l_main___lam__0(v___x_502_, v___x_503_, v___x_35659__boxed_513_, v_importArts_505_, v___y_35660__boxed_514_, v___x_35661__boxed_515_, v_name_508_, v___x_35662__boxed_516_, v___x_510_, v___x_35664__boxed_517_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_main___lam__1(lean_object* v___x_522_, lean_object* v___x_523_, lean_object* v___x_524_, lean_object* v_name_525_, lean_object* v_a_526_, uint8_t v___x_527_, lean_object* v_head_528_, lean_object* v___x_529_, lean_object* v___x_530_, lean_object* v___x_531_, lean_object* v___x_532_, lean_object* v___x_533_, lean_object* v___x_534_, lean_object* v___x_535_, lean_object* v___x_536_, uint8_t v___x_537_, lean_object* v___x_538_, uint8_t v___x_539_){
_start:
{
lean_object* v_a_542_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v_env_549_; lean_object* v___x_550_; uint8_t v___x_551_; lean_object* v_fileName_553_; lean_object* v_fileMap_554_; lean_object* v_currRecDepth_555_; lean_object* v_ref_556_; lean_object* v_currNamespace_557_; lean_object* v_openDecls_558_; lean_object* v_initHeartbeats_559_; lean_object* v_maxHeartbeats_560_; lean_object* v_quotContext_561_; lean_object* v_currMacroScope_562_; lean_object* v_cancelTk_x3f_563_; uint8_t v_suppressElabErrors_564_; lean_object* v_inheritedTraceOptions_565_; lean_object* v___y_566_; uint8_t v___y_598_; uint8_t v___x_619_; 
v___x_545_ = lean_io_get_num_heartbeats();
v___x_546_ = lean_st_mk_ref(v___x_522_);
v___x_547_ = lean_st_ref_get(v___x_523_);
v___x_548_ = lean_st_ref_get(v___x_546_);
v_env_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc_ref(v_env_549_);
lean_dec(v___x_548_);
v___x_550_ = l_Lean_diagnostics;
v___x_551_ = l_Lean_Option_get___at___00main_spec__8(v___x_524_, v___x_550_);
v___x_619_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_549_);
lean_dec_ref(v_env_549_);
if (v___x_619_ == 0)
{
if (v___x_551_ == 0)
{
v___y_598_ = v___x_539_;
goto v___jp_597_;
}
else
{
v___y_598_ = v___x_619_;
goto v___jp_597_;
}
}
else
{
v___y_598_ = v___x_551_;
goto v___jp_597_;
}
v___jp_541_:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = lean_mk_io_user_error(v_a_542_);
v___x_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
return v___x_544_;
}
v___jp_552_:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_567_ = l_Lean_maxRecDepth;
v___x_568_ = l_Lean_Option_get___at___00main_spec__9(v___x_524_, v___x_567_);
v___x_569_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_569_, 0, v_fileName_553_);
lean_ctor_set(v___x_569_, 1, v_fileMap_554_);
lean_ctor_set(v___x_569_, 2, v___x_524_);
lean_ctor_set(v___x_569_, 3, v_currRecDepth_555_);
lean_ctor_set(v___x_569_, 4, v___x_568_);
lean_ctor_set(v___x_569_, 5, v_ref_556_);
lean_ctor_set(v___x_569_, 6, v_currNamespace_557_);
lean_ctor_set(v___x_569_, 7, v_openDecls_558_);
lean_ctor_set(v___x_569_, 8, v_initHeartbeats_559_);
lean_ctor_set(v___x_569_, 9, v_maxHeartbeats_560_);
lean_ctor_set(v___x_569_, 10, v_quotContext_561_);
lean_ctor_set(v___x_569_, 11, v_currMacroScope_562_);
lean_ctor_set(v___x_569_, 12, v_cancelTk_x3f_563_);
lean_ctor_set(v___x_569_, 13, v_inheritedTraceOptions_565_);
lean_ctor_set_uint8(v___x_569_, sizeof(void*)*14, v___x_551_);
lean_ctor_set_uint8(v___x_569_, sizeof(void*)*14 + 1, v_suppressElabErrors_564_);
v___x_570_ = l_Lean_Compiler_LCNF_emitC(v_name_525_, v___x_569_, v___y_566_);
lean_dec(v___y_566_);
lean_dec_ref_known(v___x_569_, 14);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_a_571_);
lean_dec_ref_known(v___x_570_, 1);
v___x_572_ = lean_st_ref_get(v___x_546_);
lean_dec(v___x_546_);
lean_dec(v___x_572_);
v___x_573_ = lean_string_to_utf8(v_a_571_);
lean_dec(v_a_571_);
v___x_574_ = lean_io_prim_handle_write(v_a_526_, v___x_573_);
lean_dec_ref(v___x_573_);
return v___x_574_;
}
else
{
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_596_; 
lean_dec(v___x_546_);
v_a_575_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_596_ == 0)
{
v___x_577_ = v___x_570_;
v_isShared_578_ = v_isSharedCheck_596_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_570_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_596_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
if (lean_obj_tag(v_a_575_) == 0)
{
lean_object* v_msg_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_583_; 
v_msg_579_ = lean_ctor_get(v_a_575_, 1);
lean_inc_ref(v_msg_579_);
lean_dec_ref_known(v_a_575_, 2);
v___x_580_ = l_Lean_MessageData_toString(v_msg_579_);
v___x_581_ = lean_mk_io_user_error(v___x_580_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v___x_581_);
v___x_583_ = v___x_577_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_581_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
else
{
lean_object* v_id_585_; lean_object* v___x_586_; 
lean_del_object(v___x_577_);
v_id_585_ = lean_ctor_get(v_a_575_, 0);
lean_inc(v_id_585_);
lean_dec_ref_known(v_a_575_, 2);
v___x_586_ = l_Lean_InternalExceptionId_getName(v_id_585_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_a_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
lean_dec(v_id_585_);
v_a_587_ = lean_ctor_get(v___x_586_, 0);
lean_inc(v_a_587_);
lean_dec_ref_known(v___x_586_, 1);
v___x_588_ = ((lean_object*)(l_main___lam__1___closed__0));
v___x_589_ = l_Lean_Name_toString(v_a_587_, v___x_527_);
v___x_590_ = lean_string_append(v___x_588_, v___x_589_);
lean_dec_ref(v___x_589_);
v_a_542_ = v___x_590_;
goto v___jp_541_;
}
else
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
lean_dec_ref_known(v___x_586_, 1);
v___x_591_ = ((lean_object*)(l_main___lam__1___closed__1));
v___x_592_ = l_Nat_reprFast(v_id_585_);
v___x_593_ = lean_string_append(v___x_591_, v___x_592_);
lean_dec_ref(v___x_592_);
v___x_594_ = ((lean_object*)(l_main___lam__1___closed__2));
v___x_595_ = lean_string_append(v___x_593_, v___x_594_);
v_a_542_ = v___x_595_;
goto v___jp_541_;
}
}
}
}
}
v___jp_597_:
{
uint8_t v___x_599_; 
v___x_599_ = lean_bool_not(v___y_598_);
if (v___x_599_ == 0)
{
lean_dec_ref(v___x_538_);
lean_inc(v___x_546_);
lean_inc(v___x_532_);
v_fileName_553_ = v_head_528_;
v_fileMap_554_ = v___x_529_;
v_currRecDepth_555_ = v___x_530_;
v_ref_556_ = v___x_531_;
v_currNamespace_557_ = v___x_532_;
v_openDecls_558_ = v___x_533_;
v_initHeartbeats_559_ = v___x_545_;
v_maxHeartbeats_560_ = v___x_534_;
v_quotContext_561_ = v___x_532_;
v_currMacroScope_562_ = v___x_535_;
v_cancelTk_x3f_563_ = v___x_536_;
v_suppressElabErrors_564_ = v___x_537_;
v_inheritedTraceOptions_565_ = v___x_547_;
v___y_566_ = v___x_546_;
goto v___jp_552_;
}
else
{
lean_object* v___x_600_; lean_object* v_env_601_; lean_object* v_nextMacroScope_602_; lean_object* v_ngen_603_; lean_object* v_auxDeclNGen_604_; lean_object* v_traceState_605_; lean_object* v_messages_606_; lean_object* v_infoState_607_; lean_object* v_snapshotTasks_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_617_; 
v___x_600_ = lean_st_ref_take(v___x_546_);
v_env_601_ = lean_ctor_get(v___x_600_, 0);
v_nextMacroScope_602_ = lean_ctor_get(v___x_600_, 1);
v_ngen_603_ = lean_ctor_get(v___x_600_, 2);
v_auxDeclNGen_604_ = lean_ctor_get(v___x_600_, 3);
v_traceState_605_ = lean_ctor_get(v___x_600_, 4);
v_messages_606_ = lean_ctor_get(v___x_600_, 6);
v_infoState_607_ = lean_ctor_get(v___x_600_, 7);
v_snapshotTasks_608_ = lean_ctor_get(v___x_600_, 8);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_617_ == 0)
{
lean_object* v_unused_618_; 
v_unused_618_ = lean_ctor_get(v___x_600_, 5);
lean_dec(v_unused_618_);
v___x_610_ = v___x_600_;
v_isShared_611_ = v_isSharedCheck_617_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_snapshotTasks_608_);
lean_inc(v_infoState_607_);
lean_inc(v_messages_606_);
lean_inc(v_traceState_605_);
lean_inc(v_auxDeclNGen_604_);
lean_inc(v_ngen_603_);
lean_inc(v_nextMacroScope_602_);
lean_inc(v_env_601_);
lean_dec(v___x_600_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_617_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_612_; lean_object* v___x_614_; 
v___x_612_ = l_Lean_Kernel_enableDiag(v_env_601_, v___x_551_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 5, v___x_538_);
lean_ctor_set(v___x_610_, 0, v___x_612_);
v___x_614_ = v___x_610_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_nextMacroScope_602_);
lean_ctor_set(v_reuseFailAlloc_616_, 2, v_ngen_603_);
lean_ctor_set(v_reuseFailAlloc_616_, 3, v_auxDeclNGen_604_);
lean_ctor_set(v_reuseFailAlloc_616_, 4, v_traceState_605_);
lean_ctor_set(v_reuseFailAlloc_616_, 5, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_616_, 6, v_messages_606_);
lean_ctor_set(v_reuseFailAlloc_616_, 7, v_infoState_607_);
lean_ctor_set(v_reuseFailAlloc_616_, 8, v_snapshotTasks_608_);
v___x_614_ = v_reuseFailAlloc_616_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_615_; 
v___x_615_ = lean_st_ref_set(v___x_546_, v___x_614_);
lean_inc(v___x_546_);
lean_inc(v___x_532_);
v_fileName_553_ = v_head_528_;
v_fileMap_554_ = v___x_529_;
v_currRecDepth_555_ = v___x_530_;
v_ref_556_ = v___x_531_;
v_currNamespace_557_ = v___x_532_;
v_openDecls_558_ = v___x_533_;
v_initHeartbeats_559_ = v___x_545_;
v_maxHeartbeats_560_ = v___x_534_;
v_quotContext_561_ = v___x_532_;
v_currMacroScope_562_ = v___x_535_;
v_cancelTk_x3f_563_ = v___x_536_;
v_suppressElabErrors_564_ = v___x_537_;
v_inheritedTraceOptions_565_ = v___x_547_;
v___y_566_ = v___x_546_;
goto v___jp_552_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__1___boxed(lean_object** _args){
lean_object* v___x_620_ = _args[0];
lean_object* v___x_621_ = _args[1];
lean_object* v___x_622_ = _args[2];
lean_object* v_name_623_ = _args[3];
lean_object* v_a_624_ = _args[4];
lean_object* v___x_625_ = _args[5];
lean_object* v_head_626_ = _args[6];
lean_object* v___x_627_ = _args[7];
lean_object* v___x_628_ = _args[8];
lean_object* v___x_629_ = _args[9];
lean_object* v___x_630_ = _args[10];
lean_object* v___x_631_ = _args[11];
lean_object* v___x_632_ = _args[12];
lean_object* v___x_633_ = _args[13];
lean_object* v___x_634_ = _args[14];
lean_object* v___x_635_ = _args[15];
lean_object* v___x_636_ = _args[16];
lean_object* v___x_637_ = _args[17];
lean_object* v___y_638_ = _args[18];
_start:
{
uint8_t v___x_35741__boxed_639_; uint8_t v___x_35751__boxed_640_; uint8_t v___x_35753__boxed_641_; lean_object* v_res_642_; 
v___x_35741__boxed_639_ = lean_unbox(v___x_625_);
v___x_35751__boxed_640_ = lean_unbox(v___x_635_);
v___x_35753__boxed_641_ = lean_unbox(v___x_637_);
v_res_642_ = l_main___lam__1(v___x_620_, v___x_621_, v___x_622_, v_name_623_, v_a_624_, v___x_35741__boxed_639_, v_head_626_, v___x_627_, v___x_628_, v___x_629_, v___x_630_, v___x_631_, v___x_632_, v___x_633_, v___x_634_, v___x_35751__boxed_640_, v___x_636_, v___x_35753__boxed_641_);
lean_dec(v_a_624_);
lean_dec(v___x_621_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(lean_object* v_s_643_){
_start:
{
lean_object* v___x_645_; lean_object* v_putStr_646_; lean_object* v___x_647_; 
v___x_645_ = lean_get_stderr();
v_putStr_646_ = lean_ctor_get(v___x_645_, 4);
lean_inc_ref(v_putStr_646_);
lean_dec_ref(v___x_645_);
v___x_647_ = lean_apply_2(v_putStr_646_, v_s_643_, lean_box(0));
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8___boxed(lean_object* v_s_648_, lean_object* v_a_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v_s_648_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6(lean_object* v_s_651_){
_start:
{
uint32_t v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_653_ = 10;
v___x_654_ = lean_string_push(v_s_651_, v___x_653_);
v___x_655_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v___x_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6___boxed(lean_object* v_s_656_, lean_object* v_a_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_IO_eprintln___at___00main_spec__6(v_s_656_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(lean_object* v_o_662_, lean_object* v_k_663_, lean_object* v_v_664_){
_start:
{
lean_object* v_map_665_; uint8_t v_hasTrace_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_680_; 
v_map_665_ = lean_ctor_get(v_o_662_, 0);
v_hasTrace_666_ = lean_ctor_get_uint8(v_o_662_, sizeof(void*)*1);
v_isSharedCheck_680_ = !lean_is_exclusive(v_o_662_);
if (v_isSharedCheck_680_ == 0)
{
v___x_668_ = v_o_662_;
v_isShared_669_ = v_isSharedCheck_680_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_map_665_);
lean_dec(v_o_662_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_680_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_670_, 0, v_v_664_);
lean_inc(v_k_663_);
v___x_671_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_663_, v___x_670_, v_map_665_);
if (v_hasTrace_666_ == 0)
{
lean_object* v___x_672_; uint8_t v___x_673_; lean_object* v___x_675_; 
v___x_672_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_673_ = l_Lean_Name_isPrefixOf(v___x_672_, v_k_663_);
lean_dec(v_k_663_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v___x_671_);
v___x_675_ = v___x_668_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_671_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_ctor_set_uint8(v___x_675_, sizeof(void*)*1, v___x_673_);
return v___x_675_;
}
}
else
{
lean_object* v___x_678_; 
lean_dec(v_k_663_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v___x_671_);
v___x_678_ = v___x_668_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_671_);
lean_ctor_set_uint8(v_reuseFailAlloc_679_, sizeof(void*)*1, v_hasTrace_666_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00main_spec__3(lean_object* v_opts_681_, lean_object* v_opt_682_, lean_object* v_val_683_){
_start:
{
lean_object* v_name_684_; lean_object* v___x_685_; 
v_name_684_ = lean_ctor_get(v_opt_682_, 0);
lean_inc(v_name_684_);
lean_dec_ref(v_opt_682_);
v___x_685_ = l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(v_opts_681_, v_name_684_, v_val_683_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(lean_object* v___y_687_, lean_object* v_as_688_, size_t v_i_689_, size_t v_stop_690_, lean_object* v_b_691_){
_start:
{
lean_object* v___y_693_; uint8_t v___x_697_; 
v___x_697_ = lean_usize_dec_eq(v_i_689_, v_stop_690_);
if (v___x_697_ == 0)
{
lean_object* v_fst_698_; lean_object* v_snd_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___y_703_; 
v_fst_698_ = lean_ctor_get(v_b_691_, 0);
v_snd_699_ = lean_ctor_get(v_b_691_, 1);
v___x_700_ = lean_array_uget_borrowed(v_as_688_, v_i_689_);
v___x_701_ = l_Lean_IR_Decl_name(v___x_700_);
if (lean_obj_tag(v___x_701_) == 1)
{
lean_object* v_pre_716_; lean_object* v_str_717_; lean_object* v___x_718_; uint8_t v___x_719_; 
v_pre_716_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_pre_716_);
v_str_717_ = lean_ctor_get(v___x_701_, 1);
lean_inc_ref(v_str_717_);
v___x_718_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___closed__0));
v___x_719_ = lean_string_dec_eq(v_str_717_, v___x_718_);
lean_dec_ref(v_str_717_);
if (v___x_719_ == 0)
{
lean_dec(v_pre_716_);
lean_inc_ref(v___x_701_);
v___y_703_ = v___x_701_;
goto v___jp_702_;
}
else
{
v___y_703_ = v_pre_716_;
goto v___jp_702_;
}
}
else
{
lean_inc(v___x_701_);
v___y_703_ = v___x_701_;
goto v___jp_702_;
}
v___jp_702_:
{
uint8_t v___x_704_; 
lean_inc_ref(v___y_687_);
v___x_704_ = l_Lean_isExtern(v___y_687_, v___y_703_);
if (v___x_704_ == 0)
{
lean_dec(v___x_701_);
v___y_693_ = v_b_691_;
goto v___jp_692_;
}
else
{
lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_713_; 
lean_inc(v_snd_699_);
lean_inc(v_fst_698_);
v_isSharedCheck_713_ = !lean_is_exclusive(v_b_691_);
if (v_isSharedCheck_713_ == 0)
{
lean_object* v_unused_714_; lean_object* v_unused_715_; 
v_unused_714_ = lean_ctor_get(v_b_691_, 1);
lean_dec(v_unused_714_);
v_unused_715_ = lean_ctor_get(v_b_691_, 0);
lean_dec(v_unused_715_);
v___x_706_ = v_b_691_;
v_isShared_707_ = v_isSharedCheck_713_;
goto v_resetjp_705_;
}
else
{
lean_dec(v_b_691_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_713_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_711_; 
lean_inc_n(v___x_700_, 2);
v___x_708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_700_);
lean_ctor_set(v___x_708_, 1, v_fst_698_);
v___x_709_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(v_snd_699_, v___x_701_, v___x_700_);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 1, v___x_709_);
lean_ctor_set(v___x_706_, 0, v___x_708_);
v___x_711_ = v___x_706_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_708_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v___x_709_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
v___y_693_ = v___x_711_;
goto v___jp_692_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_687_);
return v_b_691_;
}
v___jp_692_:
{
size_t v___x_694_; size_t v___x_695_; 
v___x_694_ = ((size_t)1ULL);
v___x_695_ = lean_usize_add(v_i_689_, v___x_694_);
v_i_689_ = v___x_695_;
v_b_691_ = v___y_693_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___boxed(lean_object* v___y_720_, lean_object* v_as_721_, lean_object* v_i_722_, lean_object* v_stop_723_, lean_object* v_b_724_){
_start:
{
size_t v_i_boxed_725_; size_t v_stop_boxed_726_; lean_object* v_res_727_; 
v_i_boxed_725_ = lean_unbox_usize(v_i_722_);
lean_dec(v_i_722_);
v_stop_boxed_726_ = lean_unbox_usize(v_stop_723_);
lean_dec(v_stop_723_);
v_res_727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_720_, v_as_721_, v_i_boxed_725_, v_stop_boxed_726_, v_b_724_);
lean_dec_ref(v_as_721_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg(lean_object* v_as_x27_729_, lean_object* v_b_730_){
_start:
{
if (lean_obj_tag(v_as_x27_729_) == 0)
{
lean_object* v___x_732_; 
v___x_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_732_, 0, v_b_730_);
return v___x_732_;
}
else
{
lean_object* v_head_733_; lean_object* v_tail_734_; lean_object* v_fst_735_; lean_object* v_snd_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_761_; 
v_head_733_ = lean_ctor_get(v_as_x27_729_, 0);
v_tail_734_ = lean_ctor_get(v_as_x27_729_, 1);
v_fst_735_ = lean_ctor_get(v_b_730_, 0);
v_snd_736_ = lean_ctor_get(v_b_730_, 1);
v_isSharedCheck_761_ = !lean_is_exclusive(v_b_730_);
if (v_isSharedCheck_761_ == 0)
{
v___x_738_ = v_b_730_;
v_isShared_739_ = v_isSharedCheck_761_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_snd_736_);
lean_inc(v_fst_735_);
lean_dec(v_b_730_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_761_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_740_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0));
v___x_741_ = lean_string_dec_eq(v_head_733_, v___x_740_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; 
lean_inc(v_head_733_);
v___x_742_ = l___private_LeanIR_0__setConfigOption(v_snd_736_, v_head_733_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_a_743_; lean_object* v___x_745_; 
v_a_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_a_743_);
lean_dec_ref_known(v___x_742_, 1);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 1, v_a_743_);
v___x_745_ = v___x_738_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_fst_735_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_a_743_);
v___x_745_ = v_reuseFailAlloc_747_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
v_as_x27_729_ = v_tail_734_;
v_b_730_ = v___x_745_;
goto _start;
}
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
lean_del_object(v___x_738_);
lean_dec(v_fst_735_);
v_a_748_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_742_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_742_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
else
{
lean_object* v___x_756_; lean_object* v___x_758_; 
lean_dec(v_fst_735_);
v___x_756_ = lean_box(v___x_741_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v___x_756_);
v___x_758_ = v___x_738_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_snd_736_);
v___x_758_ = v_reuseFailAlloc_760_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
v_as_x27_729_ = v_tail_734_;
v_b_730_ = v___x_758_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg___boxed(lean_object* v_as_x27_762_, lean_object* v_b_763_, lean_object* v___y_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_762_, v_b_763_);
lean_dec(v_as_x27_762_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(lean_object* v_as_766_, size_t v_i_767_, size_t v_stop_768_, lean_object* v_b_769_){
_start:
{
uint8_t v___x_770_; 
v___x_770_ = lean_usize_dec_eq(v_i_767_, v_stop_768_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; lean_object* v_toEnvExtension_772_; lean_object* v_asyncMode_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; size_t v___x_777_; size_t v___x_778_; 
v___x_771_ = l_Lean_Compiler_LCNF_impureSigExt;
v_toEnvExtension_772_ = lean_ctor_get(v___x_771_, 0);
v_asyncMode_773_ = lean_ctor_get(v_toEnvExtension_772_, 2);
v___x_774_ = lean_box(0);
v___x_775_ = lean_array_uget_borrowed(v_as_766_, v_i_767_);
lean_inc(v___x_775_);
v___x_776_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_771_, v_b_769_, v___x_775_, v_asyncMode_773_, v___x_774_);
v___x_777_ = ((size_t)1ULL);
v___x_778_ = lean_usize_add(v_i_767_, v___x_777_);
v_i_767_ = v___x_778_;
v_b_769_ = v___x_776_;
goto _start;
}
else
{
return v_b_769_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18___boxed(lean_object* v_as_780_, lean_object* v_i_781_, lean_object* v_stop_782_, lean_object* v_b_783_){
_start:
{
size_t v_i_boxed_784_; size_t v_stop_boxed_785_; lean_object* v_res_786_; 
v_i_boxed_784_ = lean_unbox_usize(v_i_781_);
lean_dec(v_i_781_);
v_stop_boxed_785_ = lean_unbox_usize(v_stop_782_);
lean_dec(v_stop_782_);
v_res_786_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_as_780_, v_i_boxed_784_, v_stop_boxed_785_, v_b_783_);
lean_dec_ref(v_as_780_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(lean_object* v_as_790_, size_t v_sz_791_, size_t v_i_792_, lean_object* v_b_793_, lean_object* v___y_794_){
_start:
{
uint8_t v___x_796_; 
v___x_796_ = lean_usize_dec_lt(v_i_792_, v_sz_791_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; 
v___x_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_797_, 0, v_b_793_);
return v___x_797_;
}
else
{
uint8_t v___x_798_; lean_object* v_a_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
lean_dec_ref(v_b_793_);
v___x_798_ = 0;
v_a_799_ = lean_array_uget_borrowed(v_as_790_, v_i_792_);
lean_inc(v_a_799_);
v___x_800_ = l_Lean_Message_toString(v_a_799_, v___x_798_);
v___x_801_ = l_IO_eprintln___at___00main_spec__6(v___x_800_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v___x_802_; size_t v___x_803_; size_t v___x_804_; 
lean_dec_ref_known(v___x_801_, 1);
v___x_802_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_803_ = ((size_t)1ULL);
v___x_804_ = lean_usize_add(v_i_792_, v___x_803_);
v_i_792_ = v___x_804_;
v_b_793_ = v___x_802_;
goto _start;
}
else
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_818_; 
v_a_806_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_818_ == 0)
{
v___x_808_ = v___x_801_;
v_isShared_809_ = v_isSharedCheck_818_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_801_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_818_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v_ref_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_816_; 
v_ref_810_ = lean_ctor_get(v___y_794_, 5);
v___x_811_ = lean_io_error_to_string(v_a_806_);
v___x_812_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
v___x_813_ = l_Lean_MessageData_ofFormat(v___x_812_);
lean_inc(v_ref_810_);
v___x_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_814_, 0, v_ref_810_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v___x_814_);
v___x_816_ = v___x_808_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___boxed(lean_object* v_as_819_, lean_object* v_sz_820_, lean_object* v_i_821_, lean_object* v_b_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
size_t v_sz_boxed_825_; size_t v_i_boxed_826_; lean_object* v_res_827_; 
v_sz_boxed_825_ = lean_unbox_usize(v_sz_820_);
lean_dec(v_sz_820_);
v_i_boxed_826_ = lean_unbox_usize(v_i_821_);
lean_dec(v_i_821_);
v_res_827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_819_, v_sz_boxed_825_, v_i_boxed_826_, v_b_822_, v___y_823_);
lean_dec_ref(v___y_823_);
lean_dec_ref(v_as_819_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(lean_object* v_as_828_, size_t v_sz_829_, size_t v_i_830_, lean_object* v_b_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
uint8_t v___x_835_; 
v___x_835_ = lean_usize_dec_lt(v_i_830_, v_sz_829_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; 
v___x_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_836_, 0, v_b_831_);
return v___x_836_;
}
else
{
uint8_t v___x_837_; lean_object* v_a_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
lean_dec_ref(v_b_831_);
v___x_837_ = 0;
v_a_838_ = lean_array_uget_borrowed(v_as_828_, v_i_830_);
lean_inc(v_a_838_);
v___x_839_ = l_Lean_Message_toString(v_a_838_, v___x_837_);
v___x_840_ = l_IO_eprintln___at___00main_spec__6(v___x_839_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v___x_841_; size_t v___x_842_; size_t v___x_843_; lean_object* v___x_844_; 
lean_dec_ref_known(v___x_840_, 1);
v___x_841_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_842_ = ((size_t)1ULL);
v___x_843_ = lean_usize_add(v_i_830_, v___x_842_);
v___x_844_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_828_, v_sz_829_, v___x_843_, v___x_841_, v___y_832_);
return v___x_844_;
}
else
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_857_; 
v_a_845_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_857_ == 0)
{
v___x_847_ = v___x_840_;
v_isShared_848_ = v_isSharedCheck_857_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_840_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_857_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v_ref_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_855_; 
v_ref_849_ = lean_ctor_get(v___y_832_, 5);
v___x_850_ = lean_io_error_to_string(v_a_845_);
v___x_851_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
v___x_852_ = l_Lean_MessageData_ofFormat(v___x_851_);
lean_inc(v_ref_849_);
v___x_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_853_, 0, v_ref_849_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v___x_853_);
v___x_855_ = v___x_847_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_853_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27___boxed(lean_object* v_as_858_, lean_object* v_sz_859_, lean_object* v_i_860_, lean_object* v_b_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
size_t v_sz_boxed_865_; size_t v_i_boxed_866_; lean_object* v_res_867_; 
v_sz_boxed_865_ = lean_unbox_usize(v_sz_859_);
lean_dec(v_sz_859_);
v_i_boxed_866_ = lean_unbox_usize(v_i_860_);
lean_dec(v_i_860_);
v_res_867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(v_as_858_, v_sz_boxed_865_, v_i_boxed_866_, v_b_861_, v___y_862_, v___y_863_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec_ref(v_as_858_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(lean_object* v_as_871_, size_t v_sz_872_, size_t v_i_873_, lean_object* v_b_874_, lean_object* v___y_875_){
_start:
{
uint8_t v___x_877_; 
v___x_877_ = lean_usize_dec_lt(v_i_873_, v_sz_872_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; 
v___x_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_878_, 0, v_b_874_);
return v___x_878_;
}
else
{
uint8_t v___x_879_; lean_object* v_a_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
lean_dec_ref(v_b_874_);
v___x_879_ = 0;
v_a_880_ = lean_array_uget_borrowed(v_as_871_, v_i_873_);
lean_inc(v_a_880_);
v___x_881_ = l_Lean_Message_toString(v_a_880_, v___x_879_);
v___x_882_ = l_IO_eprintln___at___00main_spec__6(v___x_881_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v___x_883_; size_t v___x_884_; size_t v___x_885_; 
lean_dec_ref_known(v___x_882_, 1);
v___x_883_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_884_ = ((size_t)1ULL);
v___x_885_ = lean_usize_add(v_i_873_, v___x_884_);
v_i_873_ = v___x_885_;
v_b_874_ = v___x_883_;
goto _start;
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_899_; 
v_a_887_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_899_ == 0)
{
v___x_889_ = v___x_882_;
v_isShared_890_ = v_isSharedCheck_899_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_882_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_899_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v_ref_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_897_; 
v_ref_891_ = lean_ctor_get(v___y_875_, 5);
v___x_892_ = lean_io_error_to_string(v_a_887_);
v___x_893_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
v___x_894_ = l_Lean_MessageData_ofFormat(v___x_893_);
lean_inc(v_ref_891_);
v___x_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_895_, 0, v_ref_891_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_895_);
v___x_897_ = v___x_889_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_895_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___boxed(lean_object* v_as_900_, lean_object* v_sz_901_, lean_object* v_i_902_, lean_object* v_b_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
size_t v_sz_boxed_906_; size_t v_i_boxed_907_; lean_object* v_res_908_; 
v_sz_boxed_906_ = lean_unbox_usize(v_sz_901_);
lean_dec(v_sz_901_);
v_i_boxed_907_ = lean_unbox_usize(v_i_902_);
lean_dec(v_i_902_);
v_res_908_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_900_, v_sz_boxed_906_, v_i_boxed_907_, v_b_903_, v___y_904_);
lean_dec_ref(v___y_904_);
lean_dec_ref(v_as_900_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(lean_object* v_as_909_, size_t v_sz_910_, size_t v_i_911_, lean_object* v_b_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
uint8_t v___x_916_; 
v___x_916_ = lean_usize_dec_lt(v_i_911_, v_sz_910_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; 
v___x_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_917_, 0, v_b_912_);
return v___x_917_;
}
else
{
uint8_t v___x_918_; lean_object* v_a_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
lean_dec_ref(v_b_912_);
v___x_918_ = 0;
v_a_919_ = lean_array_uget_borrowed(v_as_909_, v_i_911_);
lean_inc(v_a_919_);
v___x_920_ = l_Lean_Message_toString(v_a_919_, v___x_918_);
v___x_921_ = l_IO_eprintln___at___00main_spec__6(v___x_920_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v___x_922_; size_t v___x_923_; size_t v___x_924_; lean_object* v___x_925_; 
lean_dec_ref_known(v___x_921_, 1);
v___x_922_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_923_ = ((size_t)1ULL);
v___x_924_ = lean_usize_add(v_i_911_, v___x_923_);
v___x_925_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_909_, v_sz_910_, v___x_924_, v___x_922_, v___y_913_);
return v___x_925_;
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_938_; 
v_a_926_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_938_ == 0)
{
v___x_928_ = v___x_921_;
v_isShared_929_ = v_isSharedCheck_938_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_921_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_938_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v_ref_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_936_; 
v_ref_930_ = lean_ctor_get(v___y_913_, 5);
v___x_931_ = lean_io_error_to_string(v_a_926_);
v___x_932_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
v___x_933_ = l_Lean_MessageData_ofFormat(v___x_932_);
lean_inc(v_ref_930_);
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v_ref_930_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 0, v___x_934_);
v___x_936_ = v___x_928_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_934_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38___boxed(lean_object* v_as_939_, lean_object* v_sz_940_, lean_object* v_i_941_, lean_object* v_b_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
size_t v_sz_boxed_946_; size_t v_i_boxed_947_; lean_object* v_res_948_; 
v_sz_boxed_946_ = lean_unbox_usize(v_sz_940_);
lean_dec(v_sz_940_);
v_i_boxed_947_ = lean_unbox_usize(v_i_941_);
lean_dec(v_i_941_);
v_res_948_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(v_as_939_, v_sz_boxed_946_, v_i_boxed_947_, v_b_942_, v___y_943_, v___y_944_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec_ref(v_as_939_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(lean_object* v_init_949_, lean_object* v_n_950_, lean_object* v_b_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
if (lean_obj_tag(v_n_950_) == 0)
{
lean_object* v_cs_955_; lean_object* v___x_956_; lean_object* v___x_957_; size_t v_sz_958_; size_t v___x_959_; lean_object* v___x_960_; 
v_cs_955_ = lean_ctor_get(v_n_950_, 0);
v___x_956_ = lean_box(0);
v___x_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
lean_ctor_set(v___x_957_, 1, v_b_951_);
v_sz_958_ = lean_array_size(v_cs_955_);
v___x_959_ = ((size_t)0ULL);
v___x_960_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(v_init_949_, v_cs_955_, v_sz_958_, v___x_959_, v___x_957_, v___y_952_, v___y_953_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_975_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_975_ == 0)
{
v___x_963_ = v___x_960_;
v_isShared_964_ = v_isSharedCheck_975_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_960_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_975_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v_fst_965_; 
v_fst_965_ = lean_ctor_get(v_a_961_, 0);
if (lean_obj_tag(v_fst_965_) == 0)
{
lean_object* v_snd_966_; lean_object* v___x_967_; lean_object* v___x_969_; 
v_snd_966_ = lean_ctor_get(v_a_961_, 1);
lean_inc(v_snd_966_);
lean_dec(v_a_961_);
v___x_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_967_, 0, v_snd_966_);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v___x_967_);
v___x_969_ = v___x_963_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_967_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
else
{
lean_object* v_val_971_; lean_object* v___x_973_; 
lean_inc_ref(v_fst_965_);
lean_dec(v_a_961_);
v_val_971_ = lean_ctor_get(v_fst_965_, 0);
lean_inc(v_val_971_);
lean_dec_ref_known(v_fst_965_, 1);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v_val_971_);
v___x_973_ = v___x_963_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_val_971_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
else
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
v_a_976_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v___x_960_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_960_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_976_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
}
else
{
lean_object* v_vs_984_; lean_object* v___x_985_; lean_object* v___x_986_; size_t v_sz_987_; size_t v___x_988_; lean_object* v___x_989_; 
v_vs_984_ = lean_ctor_get(v_n_950_, 0);
v___x_985_ = lean_box(0);
v___x_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
lean_ctor_set(v___x_986_, 1, v_b_951_);
v_sz_987_ = lean_array_size(v_vs_984_);
v___x_988_ = ((size_t)0ULL);
v___x_989_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(v_vs_984_, v_sz_987_, v___x_988_, v___x_986_, v___y_952_, v___y_953_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1004_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_992_ = v___x_989_;
v_isShared_993_ = v_isSharedCheck_1004_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_989_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1004_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v_fst_994_; 
v_fst_994_ = lean_ctor_get(v_a_990_, 0);
if (lean_obj_tag(v_fst_994_) == 0)
{
lean_object* v_snd_995_; lean_object* v___x_996_; lean_object* v___x_998_; 
v_snd_995_ = lean_ctor_get(v_a_990_, 1);
lean_inc(v_snd_995_);
lean_dec(v_a_990_);
v___x_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_996_, 0, v_snd_995_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v___x_996_);
v___x_998_ = v___x_992_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_996_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
else
{
lean_object* v_val_1000_; lean_object* v___x_1002_; 
lean_inc_ref(v_fst_994_);
lean_dec(v_a_990_);
v_val_1000_ = lean_ctor_get(v_fst_994_, 0);
lean_inc(v_val_1000_);
lean_dec_ref_known(v_fst_994_, 1);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v_val_1000_);
v___x_1002_ = v___x_992_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_val_1000_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
else
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1012_; 
v_a_1005_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1007_ = v___x_989_;
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_989_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1010_; 
if (v_isShared_1008_ == 0)
{
v___x_1010_ = v___x_1007_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_a_1005_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(lean_object* v_init_1013_, lean_object* v_as_1014_, size_t v_sz_1015_, size_t v_i_1016_, lean_object* v_b_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
uint8_t v___x_1021_; 
v___x_1021_ = lean_usize_dec_lt(v_i_1016_, v_sz_1015_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1022_; 
v___x_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1022_, 0, v_b_1017_);
return v___x_1022_;
}
else
{
lean_object* v_snd_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1057_; 
v_snd_1023_ = lean_ctor_get(v_b_1017_, 1);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_b_1017_);
if (v_isSharedCheck_1057_ == 0)
{
lean_object* v_unused_1058_; 
v_unused_1058_ = lean_ctor_get(v_b_1017_, 0);
lean_dec(v_unused_1058_);
v___x_1025_ = v_b_1017_;
v_isShared_1026_ = v_isSharedCheck_1057_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_snd_1023_);
lean_dec(v_b_1017_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1057_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v_a_1027_; lean_object* v___x_1028_; 
v_a_1027_ = lean_array_uget_borrowed(v_as_1014_, v_i_1016_);
lean_inc(v_snd_1023_);
v___x_1028_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_1013_, v_a_1027_, v_snd_1023_, v___y_1018_, v___y_1019_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1048_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1031_ = v___x_1028_;
v_isShared_1032_ = v_isSharedCheck_1048_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1028_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1048_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
if (lean_obj_tag(v_a_1029_) == 0)
{
lean_object* v___x_1033_; lean_object* v___x_1035_; 
v___x_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1033_, 0, v_a_1029_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v___x_1033_);
v___x_1035_ = v___x_1025_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1033_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_snd_1023_);
v___x_1035_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1037_; 
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 0, v___x_1035_);
v___x_1037_ = v___x_1031_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
else
{
lean_object* v_a_1040_; lean_object* v___x_1041_; lean_object* v___x_1043_; 
lean_del_object(v___x_1031_);
lean_dec(v_snd_1023_);
v_a_1040_ = lean_ctor_get(v_a_1029_, 0);
lean_inc(v_a_1040_);
lean_dec_ref_known(v_a_1029_, 1);
v___x_1041_ = lean_box(0);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 1, v_a_1040_);
lean_ctor_set(v___x_1025_, 0, v___x_1041_);
v___x_1043_ = v___x_1025_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1041_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v_a_1040_);
v___x_1043_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
size_t v___x_1044_; size_t v___x_1045_; 
v___x_1044_ = ((size_t)1ULL);
v___x_1045_ = lean_usize_add(v_i_1016_, v___x_1044_);
v_i_1016_ = v___x_1045_;
v_b_1017_ = v___x_1043_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
lean_del_object(v___x_1025_);
lean_dec(v_snd_1023_);
v_a_1049_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1051_ = v___x_1028_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1028_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37___boxed(lean_object* v_init_1059_, lean_object* v_as_1060_, lean_object* v_sz_1061_, lean_object* v_i_1062_, lean_object* v_b_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
size_t v_sz_boxed_1067_; size_t v_i_boxed_1068_; lean_object* v_res_1069_; 
v_sz_boxed_1067_ = lean_unbox_usize(v_sz_1061_);
lean_dec(v_sz_1061_);
v_i_boxed_1068_ = lean_unbox_usize(v_i_1062_);
lean_dec(v_i_1062_);
v_res_1069_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(v_init_1059_, v_as_1060_, v_sz_boxed_1067_, v_i_boxed_1068_, v_b_1063_, v___y_1064_, v___y_1065_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec_ref(v_as_1060_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26___boxed(lean_object* v_init_1070_, lean_object* v_n_1071_, lean_object* v_b_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_1070_, v_n_1071_, v_b_1072_, v___y_1073_, v___y_1074_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec_ref(v_n_1071_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__12(lean_object* v_t_1077_, lean_object* v_init_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_root_1082_; lean_object* v_tail_1083_; lean_object* v___x_1084_; 
v_root_1082_ = lean_ctor_get(v_t_1077_, 0);
v_tail_1083_ = lean_ctor_get(v_t_1077_, 1);
v___x_1084_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_1078_, v_root_1082_, v_init_1078_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1121_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1087_ = v___x_1084_;
v_isShared_1088_ = v_isSharedCheck_1121_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1084_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1121_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
if (lean_obj_tag(v_a_1085_) == 0)
{
lean_object* v_a_1089_; lean_object* v___x_1091_; 
v_a_1089_ = lean_ctor_get(v_a_1085_, 0);
lean_inc(v_a_1089_);
lean_dec_ref_known(v_a_1085_, 1);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v_a_1089_);
v___x_1091_ = v___x_1087_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; size_t v_sz_1096_; size_t v___x_1097_; lean_object* v___x_1098_; 
lean_del_object(v___x_1087_);
v_a_1093_ = lean_ctor_get(v_a_1085_, 0);
lean_inc(v_a_1093_);
lean_dec_ref_known(v_a_1085_, 1);
v___x_1094_ = lean_box(0);
v___x_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
lean_ctor_set(v___x_1095_, 1, v_a_1093_);
v_sz_1096_ = lean_array_size(v_tail_1083_);
v___x_1097_ = ((size_t)0ULL);
v___x_1098_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(v_tail_1083_, v_sz_1096_, v___x_1097_, v___x_1095_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1112_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1101_ = v___x_1098_;
v_isShared_1102_ = v_isSharedCheck_1112_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1098_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1112_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v_fst_1103_; 
v_fst_1103_ = lean_ctor_get(v_a_1099_, 0);
if (lean_obj_tag(v_fst_1103_) == 0)
{
lean_object* v_snd_1104_; lean_object* v___x_1106_; 
v_snd_1104_ = lean_ctor_get(v_a_1099_, 1);
lean_inc(v_snd_1104_);
lean_dec(v_a_1099_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v_snd_1104_);
v___x_1106_ = v___x_1101_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_snd_1104_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
else
{
lean_object* v_val_1108_; lean_object* v___x_1110_; 
lean_inc_ref(v_fst_1103_);
lean_dec(v_a_1099_);
v_val_1108_ = lean_ctor_get(v_fst_1103_, 0);
lean_inc(v_val_1108_);
lean_dec_ref_known(v_fst_1103_, 1);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v_val_1108_);
v___x_1110_ = v___x_1101_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_val_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
v_a_1113_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1098_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1098_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
}
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
v_a_1122_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1084_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1084_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__12___boxed(lean_object* v_t_1130_, lean_object* v_init_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_PersistentArray_forIn___at___00main_spec__12(v_t_1130_, v_init_1131_, v___y_1132_, v___y_1133_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec_ref(v_t_1130_);
return v_res_1135_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0(uint8_t v___x_1143_, uint8_t v_suppressElabErrors_1144_, lean_object* v___x_1145_, lean_object* v_x_1146_){
_start:
{
if (lean_obj_tag(v_x_1146_) == 1)
{
lean_object* v_pre_1147_; 
v_pre_1147_ = lean_ctor_get(v_x_1146_, 0);
switch(lean_obj_tag(v_pre_1147_))
{
case 1:
{
lean_object* v_pre_1148_; 
v_pre_1148_ = lean_ctor_get(v_pre_1147_, 0);
switch(lean_obj_tag(v_pre_1148_))
{
case 0:
{
lean_object* v_str_1149_; lean_object* v_str_1150_; lean_object* v___x_1151_; uint8_t v___x_1152_; 
v_str_1149_ = lean_ctor_get(v_x_1146_, 1);
v_str_1150_ = lean_ctor_get(v_pre_1147_, 1);
v___x_1151_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0));
v___x_1152_ = lean_string_dec_eq(v_str_1150_, v___x_1151_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; uint8_t v___x_1154_; 
v___x_1153_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1));
v___x_1154_ = lean_string_dec_eq(v_str_1150_, v___x_1153_);
if (v___x_1154_ == 0)
{
return v___x_1143_;
}
else
{
lean_object* v___x_1155_; uint8_t v___x_1156_; 
v___x_1155_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2));
v___x_1156_ = lean_string_dec_eq(v_str_1149_, v___x_1155_);
if (v___x_1156_ == 0)
{
return v___x_1143_;
}
else
{
return v_suppressElabErrors_1144_;
}
}
}
else
{
lean_object* v___x_1157_; uint8_t v___x_1158_; 
v___x_1157_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3));
v___x_1158_ = lean_string_dec_eq(v_str_1149_, v___x_1157_);
if (v___x_1158_ == 0)
{
return v___x_1143_;
}
else
{
return v_suppressElabErrors_1144_;
}
}
}
case 1:
{
lean_object* v_pre_1159_; 
v_pre_1159_ = lean_ctor_get(v_pre_1148_, 0);
if (lean_obj_tag(v_pre_1159_) == 0)
{
lean_object* v_str_1160_; lean_object* v_str_1161_; lean_object* v_str_1162_; lean_object* v___x_1163_; uint8_t v___x_1164_; 
v_str_1160_ = lean_ctor_get(v_x_1146_, 1);
v_str_1161_ = lean_ctor_get(v_pre_1147_, 1);
v_str_1162_ = lean_ctor_get(v_pre_1148_, 1);
v___x_1163_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4));
v___x_1164_ = lean_string_dec_eq(v_str_1162_, v___x_1163_);
if (v___x_1164_ == 0)
{
return v___x_1143_;
}
else
{
lean_object* v___x_1165_; uint8_t v___x_1166_; 
v___x_1165_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5));
v___x_1166_ = lean_string_dec_eq(v_str_1161_, v___x_1165_);
if (v___x_1166_ == 0)
{
return v___x_1143_;
}
else
{
lean_object* v___x_1167_; uint8_t v___x_1168_; 
v___x_1167_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6));
v___x_1168_ = lean_string_dec_eq(v_str_1160_, v___x_1167_);
if (v___x_1168_ == 0)
{
return v___x_1143_;
}
else
{
return v_suppressElabErrors_1144_;
}
}
}
}
else
{
return v___x_1143_;
}
}
default: 
{
return v___x_1143_;
}
}
}
case 0:
{
lean_object* v_str_1169_; uint8_t v___x_1170_; 
v_str_1169_ = lean_ctor_get(v_x_1146_, 1);
v___x_1170_ = lean_string_dec_eq(v_str_1169_, v___x_1145_);
if (v___x_1170_ == 0)
{
return v___x_1143_;
}
else
{
return v_suppressElabErrors_1144_;
}
}
default: 
{
return v___x_1143_;
}
}
}
else
{
return v___x_1143_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___boxed(lean_object* v___x_1171_, lean_object* v_suppressElabErrors_1172_, lean_object* v___x_1173_, lean_object* v_x_1174_){
_start:
{
uint8_t v___x_36640__boxed_1175_; uint8_t v_suppressElabErrors_boxed_1176_; uint8_t v_res_1177_; lean_object* v_r_1178_; 
v___x_36640__boxed_1175_ = lean_unbox(v___x_1171_);
v_suppressElabErrors_boxed_1176_ = lean_unbox(v_suppressElabErrors_1172_);
v_res_1177_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0(v___x_36640__boxed_1175_, v_suppressElabErrors_boxed_1176_, v___x_1173_, v_x_1174_);
lean_dec(v_x_1174_);
lean_dec_ref(v___x_1173_);
v_r_1178_ = lean_box(v_res_1177_);
return v_r_1178_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0(void){
_start:
{
lean_object* v___x_1179_; double v___x_1180_; 
v___x_1179_ = lean_unsigned_to_nat(0u);
v___x_1180_ = lean_float_of_nat(v___x_1179_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(uint8_t v___x_1182_, lean_object* v_as_1183_, size_t v_sz_1184_, size_t v_i_1185_, lean_object* v_b_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v_a_1191_; uint8_t v___x_1195_; 
v___x_1195_ = lean_usize_dec_lt(v_i_1185_, v_sz_1184_);
if (v___x_1195_ == 0)
{
lean_object* v___x_1196_; 
v___x_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1196_, 0, v_b_1186_);
return v___x_1196_;
}
else
{
lean_object* v_a_1197_; lean_object* v_fst_1198_; lean_object* v_snd_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1275_; 
v_a_1197_ = lean_array_uget(v_as_1183_, v_i_1185_);
v_fst_1198_ = lean_ctor_get(v_a_1197_, 0);
v_snd_1199_ = lean_ctor_get(v_a_1197_, 1);
v_isSharedCheck_1275_ = !lean_is_exclusive(v_a_1197_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1201_ = v_a_1197_;
v_isShared_1202_ = v_isSharedCheck_1275_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_snd_1199_);
lean_inc(v_fst_1198_);
lean_dec(v_a_1197_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1275_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v_fst_1203_; lean_object* v_snd_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1274_; 
v_fst_1203_ = lean_ctor_get(v_fst_1198_, 0);
v_snd_1204_ = lean_ctor_get(v_fst_1198_, 1);
v_isSharedCheck_1274_ = !lean_is_exclusive(v_fst_1198_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1206_ = v_fst_1198_;
v_isShared_1207_ = v_isSharedCheck_1274_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_snd_1204_);
lean_inc(v_fst_1203_);
lean_dec(v_fst_1198_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1274_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; double v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v_fileName_1213_; lean_object* v_fileMap_1214_; uint8_t v_suppressElabErrors_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1222_; 
v___x_1208_ = lean_box(0);
v___x_1209_ = lean_box(0);
v___x_1210_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0);
v___x_1211_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1));
v___x_1212_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1212_, 0, v___x_1208_);
lean_ctor_set(v___x_1212_, 1, v___x_1209_);
lean_ctor_set(v___x_1212_, 2, v___x_1211_);
lean_ctor_set_float(v___x_1212_, sizeof(void*)*3, v___x_1210_);
lean_ctor_set_float(v___x_1212_, sizeof(void*)*3 + 8, v___x_1210_);
lean_ctor_set_uint8(v___x_1212_, sizeof(void*)*3 + 16, v___x_1195_);
v_fileName_1213_ = lean_ctor_get(v___y_1187_, 0);
v_fileMap_1214_ = lean_ctor_get(v___y_1187_, 1);
v_suppressElabErrors_1215_ = lean_ctor_get_uint8(v___y_1187_, sizeof(void*)*14 + 1);
v___x_1216_ = lean_box(0);
v___x_1217_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_1218_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_1219_ = l_Lean_MessageData_nil;
v___x_1220_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1212_);
lean_ctor_set(v___x_1220_, 1, v___x_1219_);
lean_ctor_set(v___x_1220_, 2, v_snd_1199_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set_tag(v___x_1206_, 8);
lean_ctor_set(v___x_1206_, 1, v___x_1220_);
lean_ctor_set(v___x_1206_, 0, v___x_1218_);
v___x_1222_ = v___x_1206_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1218_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v___x_1220_);
v___x_1222_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
uint8_t v___x_1223_; lean_object* v___x_1224_; lean_object* v___y_1226_; lean_object* v___y_1227_; 
v___x_1223_ = 0;
lean_inc_ref(v_fileMap_1214_);
lean_inc_ref(v_fileName_1213_);
v___x_1224_ = l_Lean_Elab_mkMessageCore(v_fileName_1213_, v_fileMap_1214_, v___x_1222_, v___x_1223_, v_fst_1203_, v_snd_1204_);
lean_dec(v_snd_1204_);
lean_dec(v_fst_1203_);
if (v_suppressElabErrors_1215_ == 0)
{
v___y_1226_ = v___y_1187_;
v___y_1227_ = v___y_1188_;
goto v___jp_1225_;
}
else
{
lean_object* v_data_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___f_1271_; uint8_t v___x_1272_; 
v_data_1268_ = lean_ctor_get(v___x_1224_, 4);
lean_inc(v_data_1268_);
v___x_1269_ = lean_box(v___x_1182_);
v___x_1270_ = lean_box(v_suppressElabErrors_1215_);
v___f_1271_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1271_, 0, v___x_1269_);
lean_closure_set(v___f_1271_, 1, v___x_1270_);
lean_closure_set(v___f_1271_, 2, v___x_1217_);
v___x_1272_ = l_Lean_MessageData_hasTag(v___f_1271_, v_data_1268_);
if (v___x_1272_ == 0)
{
lean_dec_ref(v___x_1224_);
lean_del_object(v___x_1201_);
v_a_1191_ = v___x_1216_;
goto v___jp_1190_;
}
else
{
v___y_1226_ = v___y_1187_;
v___y_1227_ = v___y_1188_;
goto v___jp_1225_;
}
}
v___jp_1225_:
{
lean_object* v___x_1228_; lean_object* v_fileName_1229_; lean_object* v_pos_1230_; lean_object* v_endPos_1231_; uint8_t v_keepFullRange_1232_; uint8_t v_severity_1233_; uint8_t v_isSilent_1234_; lean_object* v_caption_1235_; lean_object* v_data_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1267_; 
v___x_1228_ = lean_st_ref_take(v___y_1227_);
v_fileName_1229_ = lean_ctor_get(v___x_1224_, 0);
v_pos_1230_ = lean_ctor_get(v___x_1224_, 1);
v_endPos_1231_ = lean_ctor_get(v___x_1224_, 2);
v_keepFullRange_1232_ = lean_ctor_get_uint8(v___x_1224_, sizeof(void*)*5);
v_severity_1233_ = lean_ctor_get_uint8(v___x_1224_, sizeof(void*)*5 + 1);
v_isSilent_1234_ = lean_ctor_get_uint8(v___x_1224_, sizeof(void*)*5 + 2);
v_caption_1235_ = lean_ctor_get(v___x_1224_, 3);
v_data_1236_ = lean_ctor_get(v___x_1224_, 4);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1238_ = v___x_1224_;
v_isShared_1239_ = v_isSharedCheck_1267_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_data_1236_);
lean_inc(v_caption_1235_);
lean_inc(v_endPos_1231_);
lean_inc(v_pos_1230_);
lean_inc(v_fileName_1229_);
lean_dec(v___x_1224_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1267_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v_currNamespace_1240_; lean_object* v_openDecls_1241_; lean_object* v_env_1242_; lean_object* v_nextMacroScope_1243_; lean_object* v_ngen_1244_; lean_object* v_auxDeclNGen_1245_; lean_object* v_traceState_1246_; lean_object* v_cache_1247_; lean_object* v_messages_1248_; lean_object* v_infoState_1249_; lean_object* v_snapshotTasks_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1266_; 
v_currNamespace_1240_ = lean_ctor_get(v___y_1226_, 6);
v_openDecls_1241_ = lean_ctor_get(v___y_1226_, 7);
v_env_1242_ = lean_ctor_get(v___x_1228_, 0);
v_nextMacroScope_1243_ = lean_ctor_get(v___x_1228_, 1);
v_ngen_1244_ = lean_ctor_get(v___x_1228_, 2);
v_auxDeclNGen_1245_ = lean_ctor_get(v___x_1228_, 3);
v_traceState_1246_ = lean_ctor_get(v___x_1228_, 4);
v_cache_1247_ = lean_ctor_get(v___x_1228_, 5);
v_messages_1248_ = lean_ctor_get(v___x_1228_, 6);
v_infoState_1249_ = lean_ctor_get(v___x_1228_, 7);
v_snapshotTasks_1250_ = lean_ctor_get(v___x_1228_, 8);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1252_ = v___x_1228_;
v_isShared_1253_ = v_isSharedCheck_1266_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_snapshotTasks_1250_);
lean_inc(v_infoState_1249_);
lean_inc(v_messages_1248_);
lean_inc(v_cache_1247_);
lean_inc(v_traceState_1246_);
lean_inc(v_auxDeclNGen_1245_);
lean_inc(v_ngen_1244_);
lean_inc(v_nextMacroScope_1243_);
lean_inc(v_env_1242_);
lean_dec(v___x_1228_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1266_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
lean_inc(v_openDecls_1241_);
lean_inc(v_currNamespace_1240_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 1, v_openDecls_1241_);
lean_ctor_set(v___x_1201_, 0, v_currNamespace_1240_);
v___x_1255_ = v___x_1201_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_currNamespace_1240_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v_openDecls_1241_);
v___x_1255_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
lean_object* v___x_1256_; lean_object* v___x_1258_; 
v___x_1256_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
lean_ctor_set(v___x_1256_, 1, v_data_1236_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 4, v___x_1256_);
v___x_1258_ = v___x_1238_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_fileName_1229_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v_pos_1230_);
lean_ctor_set(v_reuseFailAlloc_1264_, 2, v_endPos_1231_);
lean_ctor_set(v_reuseFailAlloc_1264_, 3, v_caption_1235_);
lean_ctor_set(v_reuseFailAlloc_1264_, 4, v___x_1256_);
lean_ctor_set_uint8(v_reuseFailAlloc_1264_, sizeof(void*)*5, v_keepFullRange_1232_);
lean_ctor_set_uint8(v_reuseFailAlloc_1264_, sizeof(void*)*5 + 1, v_severity_1233_);
lean_ctor_set_uint8(v_reuseFailAlloc_1264_, sizeof(void*)*5 + 2, v_isSilent_1234_);
v___x_1258_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
lean_object* v___x_1259_; lean_object* v___x_1261_; 
v___x_1259_ = l_Lean_MessageLog_add(v___x_1258_, v_messages_1248_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 6, v___x_1259_);
v___x_1261_ = v___x_1252_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_env_1242_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v_nextMacroScope_1243_);
lean_ctor_set(v_reuseFailAlloc_1263_, 2, v_ngen_1244_);
lean_ctor_set(v_reuseFailAlloc_1263_, 3, v_auxDeclNGen_1245_);
lean_ctor_set(v_reuseFailAlloc_1263_, 4, v_traceState_1246_);
lean_ctor_set(v_reuseFailAlloc_1263_, 5, v_cache_1247_);
lean_ctor_set(v_reuseFailAlloc_1263_, 6, v___x_1259_);
lean_ctor_set(v_reuseFailAlloc_1263_, 7, v_infoState_1249_);
lean_ctor_set(v_reuseFailAlloc_1263_, 8, v_snapshotTasks_1250_);
v___x_1261_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
lean_object* v___x_1262_; 
v___x_1262_ = lean_st_ref_set(v___y_1227_, v___x_1261_);
v_a_1191_ = v___x_1216_;
goto v___jp_1190_;
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
v___jp_1190_:
{
size_t v___x_1192_; size_t v___x_1193_; 
v___x_1192_ = ((size_t)1ULL);
v___x_1193_ = lean_usize_add(v_i_1185_, v___x_1192_);
v_i_1185_ = v___x_1193_;
v_b_1186_ = v_a_1191_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___boxed(lean_object* v___x_1276_, lean_object* v_as_1277_, lean_object* v_sz_1278_, lean_object* v_i_1279_, lean_object* v_b_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
uint8_t v___x_36713__boxed_1284_; size_t v_sz_boxed_1285_; size_t v_i_boxed_1286_; lean_object* v_res_1287_; 
v___x_36713__boxed_1284_ = lean_unbox(v___x_1276_);
v_sz_boxed_1285_ = lean_unbox_usize(v_sz_1278_);
lean_dec(v_sz_1278_);
v_i_boxed_1286_ = lean_unbox_usize(v_i_1279_);
lean_dec(v_i_1279_);
v_res_1287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(v___x_36713__boxed_1284_, v_as_1277_, v_sz_boxed_1285_, v_i_boxed_1286_, v_b_1280_, v___y_1281_, v___y_1282_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec_ref(v_as_1277_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(lean_object* v_opts_1288_, lean_object* v_opt_1289_){
_start:
{
lean_object* v_name_1290_; lean_object* v_map_1291_; lean_object* v___x_1292_; 
v_name_1290_ = lean_ctor_get(v_opt_1289_, 0);
v_map_1291_ = lean_ctor_get(v_opts_1288_, 0);
v___x_1292_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1291_, v_name_1290_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v___x_1293_; 
v___x_1293_ = lean_box(0);
return v___x_1293_;
}
else
{
lean_object* v_val_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1303_; 
v_val_1294_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1296_ = v___x_1292_;
v_isShared_1297_ = v_isSharedCheck_1303_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_val_1294_);
lean_dec(v___x_1292_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1303_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
if (lean_obj_tag(v_val_1294_) == 0)
{
lean_object* v_v_1298_; lean_object* v___x_1300_; 
v_v_1298_ = lean_ctor_get(v_val_1294_, 0);
lean_inc_ref(v_v_1298_);
lean_dec_ref_known(v_val_1294_, 1);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 0, v_v_1298_);
v___x_1300_ = v___x_1296_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_v_1298_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
else
{
lean_object* v___x_1302_; 
lean_del_object(v___x_1296_);
lean_dec(v_val_1294_);
v___x_1302_ = lean_box(0);
return v___x_1302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15___boxed(lean_object* v_opts_1304_, lean_object* v_opt_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(v_opts_1304_, v_opt_1305_);
lean_dec_ref(v_opt_1305_);
lean_dec_ref(v_opts_1304_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(lean_object* v_a_1307_, lean_object* v_fallback_1308_, lean_object* v_x_1309_){
_start:
{
if (lean_obj_tag(v_x_1309_) == 0)
{
lean_inc(v_fallback_1308_);
return v_fallback_1308_;
}
else
{
lean_object* v_key_1310_; lean_object* v_value_1311_; lean_object* v_tail_1312_; uint8_t v___y_1314_; lean_object* v_fst_1316_; lean_object* v_snd_1317_; lean_object* v_fst_1318_; lean_object* v_snd_1319_; uint8_t v___x_1320_; 
v_key_1310_ = lean_ctor_get(v_x_1309_, 0);
v_value_1311_ = lean_ctor_get(v_x_1309_, 1);
v_tail_1312_ = lean_ctor_get(v_x_1309_, 2);
v_fst_1316_ = lean_ctor_get(v_key_1310_, 0);
v_snd_1317_ = lean_ctor_get(v_key_1310_, 1);
v_fst_1318_ = lean_ctor_get(v_a_1307_, 0);
v_snd_1319_ = lean_ctor_get(v_a_1307_, 1);
v___x_1320_ = lean_nat_dec_eq(v_fst_1316_, v_fst_1318_);
if (v___x_1320_ == 0)
{
v___y_1314_ = v___x_1320_;
goto v___jp_1313_;
}
else
{
uint8_t v___x_1321_; 
v___x_1321_ = lean_nat_dec_eq(v_snd_1317_, v_snd_1319_);
v___y_1314_ = v___x_1321_;
goto v___jp_1313_;
}
v___jp_1313_:
{
if (v___y_1314_ == 0)
{
v_x_1309_ = v_tail_1312_;
goto _start;
}
else
{
lean_inc(v_value_1311_);
return v_value_1311_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg___boxed(lean_object* v_a_1322_, lean_object* v_fallback_1323_, lean_object* v_x_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_1322_, v_fallback_1323_, v_x_1324_);
lean_dec(v_x_1324_);
lean_dec(v_fallback_1323_);
lean_dec_ref(v_a_1322_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(lean_object* v_m_1326_, lean_object* v_a_1327_, lean_object* v_fallback_1328_){
_start:
{
lean_object* v_buckets_1329_; lean_object* v_fst_1330_; lean_object* v_snd_1331_; lean_object* v___x_1332_; uint64_t v___x_1333_; uint64_t v___x_1334_; uint64_t v___x_1335_; uint64_t v___x_1336_; uint64_t v___x_1337_; uint64_t v_fold_1338_; uint64_t v___x_1339_; uint64_t v___x_1340_; uint64_t v___x_1341_; size_t v___x_1342_; size_t v___x_1343_; size_t v___x_1344_; size_t v___x_1345_; size_t v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v_buckets_1329_ = lean_ctor_get(v_m_1326_, 1);
v_fst_1330_ = lean_ctor_get(v_a_1327_, 0);
v_snd_1331_ = lean_ctor_get(v_a_1327_, 1);
v___x_1332_ = lean_array_get_size(v_buckets_1329_);
v___x_1333_ = l_String_instHashableRaw_hash(v_fst_1330_);
v___x_1334_ = l_String_instHashableRaw_hash(v_snd_1331_);
v___x_1335_ = lean_uint64_mix_hash(v___x_1333_, v___x_1334_);
v___x_1336_ = 32ULL;
v___x_1337_ = lean_uint64_shift_right(v___x_1335_, v___x_1336_);
v_fold_1338_ = lean_uint64_xor(v___x_1335_, v___x_1337_);
v___x_1339_ = 16ULL;
v___x_1340_ = lean_uint64_shift_right(v_fold_1338_, v___x_1339_);
v___x_1341_ = lean_uint64_xor(v_fold_1338_, v___x_1340_);
v___x_1342_ = lean_uint64_to_usize(v___x_1341_);
v___x_1343_ = lean_usize_of_nat(v___x_1332_);
v___x_1344_ = ((size_t)1ULL);
v___x_1345_ = lean_usize_sub(v___x_1343_, v___x_1344_);
v___x_1346_ = lean_usize_land(v___x_1342_, v___x_1345_);
v___x_1347_ = lean_array_uget_borrowed(v_buckets_1329_, v___x_1346_);
v___x_1348_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_1327_, v_fallback_1328_, v___x_1347_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg___boxed(lean_object* v_m_1349_, lean_object* v_a_1350_, lean_object* v_fallback_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_m_1349_, v_a_1350_, v_fallback_1351_);
lean_dec(v_fallback_1351_);
lean_dec_ref(v_a_1350_);
lean_dec_ref(v_m_1349_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(lean_object* v_x_1353_, lean_object* v_x_1354_){
_start:
{
if (lean_obj_tag(v_x_1354_) == 0)
{
return v_x_1353_;
}
else
{
lean_object* v_key_1355_; lean_object* v_value_1356_; lean_object* v_tail_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1384_; 
v_key_1355_ = lean_ctor_get(v_x_1354_, 0);
v_value_1356_ = lean_ctor_get(v_x_1354_, 1);
v_tail_1357_ = lean_ctor_get(v_x_1354_, 2);
v_isSharedCheck_1384_ = !lean_is_exclusive(v_x_1354_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1359_ = v_x_1354_;
v_isShared_1360_ = v_isSharedCheck_1384_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_tail_1357_);
lean_inc(v_value_1356_);
lean_inc(v_key_1355_);
lean_dec(v_x_1354_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1384_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v_fst_1361_; lean_object* v_snd_1362_; lean_object* v___x_1363_; uint64_t v___x_1364_; uint64_t v___x_1365_; uint64_t v___x_1366_; uint64_t v___x_1367_; uint64_t v___x_1368_; uint64_t v_fold_1369_; uint64_t v___x_1370_; uint64_t v___x_1371_; uint64_t v___x_1372_; size_t v___x_1373_; size_t v___x_1374_; size_t v___x_1375_; size_t v___x_1376_; size_t v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1380_; 
v_fst_1361_ = lean_ctor_get(v_key_1355_, 0);
v_snd_1362_ = lean_ctor_get(v_key_1355_, 1);
v___x_1363_ = lean_array_get_size(v_x_1353_);
v___x_1364_ = l_String_instHashableRaw_hash(v_fst_1361_);
v___x_1365_ = l_String_instHashableRaw_hash(v_snd_1362_);
v___x_1366_ = lean_uint64_mix_hash(v___x_1364_, v___x_1365_);
v___x_1367_ = 32ULL;
v___x_1368_ = lean_uint64_shift_right(v___x_1366_, v___x_1367_);
v_fold_1369_ = lean_uint64_xor(v___x_1366_, v___x_1368_);
v___x_1370_ = 16ULL;
v___x_1371_ = lean_uint64_shift_right(v_fold_1369_, v___x_1370_);
v___x_1372_ = lean_uint64_xor(v_fold_1369_, v___x_1371_);
v___x_1373_ = lean_uint64_to_usize(v___x_1372_);
v___x_1374_ = lean_usize_of_nat(v___x_1363_);
v___x_1375_ = ((size_t)1ULL);
v___x_1376_ = lean_usize_sub(v___x_1374_, v___x_1375_);
v___x_1377_ = lean_usize_land(v___x_1373_, v___x_1376_);
v___x_1378_ = lean_array_uget_borrowed(v_x_1353_, v___x_1377_);
lean_inc(v___x_1378_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 2, v___x_1378_);
v___x_1380_ = v___x_1359_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_key_1355_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v_value_1356_);
lean_ctor_set(v_reuseFailAlloc_1383_, 2, v___x_1378_);
v___x_1380_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
lean_object* v___x_1381_; 
v___x_1381_ = lean_array_uset(v_x_1353_, v___x_1377_, v___x_1380_);
v_x_1353_ = v___x_1381_;
v_x_1354_ = v_tail_1357_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(lean_object* v_i_1385_, lean_object* v_source_1386_, lean_object* v_target_1387_){
_start:
{
lean_object* v___x_1388_; uint8_t v___x_1389_; 
v___x_1388_ = lean_array_get_size(v_source_1386_);
v___x_1389_ = lean_nat_dec_lt(v_i_1385_, v___x_1388_);
if (v___x_1389_ == 0)
{
lean_dec_ref(v_source_1386_);
lean_dec(v_i_1385_);
return v_target_1387_;
}
else
{
lean_object* v_es_1390_; lean_object* v___x_1391_; lean_object* v_source_1392_; lean_object* v_target_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v_es_1390_ = lean_array_fget(v_source_1386_, v_i_1385_);
v___x_1391_ = lean_box(0);
v_source_1392_ = lean_array_fset(v_source_1386_, v_i_1385_, v___x_1391_);
v_target_1393_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(v_target_1387_, v_es_1390_);
v___x_1394_ = lean_unsigned_to_nat(1u);
v___x_1395_ = lean_nat_add(v_i_1385_, v___x_1394_);
lean_dec(v_i_1385_);
v_i_1385_ = v___x_1395_;
v_source_1386_ = v_source_1392_;
v_target_1387_ = v_target_1393_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(lean_object* v_data_1397_){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v_nbuckets_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1398_ = lean_array_get_size(v_data_1397_);
v___x_1399_ = lean_unsigned_to_nat(2u);
v_nbuckets_1400_ = lean_nat_mul(v___x_1398_, v___x_1399_);
v___x_1401_ = lean_unsigned_to_nat(0u);
v___x_1402_ = lean_box(0);
v___x_1403_ = lean_mk_array(v_nbuckets_1400_, v___x_1402_);
v___x_1404_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(v___x_1401_, v_data_1397_, v___x_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(lean_object* v_a_1405_, lean_object* v_b_1406_, lean_object* v_x_1407_){
_start:
{
if (lean_obj_tag(v_x_1407_) == 0)
{
lean_dec(v_b_1406_);
lean_dec_ref(v_a_1405_);
return v_x_1407_;
}
else
{
lean_object* v_key_1408_; lean_object* v_value_1409_; lean_object* v_tail_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1429_; 
v_key_1408_ = lean_ctor_get(v_x_1407_, 0);
v_value_1409_ = lean_ctor_get(v_x_1407_, 1);
v_tail_1410_ = lean_ctor_get(v_x_1407_, 2);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_x_1407_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1412_ = v_x_1407_;
v_isShared_1413_ = v_isSharedCheck_1429_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_tail_1410_);
lean_inc(v_value_1409_);
lean_inc(v_key_1408_);
lean_dec(v_x_1407_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1429_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
uint8_t v___y_1415_; lean_object* v_fst_1423_; lean_object* v_snd_1424_; lean_object* v_fst_1425_; lean_object* v_snd_1426_; uint8_t v___x_1427_; 
v_fst_1423_ = lean_ctor_get(v_key_1408_, 0);
v_snd_1424_ = lean_ctor_get(v_key_1408_, 1);
v_fst_1425_ = lean_ctor_get(v_a_1405_, 0);
v_snd_1426_ = lean_ctor_get(v_a_1405_, 1);
v___x_1427_ = lean_nat_dec_eq(v_fst_1423_, v_fst_1425_);
if (v___x_1427_ == 0)
{
v___y_1415_ = v___x_1427_;
goto v___jp_1414_;
}
else
{
uint8_t v___x_1428_; 
v___x_1428_ = lean_nat_dec_eq(v_snd_1424_, v_snd_1426_);
v___y_1415_ = v___x_1428_;
goto v___jp_1414_;
}
v___jp_1414_:
{
if (v___y_1415_ == 0)
{
lean_object* v___x_1416_; lean_object* v___x_1418_; 
v___x_1416_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_1405_, v_b_1406_, v_tail_1410_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 2, v___x_1416_);
v___x_1418_ = v___x_1412_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_key_1408_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v_value_1409_);
lean_ctor_set(v_reuseFailAlloc_1419_, 2, v___x_1416_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
else
{
lean_object* v___x_1421_; 
lean_dec(v_value_1409_);
lean_dec(v_key_1408_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 1, v_b_1406_);
lean_ctor_set(v___x_1412_, 0, v_a_1405_);
v___x_1421_ = v___x_1412_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_a_1405_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_b_1406_);
lean_ctor_set(v_reuseFailAlloc_1422_, 2, v_tail_1410_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(lean_object* v_a_1430_, lean_object* v_x_1431_){
_start:
{
if (lean_obj_tag(v_x_1431_) == 0)
{
uint8_t v___x_1432_; 
v___x_1432_ = 0;
return v___x_1432_;
}
else
{
lean_object* v_key_1433_; lean_object* v_tail_1434_; uint8_t v___y_1436_; lean_object* v_fst_1438_; lean_object* v_snd_1439_; lean_object* v_fst_1440_; lean_object* v_snd_1441_; uint8_t v___x_1442_; 
v_key_1433_ = lean_ctor_get(v_x_1431_, 0);
v_tail_1434_ = lean_ctor_get(v_x_1431_, 2);
v_fst_1438_ = lean_ctor_get(v_key_1433_, 0);
v_snd_1439_ = lean_ctor_get(v_key_1433_, 1);
v_fst_1440_ = lean_ctor_get(v_a_1430_, 0);
v_snd_1441_ = lean_ctor_get(v_a_1430_, 1);
v___x_1442_ = lean_nat_dec_eq(v_fst_1438_, v_fst_1440_);
if (v___x_1442_ == 0)
{
v___y_1436_ = v___x_1442_;
goto v___jp_1435_;
}
else
{
uint8_t v___x_1443_; 
v___x_1443_ = lean_nat_dec_eq(v_snd_1439_, v_snd_1441_);
v___y_1436_ = v___x_1443_;
goto v___jp_1435_;
}
v___jp_1435_:
{
if (v___y_1436_ == 0)
{
v_x_1431_ = v_tail_1434_;
goto _start;
}
else
{
return v___y_1436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg___boxed(lean_object* v_a_1444_, lean_object* v_x_1445_){
_start:
{
uint8_t v_res_1446_; lean_object* v_r_1447_; 
v_res_1446_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_1444_, v_x_1445_);
lean_dec(v_x_1445_);
lean_dec_ref(v_a_1444_);
v_r_1447_ = lean_box(v_res_1446_);
return v_r_1447_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(lean_object* v_m_1448_, lean_object* v_a_1449_, lean_object* v_b_1450_){
_start:
{
lean_object* v_size_1451_; lean_object* v_buckets_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1499_; 
v_size_1451_ = lean_ctor_get(v_m_1448_, 0);
v_buckets_1452_ = lean_ctor_get(v_m_1448_, 1);
v_isSharedCheck_1499_ = !lean_is_exclusive(v_m_1448_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1454_ = v_m_1448_;
v_isShared_1455_ = v_isSharedCheck_1499_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_buckets_1452_);
lean_inc(v_size_1451_);
lean_dec(v_m_1448_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1499_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v_fst_1456_; lean_object* v_snd_1457_; lean_object* v___x_1458_; uint64_t v___x_1459_; uint64_t v___x_1460_; uint64_t v___x_1461_; uint64_t v___x_1462_; uint64_t v___x_1463_; uint64_t v_fold_1464_; uint64_t v___x_1465_; uint64_t v___x_1466_; uint64_t v___x_1467_; size_t v___x_1468_; size_t v___x_1469_; size_t v___x_1470_; size_t v___x_1471_; size_t v___x_1472_; lean_object* v_bkt_1473_; uint8_t v___x_1474_; 
v_fst_1456_ = lean_ctor_get(v_a_1449_, 0);
v_snd_1457_ = lean_ctor_get(v_a_1449_, 1);
v___x_1458_ = lean_array_get_size(v_buckets_1452_);
v___x_1459_ = l_String_instHashableRaw_hash(v_fst_1456_);
v___x_1460_ = l_String_instHashableRaw_hash(v_snd_1457_);
v___x_1461_ = lean_uint64_mix_hash(v___x_1459_, v___x_1460_);
v___x_1462_ = 32ULL;
v___x_1463_ = lean_uint64_shift_right(v___x_1461_, v___x_1462_);
v_fold_1464_ = lean_uint64_xor(v___x_1461_, v___x_1463_);
v___x_1465_ = 16ULL;
v___x_1466_ = lean_uint64_shift_right(v_fold_1464_, v___x_1465_);
v___x_1467_ = lean_uint64_xor(v_fold_1464_, v___x_1466_);
v___x_1468_ = lean_uint64_to_usize(v___x_1467_);
v___x_1469_ = lean_usize_of_nat(v___x_1458_);
v___x_1470_ = ((size_t)1ULL);
v___x_1471_ = lean_usize_sub(v___x_1469_, v___x_1470_);
v___x_1472_ = lean_usize_land(v___x_1468_, v___x_1471_);
v_bkt_1473_ = lean_array_uget_borrowed(v_buckets_1452_, v___x_1472_);
v___x_1474_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_1449_, v_bkt_1473_);
if (v___x_1474_ == 0)
{
lean_object* v___x_1475_; lean_object* v_size_x27_1476_; lean_object* v___x_1477_; lean_object* v_buckets_x27_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; uint8_t v___x_1484_; 
v___x_1475_ = lean_unsigned_to_nat(1u);
v_size_x27_1476_ = lean_nat_add(v_size_1451_, v___x_1475_);
lean_dec(v_size_1451_);
lean_inc(v_bkt_1473_);
v___x_1477_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1477_, 0, v_a_1449_);
lean_ctor_set(v___x_1477_, 1, v_b_1450_);
lean_ctor_set(v___x_1477_, 2, v_bkt_1473_);
v_buckets_x27_1478_ = lean_array_uset(v_buckets_1452_, v___x_1472_, v___x_1477_);
v___x_1479_ = lean_unsigned_to_nat(4u);
v___x_1480_ = lean_nat_mul(v_size_x27_1476_, v___x_1479_);
v___x_1481_ = lean_unsigned_to_nat(3u);
v___x_1482_ = lean_nat_div(v___x_1480_, v___x_1481_);
lean_dec(v___x_1480_);
v___x_1483_ = lean_array_get_size(v_buckets_x27_1478_);
v___x_1484_ = lean_nat_dec_le(v___x_1482_, v___x_1483_);
lean_dec(v___x_1482_);
if (v___x_1484_ == 0)
{
lean_object* v_val_1485_; lean_object* v___x_1487_; 
v_val_1485_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(v_buckets_x27_1478_);
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 1, v_val_1485_);
lean_ctor_set(v___x_1454_, 0, v_size_x27_1476_);
v___x_1487_ = v___x_1454_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_size_x27_1476_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_val_1485_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
else
{
lean_object* v___x_1490_; 
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 1, v_buckets_x27_1478_);
lean_ctor_set(v___x_1454_, 0, v_size_x27_1476_);
v___x_1490_ = v___x_1454_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_size_x27_1476_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v_buckets_x27_1478_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
else
{
lean_object* v___x_1492_; lean_object* v_buckets_x27_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1497_; 
lean_inc(v_bkt_1473_);
v___x_1492_ = lean_box(0);
v_buckets_x27_1493_ = lean_array_uset(v_buckets_1452_, v___x_1472_, v___x_1492_);
v___x_1494_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_1449_, v_b_1450_, v_bkt_1473_);
v___x_1495_ = lean_array_uset(v_buckets_x27_1493_, v___x_1472_, v___x_1494_);
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 1, v___x_1495_);
v___x_1497_ = v___x_1454_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_size_1451_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v___x_1495_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(uint8_t v___x_1502_, lean_object* v_as_1503_, size_t v_sz_1504_, size_t v_i_1505_, lean_object* v_b_1506_, lean_object* v___y_1507_){
_start:
{
uint8_t v___x_1509_; 
v___x_1509_ = lean_usize_dec_lt(v_i_1505_, v_sz_1504_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1510_; 
v___x_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1510_, 0, v_b_1506_);
return v___x_1510_;
}
else
{
lean_object* v_snd_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1548_; 
v_snd_1511_ = lean_ctor_get(v_b_1506_, 1);
v_isSharedCheck_1548_ = !lean_is_exclusive(v_b_1506_);
if (v_isSharedCheck_1548_ == 0)
{
lean_object* v_unused_1549_; 
v_unused_1549_ = lean_ctor_get(v_b_1506_, 0);
lean_dec(v_unused_1549_);
v___x_1513_ = v_b_1506_;
v_isShared_1514_ = v_isSharedCheck_1548_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_snd_1511_);
lean_dec(v_b_1506_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1548_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v_ref_1515_; lean_object* v_a_1516_; lean_object* v_ref_1517_; lean_object* v_msg_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1547_; 
v_ref_1515_ = lean_ctor_get(v___y_1507_, 5);
v_a_1516_ = lean_array_uget(v_as_1503_, v_i_1505_);
v_ref_1517_ = lean_ctor_get(v_a_1516_, 0);
v_msg_1518_ = lean_ctor_get(v_a_1516_, 1);
v_isSharedCheck_1547_ = !lean_is_exclusive(v_a_1516_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1520_ = v_a_1516_;
v_isShared_1521_ = v_isSharedCheck_1547_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_msg_1518_);
lean_inc(v_ref_1517_);
lean_dec(v_a_1516_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1547_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1522_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v_ref_1539_; lean_object* v___y_1541_; lean_object* v___x_1544_; 
v___x_1522_ = lean_box(0);
v_ref_1539_ = l_Lean_replaceRef(v_ref_1517_, v_ref_1515_);
lean_dec(v_ref_1517_);
v___x_1544_ = l_Lean_Syntax_getPos_x3f(v_ref_1539_, v___x_1502_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v___x_1545_; 
v___x_1545_ = lean_unsigned_to_nat(0u);
v___y_1541_ = v___x_1545_;
goto v___jp_1540_;
}
else
{
lean_object* v_val_1546_; 
v_val_1546_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_val_1546_);
lean_dec_ref_known(v___x_1544_, 1);
v___y_1541_ = v_val_1546_;
goto v___jp_1540_;
}
v___jp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 1, v___y_1525_);
lean_ctor_set(v___x_1513_, 0, v___y_1524_);
v___x_1527_ = v___x_1513_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___y_1524_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v___y_1525_);
v___x_1527_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v_pos2traces_1531_; lean_object* v___x_1533_; 
v___x_1528_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1529_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1511_, v___x_1527_, v___x_1528_);
v___x_1530_ = lean_array_push(v___x_1529_, v_msg_1518_);
v_pos2traces_1531_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1511_, v___x_1527_, v___x_1530_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 1, v_pos2traces_1531_);
lean_ctor_set(v___x_1520_, 0, v___x_1522_);
v___x_1533_ = v___x_1520_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1522_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_pos2traces_1531_);
v___x_1533_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
size_t v___x_1534_; size_t v___x_1535_; 
v___x_1534_ = ((size_t)1ULL);
v___x_1535_ = lean_usize_add(v_i_1505_, v___x_1534_);
v_i_1505_ = v___x_1535_;
v_b_1506_ = v___x_1533_;
goto _start;
}
}
}
v___jp_1540_:
{
lean_object* v___x_1542_; 
v___x_1542_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1539_, v___x_1502_);
lean_dec(v_ref_1539_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_inc(v___y_1541_);
v___y_1524_ = v___y_1541_;
v___y_1525_ = v___y_1541_;
goto v___jp_1523_;
}
else
{
lean_object* v_val_1543_; 
v_val_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_val_1543_);
lean_dec_ref_known(v___x_1542_, 1);
v___y_1524_ = v___y_1541_;
v___y_1525_ = v_val_1543_;
goto v___jp_1523_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___boxed(lean_object* v___x_1550_, lean_object* v_as_1551_, lean_object* v_sz_1552_, lean_object* v_i_1553_, lean_object* v_b_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
uint8_t v___x_37193__boxed_1557_; size_t v_sz_boxed_1558_; size_t v_i_boxed_1559_; lean_object* v_res_1560_; 
v___x_37193__boxed_1557_ = lean_unbox(v___x_1550_);
v_sz_boxed_1558_ = lean_unbox_usize(v_sz_1552_);
lean_dec(v_sz_1552_);
v_i_boxed_1559_ = lean_unbox_usize(v_i_1553_);
lean_dec(v_i_1553_);
v_res_1560_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_37193__boxed_1557_, v_as_1551_, v_sz_boxed_1558_, v_i_boxed_1559_, v_b_1554_, v___y_1555_);
lean_dec_ref(v___y_1555_);
lean_dec_ref(v_as_1551_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(uint8_t v___x_1561_, lean_object* v_as_1562_, size_t v_sz_1563_, size_t v_i_1564_, lean_object* v_b_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
uint8_t v___x_1569_; 
v___x_1569_ = lean_usize_dec_lt(v_i_1564_, v_sz_1563_);
if (v___x_1569_ == 0)
{
lean_object* v___x_1570_; 
v___x_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1570_, 0, v_b_1565_);
return v___x_1570_;
}
else
{
lean_object* v_snd_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1608_; 
v_snd_1571_ = lean_ctor_get(v_b_1565_, 1);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_b_1565_);
if (v_isSharedCheck_1608_ == 0)
{
lean_object* v_unused_1609_; 
v_unused_1609_ = lean_ctor_get(v_b_1565_, 0);
lean_dec(v_unused_1609_);
v___x_1573_ = v_b_1565_;
v_isShared_1574_ = v_isSharedCheck_1608_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_snd_1571_);
lean_dec(v_b_1565_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1608_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v_ref_1575_; lean_object* v_a_1576_; lean_object* v_ref_1577_; lean_object* v_msg_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1607_; 
v_ref_1575_ = lean_ctor_get(v___y_1566_, 5);
v_a_1576_ = lean_array_uget(v_as_1562_, v_i_1564_);
v_ref_1577_ = lean_ctor_get(v_a_1576_, 0);
v_msg_1578_ = lean_ctor_get(v_a_1576_, 1);
v_isSharedCheck_1607_ = !lean_is_exclusive(v_a_1576_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1580_ = v_a_1576_;
v_isShared_1581_ = v_isSharedCheck_1607_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_msg_1578_);
lean_inc(v_ref_1577_);
lean_dec(v_a_1576_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1607_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1582_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v_ref_1599_; lean_object* v___y_1601_; lean_object* v___x_1604_; 
v___x_1582_ = lean_box(0);
v_ref_1599_ = l_Lean_replaceRef(v_ref_1577_, v_ref_1575_);
lean_dec(v_ref_1577_);
v___x_1604_ = l_Lean_Syntax_getPos_x3f(v_ref_1599_, v___x_1561_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v___x_1605_; 
v___x_1605_ = lean_unsigned_to_nat(0u);
v___y_1601_ = v___x_1605_;
goto v___jp_1600_;
}
else
{
lean_object* v_val_1606_; 
v_val_1606_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_val_1606_);
lean_dec_ref_known(v___x_1604_, 1);
v___y_1601_ = v_val_1606_;
goto v___jp_1600_;
}
v___jp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 1, v___y_1585_);
lean_ctor_set(v___x_1573_, 0, v___y_1584_);
v___x_1587_ = v___x_1573_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___y_1584_);
lean_ctor_set(v_reuseFailAlloc_1598_, 1, v___y_1585_);
v___x_1587_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v_pos2traces_1591_; lean_object* v___x_1593_; 
v___x_1588_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1589_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1571_, v___x_1587_, v___x_1588_);
v___x_1590_ = lean_array_push(v___x_1589_, v_msg_1578_);
v_pos2traces_1591_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1571_, v___x_1587_, v___x_1590_);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 1, v_pos2traces_1591_);
lean_ctor_set(v___x_1580_, 0, v___x_1582_);
v___x_1593_ = v___x_1580_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v___x_1582_);
lean_ctor_set(v_reuseFailAlloc_1597_, 1, v_pos2traces_1591_);
v___x_1593_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
size_t v___x_1594_; size_t v___x_1595_; lean_object* v___x_1596_; 
v___x_1594_ = ((size_t)1ULL);
v___x_1595_ = lean_usize_add(v_i_1564_, v___x_1594_);
v___x_1596_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_1561_, v_as_1562_, v_sz_1563_, v___x_1595_, v___x_1593_, v___y_1566_);
return v___x_1596_;
}
}
}
v___jp_1600_:
{
lean_object* v___x_1602_; 
v___x_1602_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1599_, v___x_1561_);
lean_dec(v_ref_1599_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_inc(v___y_1601_);
v___y_1584_ = v___y_1601_;
v___y_1585_ = v___y_1601_;
goto v___jp_1583_;
}
else
{
lean_object* v_val_1603_; 
v_val_1603_ = lean_ctor_get(v___x_1602_, 0);
lean_inc(v_val_1603_);
lean_dec_ref_known(v___x_1602_, 1);
v___y_1584_ = v___y_1601_;
v___y_1585_ = v_val_1603_;
goto v___jp_1583_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40___boxed(lean_object* v___x_1610_, lean_object* v_as_1611_, lean_object* v_sz_1612_, lean_object* v_i_1613_, lean_object* v_b_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
uint8_t v___x_37274__boxed_1618_; size_t v_sz_boxed_1619_; size_t v_i_boxed_1620_; lean_object* v_res_1621_; 
v___x_37274__boxed_1618_ = lean_unbox(v___x_1610_);
v_sz_boxed_1619_ = lean_unbox_usize(v_sz_1612_);
lean_dec(v_sz_1612_);
v_i_boxed_1620_ = lean_unbox_usize(v_i_1613_);
lean_dec(v_i_1613_);
v_res_1621_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(v___x_37274__boxed_1618_, v_as_1611_, v_sz_boxed_1619_, v_i_boxed_1620_, v_b_1614_, v___y_1615_, v___y_1616_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec_ref(v_as_1611_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(lean_object* v_init_1622_, uint8_t v___x_1623_, lean_object* v_n_1624_, lean_object* v_b_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
if (lean_obj_tag(v_n_1624_) == 0)
{
lean_object* v_cs_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; size_t v_sz_1632_; size_t v___x_1633_; lean_object* v___x_1634_; 
v_cs_1629_ = lean_ctor_get(v_n_1624_, 0);
v___x_1630_ = lean_box(0);
v___x_1631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1630_);
lean_ctor_set(v___x_1631_, 1, v_b_1625_);
v_sz_1632_ = lean_array_size(v_cs_1629_);
v___x_1633_ = ((size_t)0ULL);
v___x_1634_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(v_init_1622_, v___x_1623_, v_cs_1629_, v_sz_1632_, v___x_1633_, v___x_1631_, v___y_1626_, v___y_1627_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1649_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1637_ = v___x_1634_;
v_isShared_1638_ = v_isSharedCheck_1649_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1634_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1649_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v_fst_1639_; 
v_fst_1639_ = lean_ctor_get(v_a_1635_, 0);
if (lean_obj_tag(v_fst_1639_) == 0)
{
lean_object* v_snd_1640_; lean_object* v___x_1641_; lean_object* v___x_1643_; 
v_snd_1640_ = lean_ctor_get(v_a_1635_, 1);
lean_inc(v_snd_1640_);
lean_dec(v_a_1635_);
v___x_1641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1641_, 0, v_snd_1640_);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v___x_1641_);
v___x_1643_ = v___x_1637_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1641_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
else
{
lean_object* v_val_1645_; lean_object* v___x_1647_; 
lean_inc_ref(v_fst_1639_);
lean_dec(v_a_1635_);
v_val_1645_ = lean_ctor_get(v_fst_1639_, 0);
lean_inc(v_val_1645_);
lean_dec_ref_known(v_fst_1639_, 1);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v_val_1645_);
v___x_1647_ = v___x_1637_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_val_1645_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
else
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
v_a_1650_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v___x_1634_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1634_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1650_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
else
{
lean_object* v_vs_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; size_t v_sz_1661_; size_t v___x_1662_; lean_object* v___x_1663_; 
v_vs_1658_ = lean_ctor_get(v_n_1624_, 0);
v___x_1659_ = lean_box(0);
v___x_1660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1659_);
lean_ctor_set(v___x_1660_, 1, v_b_1625_);
v_sz_1661_ = lean_array_size(v_vs_1658_);
v___x_1662_ = ((size_t)0ULL);
v___x_1663_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(v___x_1623_, v_vs_1658_, v_sz_1661_, v___x_1662_, v___x_1660_, v___y_1626_, v___y_1627_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1678_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1666_ = v___x_1663_;
v_isShared_1667_ = v_isSharedCheck_1678_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1663_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1678_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v_fst_1668_; 
v_fst_1668_ = lean_ctor_get(v_a_1664_, 0);
if (lean_obj_tag(v_fst_1668_) == 0)
{
lean_object* v_snd_1669_; lean_object* v___x_1670_; lean_object* v___x_1672_; 
v_snd_1669_ = lean_ctor_get(v_a_1664_, 1);
lean_inc(v_snd_1669_);
lean_dec(v_a_1664_);
v___x_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1670_, 0, v_snd_1669_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 0, v___x_1670_);
v___x_1672_ = v___x_1666_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1670_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
else
{
lean_object* v_val_1674_; lean_object* v___x_1676_; 
lean_inc_ref(v_fst_1668_);
lean_dec(v_a_1664_);
v_val_1674_ = lean_ctor_get(v_fst_1668_, 0);
lean_inc(v_val_1674_);
lean_dec_ref_known(v_fst_1668_, 1);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 0, v_val_1674_);
v___x_1676_ = v___x_1666_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_val_1674_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
v_a_1679_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1663_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1663_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(lean_object* v_init_1687_, uint8_t v___x_1688_, lean_object* v_as_1689_, size_t v_sz_1690_, size_t v_i_1691_, lean_object* v_b_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
uint8_t v___x_1696_; 
v___x_1696_ = lean_usize_dec_lt(v_i_1691_, v_sz_1690_);
if (v___x_1696_ == 0)
{
lean_object* v___x_1697_; 
v___x_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1697_, 0, v_b_1692_);
return v___x_1697_;
}
else
{
lean_object* v_snd_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1732_; 
v_snd_1698_ = lean_ctor_get(v_b_1692_, 1);
v_isSharedCheck_1732_ = !lean_is_exclusive(v_b_1692_);
if (v_isSharedCheck_1732_ == 0)
{
lean_object* v_unused_1733_; 
v_unused_1733_ = lean_ctor_get(v_b_1692_, 0);
lean_dec(v_unused_1733_);
v___x_1700_ = v_b_1692_;
v_isShared_1701_ = v_isSharedCheck_1732_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_snd_1698_);
lean_dec(v_b_1692_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1732_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v_a_1702_; lean_object* v___x_1703_; 
v_a_1702_ = lean_array_uget_borrowed(v_as_1689_, v_i_1691_);
lean_inc(v_snd_1698_);
v___x_1703_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1687_, v___x_1688_, v_a_1702_, v_snd_1698_, v___y_1693_, v___y_1694_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1723_; 
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1706_ = v___x_1703_;
v_isShared_1707_ = v_isSharedCheck_1723_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v___x_1703_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1723_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
if (lean_obj_tag(v_a_1704_) == 0)
{
lean_object* v___x_1708_; lean_object* v___x_1710_; 
v___x_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1708_, 0, v_a_1704_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 0, v___x_1708_);
v___x_1710_ = v___x_1700_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v___x_1708_);
lean_ctor_set(v_reuseFailAlloc_1714_, 1, v_snd_1698_);
v___x_1710_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
lean_object* v___x_1712_; 
if (v_isShared_1707_ == 0)
{
lean_ctor_set(v___x_1706_, 0, v___x_1710_);
v___x_1712_ = v___x_1706_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1710_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1716_; lean_object* v___x_1718_; 
lean_del_object(v___x_1706_);
lean_dec(v_snd_1698_);
v_a_1715_ = lean_ctor_get(v_a_1704_, 0);
lean_inc(v_a_1715_);
lean_dec_ref_known(v_a_1704_, 1);
v___x_1716_ = lean_box(0);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 1, v_a_1715_);
lean_ctor_set(v___x_1700_, 0, v___x_1716_);
v___x_1718_ = v___x_1700_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1716_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_a_1715_);
v___x_1718_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
size_t v___x_1719_; size_t v___x_1720_; 
v___x_1719_ = ((size_t)1ULL);
v___x_1720_ = lean_usize_add(v_i_1691_, v___x_1719_);
v_i_1691_ = v___x_1720_;
v_b_1692_ = v___x_1718_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
lean_del_object(v___x_1700_);
lean_dec(v_snd_1698_);
v_a_1724_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1703_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1703_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39___boxed(lean_object* v_init_1734_, lean_object* v___x_1735_, lean_object* v_as_1736_, lean_object* v_sz_1737_, lean_object* v_i_1738_, lean_object* v_b_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
uint8_t v___x_37355__boxed_1743_; size_t v_sz_boxed_1744_; size_t v_i_boxed_1745_; lean_object* v_res_1746_; 
v___x_37355__boxed_1743_ = lean_unbox(v___x_1735_);
v_sz_boxed_1744_ = lean_unbox_usize(v_sz_1737_);
lean_dec(v_sz_1737_);
v_i_boxed_1745_ = lean_unbox_usize(v_i_1738_);
lean_dec(v_i_1738_);
v_res_1746_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(v_init_1734_, v___x_37355__boxed_1743_, v_as_1736_, v_sz_boxed_1744_, v_i_boxed_1745_, v_b_1739_, v___y_1740_, v___y_1741_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec_ref(v_as_1736_);
lean_dec_ref(v_init_1734_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27___boxed(lean_object* v_init_1747_, lean_object* v___x_1748_, lean_object* v_n_1749_, lean_object* v_b_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
uint8_t v___x_37375__boxed_1754_; lean_object* v_res_1755_; 
v___x_37375__boxed_1754_ = lean_unbox(v___x_1748_);
v_res_1755_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1747_, v___x_37375__boxed_1754_, v_n_1749_, v_b_1750_, v___y_1751_, v___y_1752_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec_ref(v_n_1749_);
lean_dec_ref(v_init_1747_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(uint8_t v___x_1756_, lean_object* v_as_1757_, size_t v_sz_1758_, size_t v_i_1759_, lean_object* v_b_1760_, lean_object* v___y_1761_){
_start:
{
uint8_t v___x_1763_; 
v___x_1763_ = lean_usize_dec_lt(v_i_1759_, v_sz_1758_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; 
v___x_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1764_, 0, v_b_1760_);
return v___x_1764_;
}
else
{
lean_object* v_snd_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1802_; 
v_snd_1765_ = lean_ctor_get(v_b_1760_, 1);
v_isSharedCheck_1802_ = !lean_is_exclusive(v_b_1760_);
if (v_isSharedCheck_1802_ == 0)
{
lean_object* v_unused_1803_; 
v_unused_1803_ = lean_ctor_get(v_b_1760_, 0);
lean_dec(v_unused_1803_);
v___x_1767_ = v_b_1760_;
v_isShared_1768_ = v_isSharedCheck_1802_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_snd_1765_);
lean_dec(v_b_1760_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1802_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v_ref_1769_; lean_object* v_a_1770_; lean_object* v_ref_1771_; lean_object* v_msg_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1801_; 
v_ref_1769_ = lean_ctor_get(v___y_1761_, 5);
v_a_1770_ = lean_array_uget(v_as_1757_, v_i_1759_);
v_ref_1771_ = lean_ctor_get(v_a_1770_, 0);
v_msg_1772_ = lean_ctor_get(v_a_1770_, 1);
v_isSharedCheck_1801_ = !lean_is_exclusive(v_a_1770_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1774_ = v_a_1770_;
v_isShared_1775_ = v_isSharedCheck_1801_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_msg_1772_);
lean_inc(v_ref_1771_);
lean_dec(v_a_1770_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1801_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1776_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v_ref_1793_; lean_object* v___y_1795_; lean_object* v___x_1798_; 
v___x_1776_ = lean_box(0);
v_ref_1793_ = l_Lean_replaceRef(v_ref_1771_, v_ref_1769_);
lean_dec(v_ref_1771_);
v___x_1798_ = l_Lean_Syntax_getPos_x3f(v_ref_1793_, v___x_1756_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v___x_1799_; 
v___x_1799_ = lean_unsigned_to_nat(0u);
v___y_1795_ = v___x_1799_;
goto v___jp_1794_;
}
else
{
lean_object* v_val_1800_; 
v_val_1800_ = lean_ctor_get(v___x_1798_, 0);
lean_inc(v_val_1800_);
lean_dec_ref_known(v___x_1798_, 1);
v___y_1795_ = v_val_1800_;
goto v___jp_1794_;
}
v___jp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 1, v___y_1779_);
lean_ctor_set(v___x_1767_, 0, v___y_1778_);
v___x_1781_ = v___x_1767_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v___y_1778_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v___y_1779_);
v___x_1781_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v_pos2traces_1785_; lean_object* v___x_1787_; 
v___x_1782_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1783_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1765_, v___x_1781_, v___x_1782_);
v___x_1784_ = lean_array_push(v___x_1783_, v_msg_1772_);
v_pos2traces_1785_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1765_, v___x_1781_, v___x_1784_);
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 1, v_pos2traces_1785_);
lean_ctor_set(v___x_1774_, 0, v___x_1776_);
v___x_1787_ = v___x_1774_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1776_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v_pos2traces_1785_);
v___x_1787_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
size_t v___x_1788_; size_t v___x_1789_; 
v___x_1788_ = ((size_t)1ULL);
v___x_1789_ = lean_usize_add(v_i_1759_, v___x_1788_);
v_i_1759_ = v___x_1789_;
v_b_1760_ = v___x_1787_;
goto _start;
}
}
}
v___jp_1794_:
{
lean_object* v___x_1796_; 
v___x_1796_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1793_, v___x_1756_);
lean_dec(v_ref_1793_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_inc(v___y_1795_);
v___y_1778_ = v___y_1795_;
v___y_1779_ = v___y_1795_;
goto v___jp_1777_;
}
else
{
lean_object* v_val_1797_; 
v_val_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_val_1797_);
lean_dec_ref_known(v___x_1796_, 1);
v___y_1778_ = v___y_1795_;
v___y_1779_ = v_val_1797_;
goto v___jp_1777_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg___boxed(lean_object* v___x_1804_, lean_object* v_as_1805_, lean_object* v_sz_1806_, lean_object* v_i_1807_, lean_object* v_b_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
uint8_t v___x_37558__boxed_1811_; size_t v_sz_boxed_1812_; size_t v_i_boxed_1813_; lean_object* v_res_1814_; 
v___x_37558__boxed_1811_ = lean_unbox(v___x_1804_);
v_sz_boxed_1812_ = lean_unbox_usize(v_sz_1806_);
lean_dec(v_sz_1806_);
v_i_boxed_1813_ = lean_unbox_usize(v_i_1807_);
lean_dec(v_i_1807_);
v_res_1814_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_37558__boxed_1811_, v_as_1805_, v_sz_boxed_1812_, v_i_boxed_1813_, v_b_1808_, v___y_1809_);
lean_dec_ref(v___y_1809_);
lean_dec_ref(v_as_1805_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(uint8_t v___x_1815_, lean_object* v_as_1816_, size_t v_sz_1817_, size_t v_i_1818_, lean_object* v_b_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
uint8_t v___x_1823_; 
v___x_1823_ = lean_usize_dec_lt(v_i_1818_, v_sz_1817_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; 
v___x_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1824_, 0, v_b_1819_);
return v___x_1824_;
}
else
{
lean_object* v_snd_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1862_; 
v_snd_1825_ = lean_ctor_get(v_b_1819_, 1);
v_isSharedCheck_1862_ = !lean_is_exclusive(v_b_1819_);
if (v_isSharedCheck_1862_ == 0)
{
lean_object* v_unused_1863_; 
v_unused_1863_ = lean_ctor_get(v_b_1819_, 0);
lean_dec(v_unused_1863_);
v___x_1827_ = v_b_1819_;
v_isShared_1828_ = v_isSharedCheck_1862_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_snd_1825_);
lean_dec(v_b_1819_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1862_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v_ref_1829_; lean_object* v_a_1830_; lean_object* v_ref_1831_; lean_object* v_msg_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1861_; 
v_ref_1829_ = lean_ctor_get(v___y_1820_, 5);
v_a_1830_ = lean_array_uget(v_as_1816_, v_i_1818_);
v_ref_1831_ = lean_ctor_get(v_a_1830_, 0);
v_msg_1832_ = lean_ctor_get(v_a_1830_, 1);
v_isSharedCheck_1861_ = !lean_is_exclusive(v_a_1830_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1834_ = v_a_1830_;
v_isShared_1835_ = v_isSharedCheck_1861_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_msg_1832_);
lean_inc(v_ref_1831_);
lean_dec(v_a_1830_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1861_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1836_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v_ref_1853_; lean_object* v___y_1855_; lean_object* v___x_1858_; 
v___x_1836_ = lean_box(0);
v_ref_1853_ = l_Lean_replaceRef(v_ref_1831_, v_ref_1829_);
lean_dec(v_ref_1831_);
v___x_1858_ = l_Lean_Syntax_getPos_x3f(v_ref_1853_, v___x_1815_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v___x_1859_; 
v___x_1859_ = lean_unsigned_to_nat(0u);
v___y_1855_ = v___x_1859_;
goto v___jp_1854_;
}
else
{
lean_object* v_val_1860_; 
v_val_1860_ = lean_ctor_get(v___x_1858_, 0);
lean_inc(v_val_1860_);
lean_dec_ref_known(v___x_1858_, 1);
v___y_1855_ = v_val_1860_;
goto v___jp_1854_;
}
v___jp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 1, v___y_1839_);
lean_ctor_set(v___x_1827_, 0, v___y_1838_);
v___x_1841_ = v___x_1827_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___y_1838_);
lean_ctor_set(v_reuseFailAlloc_1852_, 1, v___y_1839_);
v___x_1841_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v_pos2traces_1845_; lean_object* v___x_1847_; 
v___x_1842_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1843_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1825_, v___x_1841_, v___x_1842_);
v___x_1844_ = lean_array_push(v___x_1843_, v_msg_1832_);
v_pos2traces_1845_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1825_, v___x_1841_, v___x_1844_);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 1, v_pos2traces_1845_);
lean_ctor_set(v___x_1834_, 0, v___x_1836_);
v___x_1847_ = v___x_1834_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v___x_1836_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v_pos2traces_1845_);
v___x_1847_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
size_t v___x_1848_; size_t v___x_1849_; lean_object* v___x_1850_; 
v___x_1848_ = ((size_t)1ULL);
v___x_1849_ = lean_usize_add(v_i_1818_, v___x_1848_);
v___x_1850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_1815_, v_as_1816_, v_sz_1817_, v___x_1849_, v___x_1847_, v___y_1820_);
return v___x_1850_;
}
}
}
v___jp_1854_:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1853_, v___x_1815_);
lean_dec(v_ref_1853_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_inc(v___y_1855_);
v___y_1838_ = v___y_1855_;
v___y_1839_ = v___y_1855_;
goto v___jp_1837_;
}
else
{
lean_object* v_val_1857_; 
v_val_1857_ = lean_ctor_get(v___x_1856_, 0);
lean_inc(v_val_1857_);
lean_dec_ref_known(v___x_1856_, 1);
v___y_1838_ = v___y_1855_;
v___y_1839_ = v_val_1857_;
goto v___jp_1837_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28___boxed(lean_object* v___x_1864_, lean_object* v_as_1865_, lean_object* v_sz_1866_, lean_object* v_i_1867_, lean_object* v_b_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
uint8_t v___x_37638__boxed_1872_; size_t v_sz_boxed_1873_; size_t v_i_boxed_1874_; lean_object* v_res_1875_; 
v___x_37638__boxed_1872_ = lean_unbox(v___x_1864_);
v_sz_boxed_1873_ = lean_unbox_usize(v_sz_1866_);
lean_dec(v_sz_1866_);
v_i_boxed_1874_ = lean_unbox_usize(v_i_1867_);
lean_dec(v_i_1867_);
v_res_1875_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(v___x_37638__boxed_1872_, v_as_1865_, v_sz_boxed_1873_, v_i_boxed_1874_, v_b_1868_, v___y_1869_, v___y_1870_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec_ref(v_as_1865_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(uint8_t v___x_1876_, lean_object* v_t_1877_, lean_object* v_init_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v_root_1882_; lean_object* v_tail_1883_; lean_object* v___x_1884_; 
v_root_1882_ = lean_ctor_get(v_t_1877_, 0);
v_tail_1883_ = lean_ctor_get(v_t_1877_, 1);
lean_inc_ref(v_init_1878_);
v___x_1884_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1878_, v___x_1876_, v_root_1882_, v_init_1878_, v___y_1879_, v___y_1880_);
lean_dec_ref(v_init_1878_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1921_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1887_ = v___x_1884_;
v_isShared_1888_ = v_isSharedCheck_1921_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1884_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1921_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
if (lean_obj_tag(v_a_1885_) == 0)
{
lean_object* v_a_1889_; lean_object* v___x_1891_; 
v_a_1889_ = lean_ctor_get(v_a_1885_, 0);
lean_inc(v_a_1889_);
lean_dec_ref_known(v_a_1885_, 1);
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 0, v_a_1889_);
v___x_1891_ = v___x_1887_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1889_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
else
{
lean_object* v_a_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; size_t v_sz_1896_; size_t v___x_1897_; lean_object* v___x_1898_; 
lean_del_object(v___x_1887_);
v_a_1893_ = lean_ctor_get(v_a_1885_, 0);
lean_inc(v_a_1893_);
lean_dec_ref_known(v_a_1885_, 1);
v___x_1894_ = lean_box(0);
v___x_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
lean_ctor_set(v___x_1895_, 1, v_a_1893_);
v_sz_1896_ = lean_array_size(v_tail_1883_);
v___x_1897_ = ((size_t)0ULL);
v___x_1898_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(v___x_1876_, v_tail_1883_, v_sz_1896_, v___x_1897_, v___x_1895_, v___y_1879_, v___y_1880_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1912_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1901_ = v___x_1898_;
v_isShared_1902_ = v_isSharedCheck_1912_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1898_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1912_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v_fst_1903_; 
v_fst_1903_ = lean_ctor_get(v_a_1899_, 0);
if (lean_obj_tag(v_fst_1903_) == 0)
{
lean_object* v_snd_1904_; lean_object* v___x_1906_; 
v_snd_1904_ = lean_ctor_get(v_a_1899_, 1);
lean_inc(v_snd_1904_);
lean_dec(v_a_1899_);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 0, v_snd_1904_);
v___x_1906_ = v___x_1901_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_snd_1904_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
else
{
lean_object* v_val_1908_; lean_object* v___x_1910_; 
lean_inc_ref(v_fst_1903_);
lean_dec(v_a_1899_);
v_val_1908_ = lean_ctor_get(v_fst_1903_, 0);
lean_inc(v_val_1908_);
lean_dec_ref_known(v_fst_1903_, 1);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 0, v_val_1908_);
v___x_1910_ = v___x_1901_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_val_1908_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
else
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
v_a_1913_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1915_ = v___x_1898_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1898_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
}
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
v_a_1922_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1884_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1884_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19___boxed(lean_object* v___x_1930_, lean_object* v_t_1931_, lean_object* v_init_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
uint8_t v___x_37719__boxed_1936_; lean_object* v_res_1937_; 
v___x_37719__boxed_1936_ = lean_unbox(v___x_1930_);
v_res_1937_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(v___x_37719__boxed_1936_, v_t_1931_, v_init_1932_, v___y_1933_, v___y_1934_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec_ref(v_t_1931_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(lean_object* v_x_1938_, lean_object* v_x_1939_){
_start:
{
if (lean_obj_tag(v_x_1939_) == 0)
{
return v_x_1938_;
}
else
{
lean_object* v_key_1940_; lean_object* v_value_1941_; lean_object* v_tail_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v_key_1940_ = lean_ctor_get(v_x_1939_, 0);
v_value_1941_ = lean_ctor_get(v_x_1939_, 1);
v_tail_1942_ = lean_ctor_get(v_x_1939_, 2);
lean_inc(v_value_1941_);
lean_inc(v_key_1940_);
v___x_1943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1943_, 0, v_key_1940_);
lean_ctor_set(v___x_1943_, 1, v_value_1941_);
v___x_1944_ = lean_array_push(v_x_1938_, v___x_1943_);
v_x_1938_ = v___x_1944_;
v_x_1939_ = v_tail_1942_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22___boxed(lean_object* v_x_1946_, lean_object* v_x_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(v_x_1946_, v_x_1947_);
lean_dec(v_x_1947_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(lean_object* v_as_1949_, size_t v_i_1950_, size_t v_stop_1951_, lean_object* v_b_1952_){
_start:
{
uint8_t v___x_1953_; 
v___x_1953_ = lean_usize_dec_eq(v_i_1950_, v_stop_1951_);
if (v___x_1953_ == 0)
{
lean_object* v___x_1954_; lean_object* v___x_1955_; size_t v___x_1956_; size_t v___x_1957_; 
v___x_1954_ = lean_array_uget_borrowed(v_as_1949_, v_i_1950_);
v___x_1955_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(v_b_1952_, v___x_1954_);
v___x_1956_ = ((size_t)1ULL);
v___x_1957_ = lean_usize_add(v_i_1950_, v___x_1956_);
v_i_1950_ = v___x_1957_;
v_b_1952_ = v___x_1955_;
goto _start;
}
else
{
return v_b_1952_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23___boxed(lean_object* v_as_1959_, lean_object* v_i_1960_, lean_object* v_stop_1961_, lean_object* v_b_1962_){
_start:
{
size_t v_i_boxed_1963_; size_t v_stop_boxed_1964_; lean_object* v_res_1965_; 
v_i_boxed_1963_ = lean_unbox_usize(v_i_1960_);
lean_dec(v_i_1960_);
v_stop_boxed_1964_ = lean_unbox_usize(v_stop_1961_);
lean_dec(v_stop_1961_);
v_res_1965_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_as_1959_, v_i_boxed_1963_, v_stop_boxed_1964_, v_b_1962_);
lean_dec_ref(v_as_1959_);
return v_res_1965_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0(void){
_start:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1966_ = lean_unsigned_to_nat(32u);
v___x_1967_ = lean_mk_empty_array_with_capacity(v___x_1966_);
v___x_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1967_);
return v___x_1968_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1(void){
_start:
{
size_t v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1969_ = ((size_t)5ULL);
v___x_1970_ = lean_unsigned_to_nat(0u);
v___x_1971_ = lean_unsigned_to_nat(32u);
v___x_1972_ = lean_mk_empty_array_with_capacity(v___x_1971_);
v___x_1973_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0);
v___x_1974_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1974_, 0, v___x_1973_);
lean_ctor_set(v___x_1974_, 1, v___x_1972_);
lean_ctor_set(v___x_1974_, 2, v___x_1970_);
lean_ctor_set(v___x_1974_, 3, v___x_1970_);
lean_ctor_set_usize(v___x_1974_, 4, v___x_1969_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(lean_object* v___y_1975_){
_start:
{
lean_object* v___x_1977_; lean_object* v_traceState_1978_; lean_object* v_traces_1979_; lean_object* v___x_1980_; lean_object* v_traceState_1981_; lean_object* v_env_1982_; lean_object* v_nextMacroScope_1983_; lean_object* v_ngen_1984_; lean_object* v_auxDeclNGen_1985_; lean_object* v_cache_1986_; lean_object* v_messages_1987_; lean_object* v_infoState_1988_; lean_object* v_snapshotTasks_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2008_; 
v___x_1977_ = lean_st_ref_get(v___y_1975_);
v_traceState_1978_ = lean_ctor_get(v___x_1977_, 4);
lean_inc_ref(v_traceState_1978_);
lean_dec(v___x_1977_);
v_traces_1979_ = lean_ctor_get(v_traceState_1978_, 0);
lean_inc_ref(v_traces_1979_);
lean_dec_ref(v_traceState_1978_);
v___x_1980_ = lean_st_ref_take(v___y_1975_);
v_traceState_1981_ = lean_ctor_get(v___x_1980_, 4);
v_env_1982_ = lean_ctor_get(v___x_1980_, 0);
v_nextMacroScope_1983_ = lean_ctor_get(v___x_1980_, 1);
v_ngen_1984_ = lean_ctor_get(v___x_1980_, 2);
v_auxDeclNGen_1985_ = lean_ctor_get(v___x_1980_, 3);
v_cache_1986_ = lean_ctor_get(v___x_1980_, 5);
v_messages_1987_ = lean_ctor_get(v___x_1980_, 6);
v_infoState_1988_ = lean_ctor_get(v___x_1980_, 7);
v_snapshotTasks_1989_ = lean_ctor_get(v___x_1980_, 8);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_1991_ = v___x_1980_;
v_isShared_1992_ = v_isSharedCheck_2008_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_snapshotTasks_1989_);
lean_inc(v_infoState_1988_);
lean_inc(v_messages_1987_);
lean_inc(v_cache_1986_);
lean_inc(v_traceState_1981_);
lean_inc(v_auxDeclNGen_1985_);
lean_inc(v_ngen_1984_);
lean_inc(v_nextMacroScope_1983_);
lean_inc(v_env_1982_);
lean_dec(v___x_1980_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2008_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
uint64_t v_tid_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2006_; 
v_tid_1993_ = lean_ctor_get_uint64(v_traceState_1981_, sizeof(void*)*1);
v_isSharedCheck_2006_ = !lean_is_exclusive(v_traceState_1981_);
if (v_isSharedCheck_2006_ == 0)
{
lean_object* v_unused_2007_; 
v_unused_2007_ = lean_ctor_get(v_traceState_1981_, 0);
lean_dec(v_unused_2007_);
v___x_1995_ = v_traceState_1981_;
v_isShared_1996_ = v_isSharedCheck_2006_;
goto v_resetjp_1994_;
}
else
{
lean_dec(v_traceState_1981_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2006_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1997_; lean_object* v___x_1999_; 
v___x_1997_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 0, v___x_1997_);
v___x_1999_ = v___x_1995_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_1997_);
lean_ctor_set_uint64(v_reuseFailAlloc_2005_, sizeof(void*)*1, v_tid_1993_);
v___x_1999_ = v_reuseFailAlloc_2005_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
lean_object* v___x_2001_; 
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 4, v___x_1999_);
v___x_2001_ = v___x_1991_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_env_1982_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v_nextMacroScope_1983_);
lean_ctor_set(v_reuseFailAlloc_2004_, 2, v_ngen_1984_);
lean_ctor_set(v_reuseFailAlloc_2004_, 3, v_auxDeclNGen_1985_);
lean_ctor_set(v_reuseFailAlloc_2004_, 4, v___x_1999_);
lean_ctor_set(v_reuseFailAlloc_2004_, 5, v_cache_1986_);
lean_ctor_set(v_reuseFailAlloc_2004_, 6, v_messages_1987_);
lean_ctor_set(v_reuseFailAlloc_2004_, 7, v_infoState_1988_);
lean_ctor_set(v_reuseFailAlloc_2004_, 8, v_snapshotTasks_1989_);
v___x_2001_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2002_ = lean_st_ref_set(v___y_1975_, v___x_2001_);
v___x_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2003_, 0, v_traces_1979_);
return v___x_2003_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___boxed(lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_2009_);
lean_dec(v___y_2009_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(lean_object* v_hi_2012_, lean_object* v_pivot_2013_, lean_object* v_as_2014_, lean_object* v_i_2015_, lean_object* v_k_2016_){
_start:
{
uint8_t v___x_2017_; 
v___x_2017_ = lean_nat_dec_lt(v_k_2016_, v_hi_2012_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
lean_dec(v_k_2016_);
v___x_2018_ = lean_array_fswap(v_as_2014_, v_i_2015_, v_hi_2012_);
v___x_2019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2019_, 0, v_i_2015_);
lean_ctor_set(v___x_2019_, 1, v___x_2018_);
return v___x_2019_;
}
else
{
lean_object* v___x_2020_; lean_object* v_fst_2021_; lean_object* v_fst_2022_; lean_object* v_fst_2023_; lean_object* v_fst_2024_; uint8_t v___x_2025_; 
v___x_2020_ = lean_array_fget_borrowed(v_as_2014_, v_k_2016_);
v_fst_2021_ = lean_ctor_get(v___x_2020_, 0);
v_fst_2022_ = lean_ctor_get(v_pivot_2013_, 0);
v_fst_2023_ = lean_ctor_get(v_fst_2021_, 0);
v_fst_2024_ = lean_ctor_get(v_fst_2022_, 0);
v___x_2025_ = lean_nat_dec_lt(v_fst_2023_, v_fst_2024_);
if (v___x_2025_ == 0)
{
lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2026_ = lean_unsigned_to_nat(1u);
v___x_2027_ = lean_nat_add(v_k_2016_, v___x_2026_);
lean_dec(v_k_2016_);
v_k_2016_ = v___x_2027_;
goto _start;
}
else
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2029_ = lean_array_fswap(v_as_2014_, v_i_2015_, v_k_2016_);
v___x_2030_ = lean_unsigned_to_nat(1u);
v___x_2031_ = lean_nat_add(v_i_2015_, v___x_2030_);
lean_dec(v_i_2015_);
v___x_2032_ = lean_nat_add(v_k_2016_, v___x_2030_);
lean_dec(v_k_2016_);
v_as_2014_ = v___x_2029_;
v_i_2015_ = v___x_2031_;
v_k_2016_ = v___x_2032_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg___boxed(lean_object* v_hi_2034_, lean_object* v_pivot_2035_, lean_object* v_as_2036_, lean_object* v_i_2037_, lean_object* v_k_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_2034_, v_pivot_2035_, v_as_2036_, v_i_2037_, v_k_2038_);
lean_dec_ref(v_pivot_2035_);
lean_dec(v_hi_2034_);
return v_res_2039_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(lean_object* v_x_2040_, lean_object* v_x_2041_){
_start:
{
lean_object* v_fst_2042_; lean_object* v_fst_2043_; lean_object* v_fst_2044_; lean_object* v_fst_2045_; uint8_t v___x_2046_; 
v_fst_2042_ = lean_ctor_get(v_x_2040_, 0);
v_fst_2043_ = lean_ctor_get(v_x_2041_, 0);
v_fst_2044_ = lean_ctor_get(v_fst_2042_, 0);
v_fst_2045_ = lean_ctor_get(v_fst_2043_, 0);
v___x_2046_ = lean_nat_dec_lt(v_fst_2044_, v_fst_2045_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0___boxed(lean_object* v_x_2047_, lean_object* v_x_2048_){
_start:
{
uint8_t v_res_2049_; lean_object* v_r_2050_; 
v_res_2049_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v_x_2047_, v_x_2048_);
lean_dec_ref(v_x_2048_);
lean_dec_ref(v_x_2047_);
v_r_2050_ = lean_box(v_res_2049_);
return v_r_2050_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(lean_object* v_n_2051_, lean_object* v_as_2052_, lean_object* v_lo_2053_, lean_object* v_hi_2054_){
_start:
{
lean_object* v___y_2056_; uint8_t v___x_2066_; 
v___x_2066_ = lean_nat_dec_lt(v_lo_2053_, v_hi_2054_);
if (v___x_2066_ == 0)
{
lean_dec(v_lo_2053_);
return v_as_2052_;
}
else
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v_mid_2069_; lean_object* v___y_2071_; lean_object* v___y_2077_; lean_object* v___x_2082_; lean_object* v___x_2083_; uint8_t v___x_2084_; 
v___x_2067_ = lean_nat_add(v_lo_2053_, v_hi_2054_);
v___x_2068_ = lean_unsigned_to_nat(1u);
v_mid_2069_ = lean_nat_shiftr(v___x_2067_, v___x_2068_);
lean_dec(v___x_2067_);
v___x_2082_ = lean_array_fget_borrowed(v_as_2052_, v_mid_2069_);
v___x_2083_ = lean_array_fget_borrowed(v_as_2052_, v_lo_2053_);
v___x_2084_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2082_, v___x_2083_);
if (v___x_2084_ == 0)
{
v___y_2077_ = v_as_2052_;
goto v___jp_2076_;
}
else
{
lean_object* v___x_2085_; 
v___x_2085_ = lean_array_fswap(v_as_2052_, v_lo_2053_, v_mid_2069_);
v___y_2077_ = v___x_2085_;
goto v___jp_2076_;
}
v___jp_2070_:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; uint8_t v___x_2074_; 
v___x_2072_ = lean_array_fget_borrowed(v___y_2071_, v_mid_2069_);
v___x_2073_ = lean_array_fget_borrowed(v___y_2071_, v_hi_2054_);
v___x_2074_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2072_, v___x_2073_);
if (v___x_2074_ == 0)
{
lean_dec(v_mid_2069_);
v___y_2056_ = v___y_2071_;
goto v___jp_2055_;
}
else
{
lean_object* v___x_2075_; 
v___x_2075_ = lean_array_fswap(v___y_2071_, v_mid_2069_, v_hi_2054_);
lean_dec(v_mid_2069_);
v___y_2056_ = v___x_2075_;
goto v___jp_2055_;
}
}
v___jp_2076_:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; uint8_t v___x_2080_; 
v___x_2078_ = lean_array_fget_borrowed(v___y_2077_, v_hi_2054_);
v___x_2079_ = lean_array_fget_borrowed(v___y_2077_, v_lo_2053_);
v___x_2080_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2078_, v___x_2079_);
if (v___x_2080_ == 0)
{
v___y_2071_ = v___y_2077_;
goto v___jp_2070_;
}
else
{
lean_object* v___x_2081_; 
v___x_2081_ = lean_array_fswap(v___y_2077_, v_lo_2053_, v_hi_2054_);
v___y_2071_ = v___x_2081_;
goto v___jp_2070_;
}
}
}
v___jp_2055_:
{
lean_object* v_pivot_2057_; lean_object* v___x_2058_; lean_object* v_fst_2059_; lean_object* v_snd_2060_; uint8_t v___x_2061_; 
v_pivot_2057_ = lean_array_fget(v___y_2056_, v_hi_2054_);
lean_inc_n(v_lo_2053_, 2);
v___x_2058_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_2054_, v_pivot_2057_, v___y_2056_, v_lo_2053_, v_lo_2053_);
lean_dec(v_pivot_2057_);
v_fst_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_fst_2059_);
v_snd_2060_ = lean_ctor_get(v___x_2058_, 1);
lean_inc(v_snd_2060_);
lean_dec_ref(v___x_2058_);
v___x_2061_ = lean_nat_dec_le(v_hi_2054_, v_fst_2059_);
if (v___x_2061_ == 0)
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2062_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_2051_, v_snd_2060_, v_lo_2053_, v_fst_2059_);
v___x_2063_ = lean_unsigned_to_nat(1u);
v___x_2064_ = lean_nat_add(v_fst_2059_, v___x_2063_);
lean_dec(v_fst_2059_);
v_as_2052_ = v___x_2062_;
v_lo_2053_ = v___x_2064_;
goto _start;
}
else
{
lean_dec(v_fst_2059_);
lean_dec(v_lo_2053_);
return v_snd_2060_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___boxed(lean_object* v_n_2086_, lean_object* v_as_2087_, lean_object* v_lo_2088_, lean_object* v_hi_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_2086_, v_as_2087_, v_lo_2088_, v_hi_2089_);
lean_dec(v_hi_2089_);
lean_dec(v_n_2086_);
return v_res_2090_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0(void){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2091_ = lean_box(0);
v___x_2092_ = lean_unsigned_to_nat(16u);
v___x_2093_ = lean_mk_array(v___x_2092_, v___x_2091_);
return v___x_2093_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1(void){
_start:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v_pos2traces_2096_; 
v___x_2094_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0, &l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0);
v___x_2095_ = lean_unsigned_to_nat(0u);
v_pos2traces_2096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos2traces_2096_, 0, v___x_2095_);
lean_ctor_set(v_pos2traces_2096_, 1, v___x_2094_);
return v_pos2traces_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10(lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
lean_object* v_options_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v_options_2103_ = lean_ctor_get(v___y_2097_, 2);
v___x_2104_ = l_Lean_trace_profiler_output;
v___x_2105_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(v_options_2103_, v___x_2104_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v___x_2106_; uint8_t v___x_2107_; 
v___x_2106_ = l_Lean_trace_profiler_serve;
v___x_2107_ = l_Lean_Option_get___at___00main_spec__8(v_options_2103_, v___x_2106_);
if (v___x_2107_ == 0)
{
lean_object* v___x_2108_; lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2175_; 
v___x_2108_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_2098_);
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2111_ = v___x_2108_;
v_isShared_2112_ = v_isSharedCheck_2175_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2108_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2175_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
uint8_t v___x_2113_; 
v___x_2113_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_2109_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; lean_object* v_pos2traces_2115_; lean_object* v___x_2116_; 
lean_del_object(v___x_2111_);
v___x_2114_ = lean_unsigned_to_nat(0u);
v_pos2traces_2115_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1, &l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1);
v___x_2116_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(v___x_2113_, v_a_2109_, v_pos2traces_2115_, v___y_2097_, v___y_2098_);
lean_dec(v_a_2109_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v___y_2119_; lean_object* v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v___y_2145_; lean_object* v_size_2151_; lean_object* v_buckets_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; uint8_t v___x_2155_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_a_2117_);
lean_dec_ref_known(v___x_2116_, 1);
v_size_2151_ = lean_ctor_get(v_a_2117_, 0);
lean_inc(v_size_2151_);
v_buckets_2152_ = lean_ctor_get(v_a_2117_, 1);
lean_inc_ref(v_buckets_2152_);
lean_dec(v_a_2117_);
v___x_2153_ = lean_mk_empty_array_with_capacity(v_size_2151_);
lean_dec(v_size_2151_);
v___x_2154_ = lean_array_get_size(v_buckets_2152_);
v___x_2155_ = lean_nat_dec_lt(v___x_2114_, v___x_2154_);
if (v___x_2155_ == 0)
{
lean_dec_ref(v_buckets_2152_);
v___y_2145_ = v___x_2153_;
goto v___jp_2144_;
}
else
{
uint8_t v___x_2156_; 
v___x_2156_ = lean_nat_dec_le(v___x_2154_, v___x_2154_);
if (v___x_2156_ == 0)
{
if (v___x_2155_ == 0)
{
lean_dec_ref(v_buckets_2152_);
v___y_2145_ = v___x_2153_;
goto v___jp_2144_;
}
else
{
size_t v___x_2157_; size_t v___x_2158_; lean_object* v___x_2159_; 
v___x_2157_ = ((size_t)0ULL);
v___x_2158_ = lean_usize_of_nat(v___x_2154_);
v___x_2159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_buckets_2152_, v___x_2157_, v___x_2158_, v___x_2153_);
lean_dec_ref(v_buckets_2152_);
v___y_2145_ = v___x_2159_;
goto v___jp_2144_;
}
}
else
{
size_t v___x_2160_; size_t v___x_2161_; lean_object* v___x_2162_; 
v___x_2160_ = ((size_t)0ULL);
v___x_2161_ = lean_usize_of_nat(v___x_2154_);
v___x_2162_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_buckets_2152_, v___x_2160_, v___x_2161_, v___x_2153_);
lean_dec_ref(v_buckets_2152_);
v___y_2145_ = v___x_2162_;
goto v___jp_2144_;
}
}
v___jp_2118_:
{
lean_object* v___x_2120_; size_t v_sz_2121_; size_t v___x_2122_; lean_object* v___x_2123_; 
v___x_2120_ = lean_box(0);
v_sz_2121_ = lean_array_size(v___y_2119_);
v___x_2122_ = ((size_t)0ULL);
v___x_2123_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(v___x_2107_, v___y_2119_, v_sz_2121_, v___x_2122_, v___x_2120_, v___y_2097_, v___y_2098_);
lean_dec_ref(v___y_2119_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2130_; 
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2130_ == 0)
{
lean_object* v_unused_2131_; 
v_unused_2131_ = lean_ctor_get(v___x_2123_, 0);
lean_dec(v_unused_2131_);
v___x_2125_ = v___x_2123_;
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
else
{
lean_dec(v___x_2123_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2128_; 
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 0, v___x_2120_);
v___x_2128_ = v___x_2125_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2120_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
else
{
return v___x_2123_;
}
}
v___jp_2132_:
{
lean_object* v___x_2137_; 
v___x_2137_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v___y_2135_, v___y_2134_, v___y_2133_, v___y_2136_);
lean_dec(v___y_2136_);
lean_dec(v___y_2135_);
v___y_2119_ = v___x_2137_;
goto v___jp_2118_;
}
v___jp_2138_:
{
uint8_t v___x_2143_; 
v___x_2143_ = lean_nat_dec_le(v___y_2142_, v___y_2139_);
if (v___x_2143_ == 0)
{
lean_dec(v___y_2139_);
lean_inc(v___y_2142_);
v___y_2133_ = v___y_2142_;
v___y_2134_ = v___y_2140_;
v___y_2135_ = v___y_2141_;
v___y_2136_ = v___y_2142_;
goto v___jp_2132_;
}
else
{
v___y_2133_ = v___y_2142_;
v___y_2134_ = v___y_2140_;
v___y_2135_ = v___y_2141_;
v___y_2136_ = v___y_2139_;
goto v___jp_2132_;
}
}
v___jp_2144_:
{
lean_object* v___x_2146_; uint8_t v___x_2147_; 
v___x_2146_ = lean_array_get_size(v___y_2145_);
v___x_2147_ = lean_nat_dec_eq(v___x_2146_, v___x_2114_);
if (v___x_2147_ == 0)
{
lean_object* v___x_2148_; lean_object* v___x_2149_; uint8_t v___x_2150_; 
v___x_2148_ = lean_unsigned_to_nat(1u);
v___x_2149_ = lean_nat_sub(v___x_2146_, v___x_2148_);
v___x_2150_ = lean_nat_dec_le(v___x_2114_, v___x_2149_);
if (v___x_2150_ == 0)
{
lean_inc(v___x_2149_);
v___y_2139_ = v___x_2149_;
v___y_2140_ = v___y_2145_;
v___y_2141_ = v___x_2146_;
v___y_2142_ = v___x_2149_;
goto v___jp_2138_;
}
else
{
v___y_2139_ = v___x_2149_;
v___y_2140_ = v___y_2145_;
v___y_2141_ = v___x_2146_;
v___y_2142_ = v___x_2114_;
goto v___jp_2138_;
}
}
else
{
v___y_2119_ = v___y_2145_;
goto v___jp_2118_;
}
}
}
else
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2170_; 
v_a_2163_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2165_ = v___x_2116_;
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2116_);
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
else
{
lean_object* v___x_2171_; lean_object* v___x_2173_; 
lean_dec(v_a_2109_);
v___x_2171_ = lean_box(0);
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 0, v___x_2171_);
v___x_2173_ = v___x_2111_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2171_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
else
{
goto v___jp_2100_;
}
}
else
{
lean_dec_ref_known(v___x_2105_, 1);
goto v___jp_2100_;
}
v___jp_2100_:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2101_ = lean_box(0);
v___x_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2101_);
return v___x_2102_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10___boxed(lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2176_, v___y_2177_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(lean_object* v_as_2180_, size_t v_sz_2181_, size_t v_i_2182_, lean_object* v_b_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
uint8_t v___x_2187_; 
v___x_2187_ = lean_usize_dec_lt(v_i_2182_, v_sz_2181_);
if (v___x_2187_ == 0)
{
lean_object* v___x_2188_; 
v___x_2188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2188_, 0, v_b_2183_);
return v___x_2188_;
}
else
{
lean_object* v_options_2189_; lean_object* v_a_2190_; lean_object* v___x_2191_; 
v_options_2189_ = lean_ctor_get(v___y_2184_, 2);
v_a_2190_ = lean_array_uget_borrowed(v_as_2180_, v_i_2182_);
lean_inc_ref(v_options_2189_);
lean_inc(v_a_2190_);
v___x_2191_ = l_Lean_Compiler_LCNF_resumeCompilation(v_a_2190_, v_options_2189_, v___y_2184_, v___y_2185_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v___x_2192_; 
lean_dec_ref_known(v___x_2191_, 1);
v___x_2192_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2184_, v___y_2185_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v___x_2193_; size_t v___x_2194_; size_t v___x_2195_; 
lean_dec_ref_known(v___x_2192_, 1);
v___x_2193_ = lean_box(0);
v___x_2194_ = ((size_t)1ULL);
v___x_2195_ = lean_usize_add(v_i_2182_, v___x_2194_);
v_i_2182_ = v___x_2195_;
v_b_2183_ = v___x_2193_;
goto _start;
}
else
{
return v___x_2192_;
}
}
else
{
lean_object* v_a_2197_; lean_object* v___x_2198_; 
v_a_2197_ = lean_ctor_get(v___x_2191_, 0);
lean_inc(v_a_2197_);
lean_dec_ref_known(v___x_2191_, 1);
v___x_2198_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2184_, v___y_2185_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2205_ == 0)
{
lean_object* v_unused_2206_; 
v_unused_2206_ = lean_ctor_get(v___x_2198_, 0);
lean_dec(v_unused_2206_);
v___x_2200_ = v___x_2198_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_dec(v___x_2198_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
lean_ctor_set_tag(v___x_2200_, 1);
lean_ctor_set(v___x_2200_, 0, v_a_2197_);
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2197_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
else
{
lean_dec(v_a_2197_);
return v___x_2198_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11___boxed(lean_object* v_as_2207_, lean_object* v_sz_2208_, lean_object* v_i_2209_, lean_object* v_b_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
size_t v_sz_boxed_2214_; size_t v_i_boxed_2215_; lean_object* v_res_2216_; 
v_sz_boxed_2214_ = lean_unbox_usize(v_sz_2208_);
lean_dec(v_sz_2208_);
v_i_boxed_2215_ = lean_unbox_usize(v_i_2209_);
lean_dec(v_i_2209_);
v_res_2216_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(v_as_2207_, v_sz_boxed_2214_, v_i_boxed_2215_, v_b_2210_, v___y_2211_, v___y_2212_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
lean_dec_ref(v_as_2207_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(lean_object* v_as_2217_, size_t v_sz_2218_, size_t v_i_2219_, lean_object* v_b_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
uint8_t v___x_2224_; 
v___x_2224_ = lean_usize_dec_lt(v_i_2219_, v_sz_2218_);
if (v___x_2224_ == 0)
{
lean_object* v___x_2225_; 
v___x_2225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2225_, 0, v_b_2220_);
return v___x_2225_;
}
else
{
lean_object* v_a_2226_; lean_object* v_declNames_2227_; lean_object* v___x_2228_; size_t v_sz_2229_; size_t v___x_2230_; lean_object* v___x_2231_; 
v_a_2226_ = lean_array_uget_borrowed(v_as_2217_, v_i_2219_);
v_declNames_2227_ = lean_ctor_get(v_a_2226_, 0);
v___x_2228_ = lean_box(0);
v_sz_2229_ = lean_array_size(v_declNames_2227_);
v___x_2230_ = ((size_t)0ULL);
v___x_2231_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(v_declNames_2227_, v_sz_2229_, v___x_2230_, v___x_2228_, v___y_2221_, v___y_2222_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v___x_2232_; 
lean_dec_ref_known(v___x_2231_, 1);
v___x_2232_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v___y_2222_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; lean_object* v_unreported_2234_; lean_object* v___x_2235_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2233_);
lean_dec_ref_known(v___x_2232_, 1);
v_unreported_2234_ = lean_ctor_get(v_a_2233_, 1);
lean_inc_ref(v_unreported_2234_);
lean_dec(v_a_2233_);
v___x_2235_ = l_Lean_PersistentArray_forIn___at___00main_spec__12(v_unreported_2234_, v___x_2228_, v___y_2221_, v___y_2222_);
lean_dec_ref(v_unreported_2234_);
if (lean_obj_tag(v___x_2235_) == 0)
{
size_t v___x_2236_; size_t v___x_2237_; 
lean_dec_ref_known(v___x_2235_, 1);
v___x_2236_ = ((size_t)1ULL);
v___x_2237_ = lean_usize_add(v_i_2219_, v___x_2236_);
v_i_2219_ = v___x_2237_;
v_b_2220_ = v___x_2228_;
goto _start;
}
else
{
return v___x_2235_;
}
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
v_a_2239_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2232_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2232_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2239_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
}
else
{
return v___x_2231_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13___boxed(lean_object* v_as_2247_, lean_object* v_sz_2248_, lean_object* v_i_2249_, lean_object* v_b_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
size_t v_sz_boxed_2254_; size_t v_i_boxed_2255_; lean_object* v_res_2256_; 
v_sz_boxed_2254_ = lean_unbox_usize(v_sz_2248_);
lean_dec(v_sz_2248_);
v_i_boxed_2255_ = lean_unbox_usize(v_i_2249_);
lean_dec(v_i_2249_);
v_res_2256_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(v_as_2247_, v_sz_boxed_2254_, v_i_boxed_2255_, v_b_2250_, v___y_2251_, v___y_2252_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec_ref(v_as_2247_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(lean_object* v_as_2257_, size_t v_i_2258_, size_t v_stop_2259_, lean_object* v_b_2260_){
_start:
{
uint8_t v___x_2261_; 
v___x_2261_ = lean_usize_dec_eq(v_i_2258_, v_stop_2259_);
if (v___x_2261_ == 0)
{
lean_object* v___x_2262_; lean_object* v_name_2263_; lean_object* v___x_2264_; size_t v___x_2265_; size_t v___x_2266_; 
v___x_2262_ = lean_array_uget_borrowed(v_as_2257_, v_i_2258_);
v_name_2263_ = lean_ctor_get(v___x_2262_, 0);
lean_inc(v_name_2263_);
v___x_2264_ = l_Lean_Compiler_LCNF_setDeclPublic(v_b_2260_, v_name_2263_);
v___x_2265_ = ((size_t)1ULL);
v___x_2266_ = lean_usize_add(v_i_2258_, v___x_2265_);
v_i_2258_ = v___x_2266_;
v_b_2260_ = v___x_2264_;
goto _start;
}
else
{
return v_b_2260_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___boxed(lean_object* v_as_2268_, lean_object* v_i_2269_, lean_object* v_stop_2270_, lean_object* v_b_2271_){
_start:
{
size_t v_i_boxed_2272_; size_t v_stop_boxed_2273_; lean_object* v_res_2274_; 
v_i_boxed_2272_ = lean_unbox_usize(v_i_2269_);
lean_dec(v_i_2269_);
v_stop_boxed_2273_ = lean_unbox_usize(v_stop_2270_);
lean_dec(v_stop_2270_);
v_res_2274_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v_as_2268_, v_i_boxed_2272_, v_stop_boxed_2273_, v_b_2271_);
lean_dec_ref(v_as_2268_);
return v_res_2274_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0(uint8_t v___y_2275_, uint8_t v_suppressElabErrors_2276_, lean_object* v_x_2277_){
_start:
{
if (lean_obj_tag(v_x_2277_) == 1)
{
lean_object* v_pre_2278_; 
v_pre_2278_ = lean_ctor_get(v_x_2277_, 0);
switch(lean_obj_tag(v_pre_2278_))
{
case 1:
{
lean_object* v_pre_2279_; 
v_pre_2279_ = lean_ctor_get(v_pre_2278_, 0);
switch(lean_obj_tag(v_pre_2279_))
{
case 0:
{
lean_object* v_str_2280_; lean_object* v_str_2281_; lean_object* v___x_2282_; uint8_t v___x_2283_; 
v_str_2280_ = lean_ctor_get(v_x_2277_, 1);
v_str_2281_ = lean_ctor_get(v_pre_2278_, 1);
v___x_2282_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0));
v___x_2283_ = lean_string_dec_eq(v_str_2281_, v___x_2282_);
if (v___x_2283_ == 0)
{
lean_object* v___x_2284_; uint8_t v___x_2285_; 
v___x_2284_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1));
v___x_2285_ = lean_string_dec_eq(v_str_2281_, v___x_2284_);
if (v___x_2285_ == 0)
{
return v___y_2275_;
}
else
{
lean_object* v___x_2286_; uint8_t v___x_2287_; 
v___x_2286_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2));
v___x_2287_ = lean_string_dec_eq(v_str_2280_, v___x_2286_);
if (v___x_2287_ == 0)
{
return v___y_2275_;
}
else
{
return v_suppressElabErrors_2276_;
}
}
}
else
{
lean_object* v___x_2288_; uint8_t v___x_2289_; 
v___x_2288_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3));
v___x_2289_ = lean_string_dec_eq(v_str_2280_, v___x_2288_);
if (v___x_2289_ == 0)
{
return v___y_2275_;
}
else
{
return v_suppressElabErrors_2276_;
}
}
}
case 1:
{
lean_object* v_pre_2290_; 
v_pre_2290_ = lean_ctor_get(v_pre_2279_, 0);
if (lean_obj_tag(v_pre_2290_) == 0)
{
lean_object* v_str_2291_; lean_object* v_str_2292_; lean_object* v_str_2293_; lean_object* v___x_2294_; uint8_t v___x_2295_; 
v_str_2291_ = lean_ctor_get(v_x_2277_, 1);
v_str_2292_ = lean_ctor_get(v_pre_2278_, 1);
v_str_2293_ = lean_ctor_get(v_pre_2279_, 1);
v___x_2294_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4));
v___x_2295_ = lean_string_dec_eq(v_str_2293_, v___x_2294_);
if (v___x_2295_ == 0)
{
return v___y_2275_;
}
else
{
lean_object* v___x_2296_; uint8_t v___x_2297_; 
v___x_2296_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5));
v___x_2297_ = lean_string_dec_eq(v_str_2292_, v___x_2296_);
if (v___x_2297_ == 0)
{
return v___y_2275_;
}
else
{
lean_object* v___x_2298_; uint8_t v___x_2299_; 
v___x_2298_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6));
v___x_2299_ = lean_string_dec_eq(v_str_2291_, v___x_2298_);
if (v___x_2299_ == 0)
{
return v___y_2275_;
}
else
{
return v_suppressElabErrors_2276_;
}
}
}
}
else
{
return v___y_2275_;
}
}
default: 
{
return v___y_2275_;
}
}
}
case 0:
{
lean_object* v_str_2300_; lean_object* v___x_2301_; uint8_t v___x_2302_; 
v_str_2300_ = lean_ctor_get(v_x_2277_, 1);
v___x_2301_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_2302_ = lean_string_dec_eq(v_str_2300_, v___x_2301_);
if (v___x_2302_ == 0)
{
return v___y_2275_;
}
else
{
return v_suppressElabErrors_2276_;
}
}
default: 
{
return v___y_2275_;
}
}
}
else
{
return v___y_2275_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0___boxed(lean_object* v___y_2303_, lean_object* v_suppressElabErrors_2304_, lean_object* v_x_2305_){
_start:
{
uint8_t v___y_38323__boxed_2306_; uint8_t v_suppressElabErrors_boxed_2307_; uint8_t v_res_2308_; lean_object* v_r_2309_; 
v___y_38323__boxed_2306_ = lean_unbox(v___y_2303_);
v_suppressElabErrors_boxed_2307_ = lean_unbox(v_suppressElabErrors_2304_);
v_res_2308_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0(v___y_38323__boxed_2306_, v_suppressElabErrors_boxed_2307_, v_x_2305_);
lean_dec(v_x_2305_);
v_r_2309_ = lean_box(v_res_2308_);
return v_r_2309_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(lean_object* v_ref_2310_, lean_object* v_msgData_2311_, uint8_t v_severity_2312_, uint8_t v_isSilent_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
uint8_t v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2323_; uint8_t v___y_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2354_; uint8_t v___y_2355_; lean_object* v___y_2356_; uint8_t v___y_2357_; lean_object* v___y_2358_; lean_object* v___y_2359_; uint8_t v___y_2360_; lean_object* v___y_2361_; lean_object* v___y_2379_; uint8_t v___y_2380_; lean_object* v___y_2381_; uint8_t v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; uint8_t v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2390_; uint8_t v___y_2391_; uint8_t v___y_2392_; lean_object* v___y_2393_; lean_object* v___y_2394_; lean_object* v___y_2395_; uint8_t v___y_2396_; uint8_t v___x_2401_; uint8_t v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; uint8_t v___y_2408_; uint8_t v___y_2409_; uint8_t v___y_2411_; uint8_t v___x_2426_; 
v___x_2401_ = 2;
v___x_2426_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2312_, v___x_2401_);
if (v___x_2426_ == 0)
{
v___y_2411_ = v___x_2426_;
goto v___jp_2410_;
}
else
{
uint8_t v___x_2427_; 
lean_inc_ref(v_msgData_2311_);
v___x_2427_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2311_);
v___y_2411_ = v___x_2427_;
goto v___jp_2410_;
}
v___jp_2317_:
{
lean_object* v___x_2327_; lean_object* v_currNamespace_2328_; lean_object* v_openDecls_2329_; lean_object* v_env_2330_; lean_object* v_nextMacroScope_2331_; lean_object* v_ngen_2332_; lean_object* v_auxDeclNGen_2333_; lean_object* v_traceState_2334_; lean_object* v_cache_2335_; lean_object* v_messages_2336_; lean_object* v_infoState_2337_; lean_object* v_snapshotTasks_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2352_; 
v___x_2327_ = lean_st_ref_take(v___y_2326_);
v_currNamespace_2328_ = lean_ctor_get(v___y_2325_, 6);
v_openDecls_2329_ = lean_ctor_get(v___y_2325_, 7);
v_env_2330_ = lean_ctor_get(v___x_2327_, 0);
v_nextMacroScope_2331_ = lean_ctor_get(v___x_2327_, 1);
v_ngen_2332_ = lean_ctor_get(v___x_2327_, 2);
v_auxDeclNGen_2333_ = lean_ctor_get(v___x_2327_, 3);
v_traceState_2334_ = lean_ctor_get(v___x_2327_, 4);
v_cache_2335_ = lean_ctor_get(v___x_2327_, 5);
v_messages_2336_ = lean_ctor_get(v___x_2327_, 6);
v_infoState_2337_ = lean_ctor_get(v___x_2327_, 7);
v_snapshotTasks_2338_ = lean_ctor_get(v___x_2327_, 8);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2340_ = v___x_2327_;
v_isShared_2341_ = v_isSharedCheck_2352_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_snapshotTasks_2338_);
lean_inc(v_infoState_2337_);
lean_inc(v_messages_2336_);
lean_inc(v_cache_2335_);
lean_inc(v_traceState_2334_);
lean_inc(v_auxDeclNGen_2333_);
lean_inc(v_ngen_2332_);
lean_inc(v_nextMacroScope_2331_);
lean_inc(v_env_2330_);
lean_dec(v___x_2327_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2352_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2347_; 
lean_inc(v_openDecls_2329_);
lean_inc(v_currNamespace_2328_);
v___x_2342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2342_, 0, v_currNamespace_2328_);
lean_ctor_set(v___x_2342_, 1, v_openDecls_2329_);
v___x_2343_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2342_);
lean_ctor_set(v___x_2343_, 1, v___y_2322_);
lean_inc_ref(v___y_2319_);
lean_inc_ref(v___y_2323_);
v___x_2344_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2344_, 0, v___y_2323_);
lean_ctor_set(v___x_2344_, 1, v___y_2321_);
lean_ctor_set(v___x_2344_, 2, v___y_2320_);
lean_ctor_set(v___x_2344_, 3, v___y_2319_);
lean_ctor_set(v___x_2344_, 4, v___x_2343_);
lean_ctor_set_uint8(v___x_2344_, sizeof(void*)*5, v___y_2318_);
lean_ctor_set_uint8(v___x_2344_, sizeof(void*)*5 + 1, v___y_2324_);
lean_ctor_set_uint8(v___x_2344_, sizeof(void*)*5 + 2, v_isSilent_2313_);
v___x_2345_ = l_Lean_MessageLog_add(v___x_2344_, v_messages_2336_);
if (v_isShared_2341_ == 0)
{
lean_ctor_set(v___x_2340_, 6, v___x_2345_);
v___x_2347_ = v___x_2340_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_env_2330_);
lean_ctor_set(v_reuseFailAlloc_2351_, 1, v_nextMacroScope_2331_);
lean_ctor_set(v_reuseFailAlloc_2351_, 2, v_ngen_2332_);
lean_ctor_set(v_reuseFailAlloc_2351_, 3, v_auxDeclNGen_2333_);
lean_ctor_set(v_reuseFailAlloc_2351_, 4, v_traceState_2334_);
lean_ctor_set(v_reuseFailAlloc_2351_, 5, v_cache_2335_);
lean_ctor_set(v_reuseFailAlloc_2351_, 6, v___x_2345_);
lean_ctor_set(v_reuseFailAlloc_2351_, 7, v_infoState_2337_);
lean_ctor_set(v_reuseFailAlloc_2351_, 8, v_snapshotTasks_2338_);
v___x_2347_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2348_ = lean_st_ref_set(v___y_2326_, v___x_2347_);
v___x_2349_ = lean_box(0);
v___x_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2349_);
return v___x_2350_;
}
}
}
v___jp_2353_:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2377_; 
v___x_2362_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2311_);
v___x_2363_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(v___x_2362_, v___y_2314_, v___y_2315_);
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2366_ = v___x_2363_;
v_isShared_2367_ = v_isSharedCheck_2377_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2363_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2377_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
lean_inc_ref_n(v___y_2359_, 2);
v___x_2368_ = l_Lean_FileMap_toPosition(v___y_2359_, v___y_2356_);
lean_dec(v___y_2356_);
v___x_2369_ = l_Lean_FileMap_toPosition(v___y_2359_, v___y_2361_);
lean_dec(v___y_2361_);
v___x_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2369_);
v___x_2371_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1));
if (v___y_2357_ == 0)
{
lean_del_object(v___x_2366_);
lean_dec_ref(v___y_2354_);
v___y_2318_ = v___y_2355_;
v___y_2319_ = v___x_2371_;
v___y_2320_ = v___x_2370_;
v___y_2321_ = v___x_2368_;
v___y_2322_ = v_a_2364_;
v___y_2323_ = v___y_2358_;
v___y_2324_ = v___y_2360_;
v___y_2325_ = v___y_2314_;
v___y_2326_ = v___y_2315_;
goto v___jp_2317_;
}
else
{
uint8_t v___x_2372_; 
lean_inc(v_a_2364_);
v___x_2372_ = l_Lean_MessageData_hasTag(v___y_2354_, v_a_2364_);
if (v___x_2372_ == 0)
{
lean_object* v___x_2373_; lean_object* v___x_2375_; 
lean_dec_ref_known(v___x_2370_, 1);
lean_dec_ref(v___x_2368_);
lean_dec(v_a_2364_);
v___x_2373_ = lean_box(0);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 0, v___x_2373_);
v___x_2375_ = v___x_2366_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2373_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
else
{
lean_del_object(v___x_2366_);
v___y_2318_ = v___y_2355_;
v___y_2319_ = v___x_2371_;
v___y_2320_ = v___x_2370_;
v___y_2321_ = v___x_2368_;
v___y_2322_ = v_a_2364_;
v___y_2323_ = v___y_2358_;
v___y_2324_ = v___y_2360_;
v___y_2325_ = v___y_2314_;
v___y_2326_ = v___y_2315_;
goto v___jp_2317_;
}
}
}
}
v___jp_2378_:
{
lean_object* v___x_2387_; 
v___x_2387_ = l_Lean_Syntax_getTailPos_x3f(v___y_2381_, v___y_2380_);
lean_dec(v___y_2381_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_inc(v___y_2386_);
v___y_2354_ = v___y_2379_;
v___y_2355_ = v___y_2380_;
v___y_2356_ = v___y_2386_;
v___y_2357_ = v___y_2382_;
v___y_2358_ = v___y_2383_;
v___y_2359_ = v___y_2384_;
v___y_2360_ = v___y_2385_;
v___y_2361_ = v___y_2386_;
goto v___jp_2353_;
}
else
{
lean_object* v_val_2388_; 
v_val_2388_ = lean_ctor_get(v___x_2387_, 0);
lean_inc(v_val_2388_);
lean_dec_ref_known(v___x_2387_, 1);
v___y_2354_ = v___y_2379_;
v___y_2355_ = v___y_2380_;
v___y_2356_ = v___y_2386_;
v___y_2357_ = v___y_2382_;
v___y_2358_ = v___y_2383_;
v___y_2359_ = v___y_2384_;
v___y_2360_ = v___y_2385_;
v___y_2361_ = v_val_2388_;
goto v___jp_2353_;
}
}
v___jp_2389_:
{
lean_object* v_ref_2397_; lean_object* v___x_2398_; 
v_ref_2397_ = l_Lean_replaceRef(v_ref_2310_, v___y_2394_);
v___x_2398_ = l_Lean_Syntax_getPos_x3f(v_ref_2397_, v___y_2391_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v___x_2399_; 
v___x_2399_ = lean_unsigned_to_nat(0u);
v___y_2379_ = v___y_2390_;
v___y_2380_ = v___y_2391_;
v___y_2381_ = v_ref_2397_;
v___y_2382_ = v___y_2392_;
v___y_2383_ = v___y_2393_;
v___y_2384_ = v___y_2395_;
v___y_2385_ = v___y_2396_;
v___y_2386_ = v___x_2399_;
goto v___jp_2378_;
}
else
{
lean_object* v_val_2400_; 
v_val_2400_ = lean_ctor_get(v___x_2398_, 0);
lean_inc(v_val_2400_);
lean_dec_ref_known(v___x_2398_, 1);
v___y_2379_ = v___y_2390_;
v___y_2380_ = v___y_2391_;
v___y_2381_ = v_ref_2397_;
v___y_2382_ = v___y_2392_;
v___y_2383_ = v___y_2393_;
v___y_2384_ = v___y_2395_;
v___y_2385_ = v___y_2396_;
v___y_2386_ = v_val_2400_;
goto v___jp_2378_;
}
}
v___jp_2402_:
{
if (v___y_2409_ == 0)
{
v___y_2390_ = v___y_2407_;
v___y_2391_ = v___y_2408_;
v___y_2392_ = v___y_2403_;
v___y_2393_ = v___y_2405_;
v___y_2394_ = v___y_2404_;
v___y_2395_ = v___y_2406_;
v___y_2396_ = v_severity_2312_;
goto v___jp_2389_;
}
else
{
v___y_2390_ = v___y_2407_;
v___y_2391_ = v___y_2408_;
v___y_2392_ = v___y_2403_;
v___y_2393_ = v___y_2405_;
v___y_2394_ = v___y_2404_;
v___y_2395_ = v___y_2406_;
v___y_2396_ = v___x_2401_;
goto v___jp_2389_;
}
}
v___jp_2410_:
{
if (v___y_2411_ == 0)
{
lean_object* v_fileName_2412_; lean_object* v_fileMap_2413_; lean_object* v_options_2414_; lean_object* v_ref_2415_; uint8_t v_suppressElabErrors_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___f_2419_; uint8_t v___x_2420_; uint8_t v___x_2421_; 
v_fileName_2412_ = lean_ctor_get(v___y_2314_, 0);
v_fileMap_2413_ = lean_ctor_get(v___y_2314_, 1);
v_options_2414_ = lean_ctor_get(v___y_2314_, 2);
v_ref_2415_ = lean_ctor_get(v___y_2314_, 5);
v_suppressElabErrors_2416_ = lean_ctor_get_uint8(v___y_2314_, sizeof(void*)*14 + 1);
v___x_2417_ = lean_box(v___y_2411_);
v___x_2418_ = lean_box(v_suppressElabErrors_2416_);
v___f_2419_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2419_, 0, v___x_2417_);
lean_closure_set(v___f_2419_, 1, v___x_2418_);
v___x_2420_ = 1;
v___x_2421_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2312_, v___x_2420_);
if (v___x_2421_ == 0)
{
v___y_2403_ = v_suppressElabErrors_2416_;
v___y_2404_ = v_ref_2415_;
v___y_2405_ = v_fileName_2412_;
v___y_2406_ = v_fileMap_2413_;
v___y_2407_ = v___f_2419_;
v___y_2408_ = v___y_2411_;
v___y_2409_ = v___x_2421_;
goto v___jp_2402_;
}
else
{
lean_object* v___x_2422_; uint8_t v___x_2423_; 
v___x_2422_ = l_Lean_warningAsError;
v___x_2423_ = l_Lean_Option_get___at___00main_spec__8(v_options_2414_, v___x_2422_);
v___y_2403_ = v_suppressElabErrors_2416_;
v___y_2404_ = v_ref_2415_;
v___y_2405_ = v_fileName_2412_;
v___y_2406_ = v_fileMap_2413_;
v___y_2407_ = v___f_2419_;
v___y_2408_ = v___y_2411_;
v___y_2409_ = v___x_2423_;
goto v___jp_2402_;
}
}
else
{
lean_object* v___x_2424_; lean_object* v___x_2425_; 
lean_dec_ref(v_msgData_2311_);
v___x_2424_ = lean_box(0);
v___x_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2424_);
return v___x_2425_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___boxed(lean_object* v_ref_2428_, lean_object* v_msgData_2429_, lean_object* v_severity_2430_, lean_object* v_isSilent_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
uint8_t v_severity_boxed_2435_; uint8_t v_isSilent_boxed_2436_; lean_object* v_res_2437_; 
v_severity_boxed_2435_ = lean_unbox(v_severity_2430_);
v_isSilent_boxed_2436_ = lean_unbox(v_isSilent_2431_);
v_res_2437_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(v_ref_2428_, v_msgData_2429_, v_severity_boxed_2435_, v_isSilent_boxed_2436_, v___y_2432_, v___y_2433_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
lean_dec(v_ref_2428_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(lean_object* v_msgData_2438_, uint8_t v_severity_2439_, uint8_t v_isSilent_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v_ref_2444_; lean_object* v___x_2445_; 
v_ref_2444_ = lean_ctor_get(v___y_2441_, 5);
v___x_2445_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(v_ref_2444_, v_msgData_2438_, v_severity_2439_, v_isSilent_2440_, v___y_2441_, v___y_2442_);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30___boxed(lean_object* v_msgData_2446_, lean_object* v_severity_2447_, lean_object* v_isSilent_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
uint8_t v_severity_boxed_2452_; uint8_t v_isSilent_boxed_2453_; lean_object* v_res_2454_; 
v_severity_boxed_2452_ = lean_unbox(v_severity_2447_);
v_isSilent_boxed_2453_ = lean_unbox(v_isSilent_2448_);
v_res_2454_ = l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(v_msgData_2446_, v_severity_boxed_2452_, v_isSilent_boxed_2453_, v___y_2449_, v___y_2450_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__14(lean_object* v_msgData_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
uint8_t v___x_2459_; uint8_t v___x_2460_; lean_object* v___x_2461_; 
v___x_2459_ = 2;
v___x_2460_ = 0;
v___x_2461_ = l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(v_msgData_2455_, v___x_2459_, v___x_2460_, v___y_2456_, v___y_2457_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__14___boxed(lean_object* v_msgData_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_Lean_logError___at___00main_spec__14(v_msgData_2462_, v___y_2463_, v___y_2464_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(lean_object* v_x2_2467_, lean_object* v_as_2468_, size_t v_i_2469_, size_t v_stop_2470_, lean_object* v_b_2471_){
_start:
{
uint8_t v___x_2472_; 
v___x_2472_ = lean_usize_dec_eq(v_i_2469_, v_stop_2470_);
if (v___x_2472_ == 0)
{
lean_object* v___x_2473_; lean_object* v___x_2474_; size_t v___x_2475_; size_t v___x_2476_; 
v___x_2473_ = lean_array_uget_borrowed(v_as_2468_, v_i_2469_);
lean_inc_ref(v_x2_2467_);
lean_inc(v___x_2473_);
v___x_2474_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2473_, v_x2_2467_, v_b_2471_);
v___x_2475_ = ((size_t)1ULL);
v___x_2476_ = lean_usize_add(v_i_2469_, v___x_2475_);
v_i_2469_ = v___x_2476_;
v_b_2471_ = v___x_2474_;
goto _start;
}
else
{
lean_dec_ref(v_x2_2467_);
return v_b_2471_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2___boxed(lean_object* v_x2_2478_, lean_object* v_as_2479_, lean_object* v_i_2480_, lean_object* v_stop_2481_, lean_object* v_b_2482_){
_start:
{
size_t v_i_boxed_2483_; size_t v_stop_boxed_2484_; lean_object* v_res_2485_; 
v_i_boxed_2483_ = lean_unbox_usize(v_i_2480_);
lean_dec(v_i_2480_);
v_stop_boxed_2484_ = lean_unbox_usize(v_stop_2481_);
lean_dec(v_stop_2481_);
v_res_2485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v_x2_2478_, v_as_2479_, v_i_boxed_2483_, v_stop_boxed_2484_, v_b_2482_);
lean_dec_ref(v_as_2479_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(lean_object* v_as_2486_, size_t v_i_2487_, size_t v_stop_2488_, lean_object* v_b_2489_){
_start:
{
lean_object* v___y_2491_; uint8_t v___x_2495_; 
v___x_2495_ = lean_usize_dec_eq(v_i_2487_, v_stop_2488_);
if (v___x_2495_ == 0)
{
lean_object* v___x_2496_; lean_object* v_declNames_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; uint8_t v___x_2500_; 
v___x_2496_ = lean_array_uget_borrowed(v_as_2486_, v_i_2487_);
v_declNames_2497_ = lean_ctor_get(v___x_2496_, 0);
v___x_2498_ = lean_unsigned_to_nat(0u);
v___x_2499_ = lean_array_get_size(v_declNames_2497_);
v___x_2500_ = lean_nat_dec_lt(v___x_2498_, v___x_2499_);
if (v___x_2500_ == 0)
{
v___y_2491_ = v_b_2489_;
goto v___jp_2490_;
}
else
{
uint8_t v___x_2501_; 
v___x_2501_ = lean_nat_dec_le(v___x_2499_, v___x_2499_);
if (v___x_2501_ == 0)
{
if (v___x_2500_ == 0)
{
v___y_2491_ = v_b_2489_;
goto v___jp_2490_;
}
else
{
size_t v___x_2502_; size_t v___x_2503_; lean_object* v___x_2504_; 
v___x_2502_ = ((size_t)0ULL);
v___x_2503_ = lean_usize_of_nat(v___x_2499_);
lean_inc(v___x_2496_);
v___x_2504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_2496_, v_declNames_2497_, v___x_2502_, v___x_2503_, v_b_2489_);
v___y_2491_ = v___x_2504_;
goto v___jp_2490_;
}
}
else
{
size_t v___x_2505_; size_t v___x_2506_; lean_object* v___x_2507_; 
v___x_2505_ = ((size_t)0ULL);
v___x_2506_ = lean_usize_of_nat(v___x_2499_);
lean_inc(v___x_2496_);
v___x_2507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_2496_, v_declNames_2497_, v___x_2505_, v___x_2506_, v_b_2489_);
v___y_2491_ = v___x_2507_;
goto v___jp_2490_;
}
}
}
else
{
return v_b_2489_;
}
v___jp_2490_:
{
size_t v___x_2492_; size_t v___x_2493_; 
v___x_2492_ = ((size_t)1ULL);
v___x_2493_ = lean_usize_add(v_i_2487_, v___x_2492_);
v_i_2487_ = v___x_2493_;
v_b_2489_ = v___y_2491_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___boxed(lean_object* v_as_2508_, lean_object* v_i_2509_, lean_object* v_stop_2510_, lean_object* v_b_2511_){
_start:
{
size_t v_i_boxed_2512_; size_t v_stop_boxed_2513_; lean_object* v_res_2514_; 
v_i_boxed_2512_ = lean_unbox_usize(v_i_2509_);
lean_dec(v_i_2509_);
v_stop_boxed_2513_ = lean_unbox_usize(v_stop_2510_);
lean_dec(v_stop_2510_);
v_res_2514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v_as_2508_, v_i_boxed_2512_, v_stop_boxed_2513_, v_b_2511_);
lean_dec_ref(v_as_2508_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(lean_object* v_a_2515_, lean_object* v_as_2516_, size_t v_i_2517_, size_t v_stop_2518_, lean_object* v_b_2519_){
_start:
{
lean_object* v___y_2521_; uint8_t v___x_2525_; 
v___x_2525_ = lean_usize_dec_eq(v_i_2517_, v_stop_2518_);
if (v___x_2525_ == 0)
{
lean_object* v___x_2526_; lean_object* v_name_2527_; uint8_t v___x_2528_; 
v___x_2526_ = lean_array_uget_borrowed(v_as_2516_, v_i_2517_);
v_name_2527_ = lean_ctor_get(v___x_2526_, 0);
lean_inc(v_name_2527_);
lean_inc_ref(v_a_2515_);
v___x_2528_ = l_Lean_isExtern(v_a_2515_, v_name_2527_);
if (v___x_2528_ == 0)
{
v___y_2521_ = v_b_2519_;
goto v___jp_2520_;
}
else
{
lean_object* v___x_2529_; 
lean_inc(v___x_2526_);
v___x_2529_ = lean_array_push(v_b_2519_, v___x_2526_);
v___y_2521_ = v___x_2529_;
goto v___jp_2520_;
}
}
else
{
lean_dec_ref(v_a_2515_);
return v_b_2519_;
}
v___jp_2520_:
{
size_t v___x_2522_; size_t v___x_2523_; 
v___x_2522_ = ((size_t)1ULL);
v___x_2523_ = lean_usize_add(v_i_2517_, v___x_2522_);
v_i_2517_ = v___x_2523_;
v_b_2519_ = v___y_2521_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19___boxed(lean_object* v_a_2530_, lean_object* v_as_2531_, lean_object* v_i_2532_, lean_object* v_stop_2533_, lean_object* v_b_2534_){
_start:
{
size_t v_i_boxed_2535_; size_t v_stop_boxed_2536_; lean_object* v_res_2537_; 
v_i_boxed_2535_ = lean_unbox_usize(v_i_2532_);
lean_dec(v_i_2532_);
v_stop_boxed_2536_ = lean_unbox_usize(v_stop_2533_);
lean_dec(v_stop_2533_);
v_res_2537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_2530_, v_as_2531_, v_i_boxed_2535_, v_stop_boxed_2536_, v_b_2534_);
lean_dec_ref(v_as_2531_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(lean_object* v_as_2538_, size_t v_sz_2539_, size_t v_i_2540_, lean_object* v_b_2541_){
_start:
{
uint8_t v___x_2543_; 
v___x_2543_ = lean_usize_dec_lt(v_i_2540_, v_sz_2539_);
if (v___x_2543_ == 0)
{
lean_object* v___x_2544_; 
v___x_2544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2544_, 0, v_b_2541_);
return v___x_2544_;
}
else
{
uint8_t v___x_2545_; lean_object* v_a_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
lean_dec_ref(v_b_2541_);
v___x_2545_ = 0;
v_a_2546_ = lean_array_uget_borrowed(v_as_2538_, v_i_2540_);
lean_inc(v_a_2546_);
v___x_2547_ = l_Lean_Message_toString(v_a_2546_, v___x_2545_);
v___x_2548_ = l_IO_eprintln___at___00main_spec__6(v___x_2547_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v___x_2549_; size_t v___x_2550_; size_t v___x_2551_; 
lean_dec_ref_known(v___x_2548_, 1);
v___x_2549_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_2550_ = ((size_t)1ULL);
v___x_2551_ = lean_usize_add(v_i_2540_, v___x_2550_);
v_i_2540_ = v___x_2551_;
v_b_2541_ = v___x_2549_;
goto _start;
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
v_a_2553_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v___x_2548_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2548_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2558_; 
if (v_isShared_2556_ == 0)
{
v___x_2558_ = v___x_2555_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_a_2553_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27___boxed(lean_object* v_as_2561_, lean_object* v_sz_2562_, lean_object* v_i_2563_, lean_object* v_b_2564_, lean_object* v___y_2565_){
_start:
{
size_t v_sz_boxed_2566_; size_t v_i_boxed_2567_; lean_object* v_res_2568_; 
v_sz_boxed_2566_ = lean_unbox_usize(v_sz_2562_);
lean_dec(v_sz_2562_);
v_i_boxed_2567_ = lean_unbox_usize(v_i_2563_);
lean_dec(v_i_2563_);
v_res_2568_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(v_as_2561_, v_sz_boxed_2566_, v_i_boxed_2567_, v_b_2564_);
lean_dec_ref(v_as_2561_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(lean_object* v_as_2569_, size_t v_sz_2570_, size_t v_i_2571_, lean_object* v_b_2572_){
_start:
{
uint8_t v___x_2574_; 
v___x_2574_ = lean_usize_dec_lt(v_i_2571_, v_sz_2570_);
if (v___x_2574_ == 0)
{
lean_object* v___x_2575_; 
v___x_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2575_, 0, v_b_2572_);
return v___x_2575_;
}
else
{
uint8_t v___x_2576_; lean_object* v_a_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
lean_dec_ref(v_b_2572_);
v___x_2576_ = 0;
v_a_2577_ = lean_array_uget_borrowed(v_as_2569_, v_i_2571_);
lean_inc(v_a_2577_);
v___x_2578_ = l_Lean_Message_toString(v_a_2577_, v___x_2576_);
v___x_2579_ = l_IO_eprintln___at___00main_spec__6(v___x_2578_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v___x_2580_; size_t v___x_2581_; size_t v___x_2582_; lean_object* v___x_2583_; 
lean_dec_ref_known(v___x_2579_, 1);
v___x_2580_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_2581_ = ((size_t)1ULL);
v___x_2582_ = lean_usize_add(v_i_2571_, v___x_2581_);
v___x_2583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(v_as_2569_, v_sz_2570_, v___x_2582_, v___x_2580_);
return v___x_2583_;
}
else
{
lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2591_; 
v_a_2584_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2586_ = v___x_2579_;
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v___x_2579_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2589_; 
if (v_isShared_2587_ == 0)
{
v___x_2589_ = v___x_2586_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_a_2584_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14___boxed(lean_object* v_as_2592_, lean_object* v_sz_2593_, lean_object* v_i_2594_, lean_object* v_b_2595_, lean_object* v___y_2596_){
_start:
{
size_t v_sz_boxed_2597_; size_t v_i_boxed_2598_; lean_object* v_res_2599_; 
v_sz_boxed_2597_ = lean_unbox_usize(v_sz_2593_);
lean_dec(v_sz_2593_);
v_i_boxed_2598_ = lean_unbox_usize(v_i_2594_);
lean_dec(v_i_2594_);
v_res_2599_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(v_as_2592_, v_sz_boxed_2597_, v_i_boxed_2598_, v_b_2595_);
lean_dec_ref(v_as_2592_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(lean_object* v_init_2600_, lean_object* v_n_2601_, lean_object* v_b_2602_){
_start:
{
if (lean_obj_tag(v_n_2601_) == 0)
{
lean_object* v_cs_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; size_t v_sz_2607_; size_t v___x_2608_; lean_object* v___x_2609_; 
v_cs_2604_ = lean_ctor_get(v_n_2601_, 0);
v___x_2605_ = lean_box(0);
v___x_2606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2605_);
lean_ctor_set(v___x_2606_, 1, v_b_2602_);
v_sz_2607_ = lean_array_size(v_cs_2604_);
v___x_2608_ = ((size_t)0ULL);
v___x_2609_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_init_2600_, v_cs_2604_, v_sz_2607_, v___x_2608_, v___x_2606_);
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2624_; 
v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2612_ = v___x_2609_;
v_isShared_2613_ = v_isSharedCheck_2624_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2609_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2624_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v_fst_2614_; 
v_fst_2614_ = lean_ctor_get(v_a_2610_, 0);
if (lean_obj_tag(v_fst_2614_) == 0)
{
lean_object* v_snd_2615_; lean_object* v___x_2616_; lean_object* v___x_2618_; 
v_snd_2615_ = lean_ctor_get(v_a_2610_, 1);
lean_inc(v_snd_2615_);
lean_dec(v_a_2610_);
v___x_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2616_, 0, v_snd_2615_);
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 0, v___x_2616_);
v___x_2618_ = v___x_2612_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2616_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
else
{
lean_object* v_val_2620_; lean_object* v___x_2622_; 
lean_inc_ref(v_fst_2614_);
lean_dec(v_a_2610_);
v_val_2620_ = lean_ctor_get(v_fst_2614_, 0);
lean_inc(v_val_2620_);
lean_dec_ref_known(v_fst_2614_, 1);
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 0, v_val_2620_);
v___x_2622_ = v___x_2612_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_val_2620_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
v_a_2625_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2609_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2609_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
else
{
lean_object* v_vs_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; size_t v_sz_2636_; size_t v___x_2637_; lean_object* v___x_2638_; 
v_vs_2633_ = lean_ctor_get(v_n_2601_, 0);
v___x_2634_ = lean_box(0);
v___x_2635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2634_);
lean_ctor_set(v___x_2635_, 1, v_b_2602_);
v_sz_2636_ = lean_array_size(v_vs_2633_);
v___x_2637_ = ((size_t)0ULL);
v___x_2638_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(v_vs_2633_, v_sz_2636_, v___x_2637_, v___x_2635_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2653_; 
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2641_ = v___x_2638_;
v_isShared_2642_ = v_isSharedCheck_2653_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2638_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2653_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v_fst_2643_; 
v_fst_2643_ = lean_ctor_get(v_a_2639_, 0);
if (lean_obj_tag(v_fst_2643_) == 0)
{
lean_object* v_snd_2644_; lean_object* v___x_2645_; lean_object* v___x_2647_; 
v_snd_2644_ = lean_ctor_get(v_a_2639_, 1);
lean_inc(v_snd_2644_);
lean_dec(v_a_2639_);
v___x_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2645_, 0, v_snd_2644_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 0, v___x_2645_);
v___x_2647_ = v___x_2641_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v___x_2645_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
else
{
lean_object* v_val_2649_; lean_object* v___x_2651_; 
lean_inc_ref(v_fst_2643_);
lean_dec(v_a_2639_);
v_val_2649_ = lean_ctor_get(v_fst_2643_, 0);
lean_inc(v_val_2649_);
lean_dec_ref_known(v_fst_2643_, 1);
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 0, v_val_2649_);
v___x_2651_ = v___x_2641_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_val_2649_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
v_a_2654_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2656_ = v___x_2638_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2638_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(lean_object* v_init_2662_, lean_object* v_as_2663_, size_t v_sz_2664_, size_t v_i_2665_, lean_object* v_b_2666_){
_start:
{
uint8_t v___x_2668_; 
v___x_2668_ = lean_usize_dec_lt(v_i_2665_, v_sz_2664_);
if (v___x_2668_ == 0)
{
lean_object* v___x_2669_; 
v___x_2669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2669_, 0, v_b_2666_);
return v___x_2669_;
}
else
{
lean_object* v_snd_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2704_; 
v_snd_2670_ = lean_ctor_get(v_b_2666_, 1);
v_isSharedCheck_2704_ = !lean_is_exclusive(v_b_2666_);
if (v_isSharedCheck_2704_ == 0)
{
lean_object* v_unused_2705_; 
v_unused_2705_ = lean_ctor_get(v_b_2666_, 0);
lean_dec(v_unused_2705_);
v___x_2672_ = v_b_2666_;
v_isShared_2673_ = v_isSharedCheck_2704_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_snd_2670_);
lean_dec(v_b_2666_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2704_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v_a_2674_; lean_object* v___x_2675_; 
v_a_2674_ = lean_array_uget_borrowed(v_as_2663_, v_i_2665_);
lean_inc(v_snd_2670_);
v___x_2675_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2662_, v_a_2674_, v_snd_2670_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2695_; 
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2678_ = v___x_2675_;
v_isShared_2679_ = v_isSharedCheck_2695_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2675_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2695_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
if (lean_obj_tag(v_a_2676_) == 0)
{
lean_object* v___x_2680_; lean_object* v___x_2682_; 
v___x_2680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2680_, 0, v_a_2676_);
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 0, v___x_2680_);
v___x_2682_ = v___x_2672_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v___x_2680_);
lean_ctor_set(v_reuseFailAlloc_2686_, 1, v_snd_2670_);
v___x_2682_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
lean_object* v___x_2684_; 
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 0, v___x_2682_);
v___x_2684_ = v___x_2678_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v___x_2682_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
else
{
lean_object* v_a_2687_; lean_object* v___x_2688_; lean_object* v___x_2690_; 
lean_del_object(v___x_2678_);
lean_dec(v_snd_2670_);
v_a_2687_ = lean_ctor_get(v_a_2676_, 0);
lean_inc(v_a_2687_);
lean_dec_ref_known(v_a_2676_, 1);
v___x_2688_ = lean_box(0);
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 1, v_a_2687_);
lean_ctor_set(v___x_2672_, 0, v___x_2688_);
v___x_2690_ = v___x_2672_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2688_);
lean_ctor_set(v_reuseFailAlloc_2694_, 1, v_a_2687_);
v___x_2690_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
size_t v___x_2691_; size_t v___x_2692_; 
v___x_2691_ = ((size_t)1ULL);
v___x_2692_ = lean_usize_add(v_i_2665_, v___x_2691_);
v_i_2665_ = v___x_2692_;
v_b_2666_ = v___x_2690_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2703_; 
lean_del_object(v___x_2672_);
lean_dec(v_snd_2670_);
v_a_2696_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2698_ = v___x_2675_;
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2675_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2701_; 
if (v_isShared_2699_ == 0)
{
v___x_2701_ = v___x_2698_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2696_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13___boxed(lean_object* v_init_2706_, lean_object* v_as_2707_, lean_object* v_sz_2708_, lean_object* v_i_2709_, lean_object* v_b_2710_, lean_object* v___y_2711_){
_start:
{
size_t v_sz_boxed_2712_; size_t v_i_boxed_2713_; lean_object* v_res_2714_; 
v_sz_boxed_2712_ = lean_unbox_usize(v_sz_2708_);
lean_dec(v_sz_2708_);
v_i_boxed_2713_ = lean_unbox_usize(v_i_2709_);
lean_dec(v_i_2709_);
v_res_2714_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_init_2706_, v_as_2707_, v_sz_boxed_2712_, v_i_boxed_2713_, v_b_2710_);
lean_dec_ref(v_as_2707_);
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10___boxed(lean_object* v_init_2715_, lean_object* v_n_2716_, lean_object* v_b_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2715_, v_n_2716_, v_b_2717_);
lean_dec_ref(v_n_2716_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(lean_object* v_as_2720_, size_t v_sz_2721_, size_t v_i_2722_, lean_object* v_b_2723_){
_start:
{
uint8_t v___x_2725_; 
v___x_2725_ = lean_usize_dec_lt(v_i_2722_, v_sz_2721_);
if (v___x_2725_ == 0)
{
lean_object* v___x_2726_; 
v___x_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2726_, 0, v_b_2723_);
return v___x_2726_;
}
else
{
uint8_t v___x_2727_; lean_object* v_a_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
lean_dec_ref(v_b_2723_);
v___x_2727_ = 0;
v_a_2728_ = lean_array_uget_borrowed(v_as_2720_, v_i_2722_);
lean_inc(v_a_2728_);
v___x_2729_ = l_Lean_Message_toString(v_a_2728_, v___x_2727_);
v___x_2730_ = l_IO_eprintln___at___00main_spec__6(v___x_2729_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v___x_2731_; size_t v___x_2732_; size_t v___x_2733_; 
lean_dec_ref_known(v___x_2730_, 1);
v___x_2731_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_2732_ = ((size_t)1ULL);
v___x_2733_ = lean_usize_add(v_i_2722_, v___x_2732_);
v_i_2722_ = v___x_2733_;
v_b_2723_ = v___x_2731_;
goto _start;
}
else
{
lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2742_; 
v_a_2735_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2737_ = v___x_2730_;
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___x_2730_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2740_; 
if (v_isShared_2738_ == 0)
{
v___x_2740_ = v___x_2737_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_a_2735_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16___boxed(lean_object* v_as_2743_, lean_object* v_sz_2744_, lean_object* v_i_2745_, lean_object* v_b_2746_, lean_object* v___y_2747_){
_start:
{
size_t v_sz_boxed_2748_; size_t v_i_boxed_2749_; lean_object* v_res_2750_; 
v_sz_boxed_2748_ = lean_unbox_usize(v_sz_2744_);
lean_dec(v_sz_2744_);
v_i_boxed_2749_ = lean_unbox_usize(v_i_2745_);
lean_dec(v_i_2745_);
v_res_2750_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(v_as_2743_, v_sz_boxed_2748_, v_i_boxed_2749_, v_b_2746_);
lean_dec_ref(v_as_2743_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(lean_object* v_as_2751_, size_t v_sz_2752_, size_t v_i_2753_, lean_object* v_b_2754_){
_start:
{
uint8_t v___x_2756_; 
v___x_2756_ = lean_usize_dec_lt(v_i_2753_, v_sz_2752_);
if (v___x_2756_ == 0)
{
lean_object* v___x_2757_; 
v___x_2757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2757_, 0, v_b_2754_);
return v___x_2757_;
}
else
{
uint8_t v___x_2758_; lean_object* v_a_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; 
lean_dec_ref(v_b_2754_);
v___x_2758_ = 0;
v_a_2759_ = lean_array_uget_borrowed(v_as_2751_, v_i_2753_);
lean_inc(v_a_2759_);
v___x_2760_ = l_Lean_Message_toString(v_a_2759_, v___x_2758_);
v___x_2761_ = l_IO_eprintln___at___00main_spec__6(v___x_2760_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v___x_2762_; size_t v___x_2763_; size_t v___x_2764_; lean_object* v___x_2765_; 
lean_dec_ref_known(v___x_2761_, 1);
v___x_2762_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_2763_ = ((size_t)1ULL);
v___x_2764_ = lean_usize_add(v_i_2753_, v___x_2763_);
v___x_2765_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(v_as_2751_, v_sz_2752_, v___x_2764_, v___x_2762_);
return v___x_2765_;
}
else
{
lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2773_; 
v_a_2766_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2768_ = v___x_2761_;
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_dec(v___x_2761_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2771_; 
if (v_isShared_2769_ == 0)
{
v___x_2771_ = v___x_2768_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_a_2766_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11___boxed(lean_object* v_as_2774_, lean_object* v_sz_2775_, lean_object* v_i_2776_, lean_object* v_b_2777_, lean_object* v___y_2778_){
_start:
{
size_t v_sz_boxed_2779_; size_t v_i_boxed_2780_; lean_object* v_res_2781_; 
v_sz_boxed_2779_ = lean_unbox_usize(v_sz_2775_);
lean_dec(v_sz_2775_);
v_i_boxed_2780_ = lean_unbox_usize(v_i_2776_);
lean_dec(v_i_2776_);
v_res_2781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_as_2774_, v_sz_boxed_2779_, v_i_boxed_2780_, v_b_2777_);
lean_dec_ref(v_as_2774_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7(lean_object* v_t_2782_, lean_object* v_init_2783_){
_start:
{
lean_object* v_root_2785_; lean_object* v_tail_2786_; lean_object* v___x_2787_; 
v_root_2785_ = lean_ctor_get(v_t_2782_, 0);
v_tail_2786_ = lean_ctor_get(v_t_2782_, 1);
v___x_2787_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2783_, v_root_2785_, v_init_2783_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2824_; 
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2790_ = v___x_2787_;
v_isShared_2791_ = v_isSharedCheck_2824_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2787_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2824_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
if (lean_obj_tag(v_a_2788_) == 0)
{
lean_object* v_a_2792_; lean_object* v___x_2794_; 
v_a_2792_ = lean_ctor_get(v_a_2788_, 0);
lean_inc(v_a_2792_);
lean_dec_ref_known(v_a_2788_, 1);
if (v_isShared_2791_ == 0)
{
lean_ctor_set(v___x_2790_, 0, v_a_2792_);
v___x_2794_ = v___x_2790_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_a_2792_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; size_t v_sz_2799_; size_t v___x_2800_; lean_object* v___x_2801_; 
lean_del_object(v___x_2790_);
v_a_2796_ = lean_ctor_get(v_a_2788_, 0);
lean_inc(v_a_2796_);
lean_dec_ref_known(v_a_2788_, 1);
v___x_2797_ = lean_box(0);
v___x_2798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2797_);
lean_ctor_set(v___x_2798_, 1, v_a_2796_);
v_sz_2799_ = lean_array_size(v_tail_2786_);
v___x_2800_ = ((size_t)0ULL);
v___x_2801_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_tail_2786_, v_sz_2799_, v___x_2800_, v___x_2798_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2815_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2804_ = v___x_2801_;
v_isShared_2805_ = v_isSharedCheck_2815_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2801_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2815_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v_fst_2806_; 
v_fst_2806_ = lean_ctor_get(v_a_2802_, 0);
if (lean_obj_tag(v_fst_2806_) == 0)
{
lean_object* v_snd_2807_; lean_object* v___x_2809_; 
v_snd_2807_ = lean_ctor_get(v_a_2802_, 1);
lean_inc(v_snd_2807_);
lean_dec(v_a_2802_);
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 0, v_snd_2807_);
v___x_2809_ = v___x_2804_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_snd_2807_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
else
{
lean_object* v_val_2811_; lean_object* v___x_2813_; 
lean_inc_ref(v_fst_2806_);
lean_dec(v_a_2802_);
v_val_2811_ = lean_ctor_get(v_fst_2806_, 0);
lean_inc(v_val_2811_);
lean_dec_ref_known(v_fst_2806_, 1);
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 0, v_val_2811_);
v___x_2813_ = v___x_2804_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_val_2811_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
}
else
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
v_a_2816_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___x_2801_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2801_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2816_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
}
}
}
else
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
v_a_2825_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2827_ = v___x_2787_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2787_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2830_; 
if (v_isShared_2828_ == 0)
{
v___x_2830_ = v___x_2827_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2825_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7___boxed(lean_object* v_t_2833_, lean_object* v_init_2834_, lean_object* v___y_2835_){
_start:
{
lean_object* v_res_2836_; 
v_res_2836_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_t_2833_, v_init_2834_);
lean_dec_ref(v_t_2833_);
return v_res_2836_;
}
}
static lean_object* _init_l_main___closed__3(void){
_start:
{
lean_object* v___x_2840_; 
v___x_2840_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(lean_box(0), lean_box(0), lean_box(0));
return v___x_2840_;
}
}
static lean_object* _init_l_main___closed__4(void){
_start:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; 
v___x_2841_ = l_Lean_instInhabitedClassState_default;
v___x_2842_ = lean_box(0);
v___x_2843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2842_);
lean_ctor_set(v___x_2843_, 1, v___x_2841_);
return v___x_2843_;
}
}
static lean_object* _init_l_main___closed__5(void){
_start:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2844_ = l_Lean_Meta_Match_Extension_instInhabitedState;
v___x_2845_ = lean_box(0);
v___x_2846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2845_);
lean_ctor_set(v___x_2846_, 1, v___x_2844_);
return v___x_2846_;
}
}
static lean_object* _init_l_main___closed__6(void){
_start:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2847_ = ((lean_object*)(l_main___closed__2));
v___x_2848_ = ((lean_object*)(l_main___closed__1));
v___x_2849_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_2848_, v___x_2847_);
return v___x_2849_;
}
}
static lean_object* _init_l_main___closed__7(void){
_start:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2850_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_2851_ = lean_box(0);
v___x_2852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2851_);
lean_ctor_set(v___x_2852_, 1, v___x_2850_);
return v___x_2852_;
}
}
static lean_object* _init_l_main___closed__8(void){
_start:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2853_ = lean_obj_once(&l_main___closed__7, &l_main___closed__7_once, _init_l_main___closed__7);
v___x_2854_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2853_);
return v___x_2854_;
}
}
static lean_object* _init_l_main___closed__9(void){
_start:
{
lean_object* v___x_2855_; 
v___x_2855_ = l_Array_instInhabited(lean_box(0));
return v___x_2855_;
}
}
static lean_object* _init_l_main___closed__15(void){
_start:
{
lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2864_ = l_Lean_Options_empty;
v___x_2865_ = l_Lean_Core_getMaxHeartbeats(v___x_2864_);
return v___x_2865_;
}
}
static lean_object* _init_l_main___closed__20(void){
_start:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2870_ = ((lean_object*)(l_main___closed__19));
v___x_2871_ = lean_unsigned_to_nat(27u);
v___x_2872_ = lean_unsigned_to_nat(149u);
v___x_2873_ = ((lean_object*)(l_main___closed__18));
v___x_2874_ = ((lean_object*)(l_main___closed__17));
v___x_2875_ = l_mkPanicMessageWithDecl(v___x_2874_, v___x_2873_, v___x_2872_, v___x_2871_, v___x_2870_);
return v___x_2875_;
}
}
static lean_object* _init_l_main___closed__22(void){
_start:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2877_ = ((lean_object*)(l_main___closed__19));
v___x_2878_ = lean_unsigned_to_nat(51u);
v___x_2879_ = lean_unsigned_to_nat(122u);
v___x_2880_ = ((lean_object*)(l_main___closed__18));
v___x_2881_ = ((lean_object*)(l_main___closed__17));
v___x_2882_ = l_mkPanicMessageWithDecl(v___x_2881_, v___x_2880_, v___x_2879_, v___x_2878_, v___x_2877_);
return v___x_2882_;
}
}
static lean_object* _init_l_main___closed__23(void){
_start:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2883_ = lean_unsigned_to_nat(1u);
v___x_2884_ = l_Lean_firstFrontendMacroScope;
v___x_2885_ = lean_nat_add(v___x_2884_, v___x_2883_);
return v___x_2885_;
}
}
static lean_object* _init_l_main___closed__27(void){
_start:
{
lean_object* v___x_2892_; uint64_t v___x_2893_; lean_object* v___x_2894_; 
v___x_2892_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2893_ = 0ULL;
v___x_2894_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2894_, 0, v___x_2892_);
lean_ctor_set_uint64(v___x_2894_, sizeof(void*)*1, v___x_2893_);
return v___x_2894_;
}
}
static lean_object* _init_l_main___closed__28(void){
_start:
{
lean_object* v___x_2895_; 
v___x_2895_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2895_;
}
}
static lean_object* _init_l_main___closed__29(void){
_start:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2896_ = lean_obj_once(&l_main___closed__28, &l_main___closed__28_once, _init_l_main___closed__28);
v___x_2897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2896_);
return v___x_2897_;
}
}
static lean_object* _init_l_main___closed__30(void){
_start:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2898_ = lean_obj_once(&l_main___closed__29, &l_main___closed__29_once, _init_l_main___closed__29);
v___x_2899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2898_);
lean_ctor_set(v___x_2899_, 1, v___x_2898_);
return v___x_2899_;
}
}
static lean_object* _init_l_main___closed__31(void){
_start:
{
lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2900_ = l_Lean_NameSet_empty;
v___x_2901_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2902_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2901_);
lean_ctor_set(v___x_2902_, 1, v___x_2901_);
lean_ctor_set(v___x_2902_, 2, v___x_2900_);
return v___x_2902_;
}
}
static lean_object* _init_l_main___closed__32(void){
_start:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; uint8_t v___x_2905_; lean_object* v___x_2906_; 
v___x_2903_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2904_ = lean_obj_once(&l_main___closed__29, &l_main___closed__29_once, _init_l_main___closed__29);
v___x_2905_ = 1;
v___x_2906_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2906_, 0, v___x_2904_);
lean_ctor_set(v___x_2906_, 1, v___x_2904_);
lean_ctor_set(v___x_2906_, 2, v___x_2903_);
lean_ctor_set_uint8(v___x_2906_, sizeof(void*)*3, v___x_2905_);
return v___x_2906_;
}
}
static uint8_t _init_l_main___closed__37(void){
_start:
{
uint8_t v___x_2913_; uint8_t v___x_2914_; uint8_t v___x_2915_; 
v___x_2913_ = 2;
v___x_2914_ = 0;
v___x_2915_ = l_Lean_instOrdOLeanLevel_ord(v___x_2914_, v___x_2913_);
return v___x_2915_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_2916_; lean_object* v___x_2917_; 
v___x_2916_ = 1;
v___x_2917_ = lean_box_uint32(v___x_2916_);
return v___x_2917_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_2918_; lean_object* v___x_2919_; 
v___x_2918_ = 0;
v___x_2919_ = lean_box_uint32(v___x_2918_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_2920_){
_start:
{
if (lean_obj_tag(v_args_2920_) == 1)
{
lean_object* v_tail_2945_; 
v_tail_2945_ = lean_ctor_get(v_args_2920_, 1);
lean_inc(v_tail_2945_);
if (lean_obj_tag(v_tail_2945_) == 1)
{
lean_object* v_tail_2946_; 
v_tail_2946_ = lean_ctor_get(v_tail_2945_, 1);
lean_inc(v_tail_2946_);
if (lean_obj_tag(v_tail_2946_) == 1)
{
lean_object* v_head_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_3594_; 
v_head_2947_ = lean_ctor_get(v_args_2920_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v_args_2920_);
if (v_isSharedCheck_3594_ == 0)
{
lean_object* v_unused_3595_; 
v_unused_3595_ = lean_ctor_get(v_args_2920_, 1);
lean_dec(v_unused_3595_);
v___x_2949_ = v_args_2920_;
v_isShared_2950_ = v_isSharedCheck_3594_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_head_2947_);
lean_dec(v_args_2920_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_3594_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v_head_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_3592_; 
v_head_2951_ = lean_ctor_get(v_tail_2945_, 0);
v_isSharedCheck_3592_ = !lean_is_exclusive(v_tail_2945_);
if (v_isSharedCheck_3592_ == 0)
{
lean_object* v_unused_3593_; 
v_unused_3593_ = lean_ctor_get(v_tail_2945_, 1);
lean_dec(v_unused_3593_);
v___x_2953_ = v_tail_2945_;
v_isShared_2954_ = v_isSharedCheck_3592_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_head_2951_);
lean_dec(v_tail_2945_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_3592_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v_head_2955_; lean_object* v_tail_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_3591_; 
v_head_2955_ = lean_ctor_get(v_tail_2946_, 0);
v_tail_2956_ = lean_ctor_get(v_tail_2946_, 1);
v_isSharedCheck_3591_ = !lean_is_exclusive(v_tail_2946_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_2958_ = v_tail_2946_;
v_isShared_2959_ = v_isSharedCheck_3591_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_tail_2956_);
lean_inc(v_head_2955_);
lean_dec(v_tail_2946_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_3591_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2960_; 
v___x_2960_ = l_Lean_ModuleSetup_load(v_head_2947_);
lean_dec(v_head_2947_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; lean_object* v_name_2962_; lean_object* v_importArts_2963_; lean_object* v_options_2964_; uint8_t v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2969_; 
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
lean_inc(v_a_2961_);
lean_dec_ref_known(v___x_2960_, 1);
v_name_2962_ = lean_ctor_get(v_a_2961_, 0);
lean_inc(v_name_2962_);
v_importArts_2963_ = lean_ctor_get(v_a_2961_, 3);
lean_inc(v_importArts_2963_);
v_options_2964_ = lean_ctor_get(v_a_2961_, 6);
lean_inc(v_options_2964_);
lean_dec(v_a_2961_);
v___x_2965_ = 0;
v___x_2966_ = l_Lean_LeanOptions_toOptions(v_options_2964_);
v___x_2967_ = lean_box(v___x_2965_);
if (v_isShared_2959_ == 0)
{
lean_ctor_set_tag(v___x_2958_, 0);
lean_ctor_set(v___x_2958_, 1, v___x_2966_);
lean_ctor_set(v___x_2958_, 0, v___x_2967_);
v___x_2969_ = v___x_2958_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v___x_2967_);
lean_ctor_set(v_reuseFailAlloc_3582_, 1, v___x_2966_);
v___x_2969_ = v_reuseFailAlloc_3582_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
lean_object* v___x_2970_; 
v___x_2970_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_tail_2956_, v___x_2969_);
lean_dec(v_tail_2956_);
if (lean_obj_tag(v___x_2970_) == 0)
{
lean_object* v_a_2971_; lean_object* v___x_2972_; 
v_a_2971_ = lean_ctor_get(v___x_2970_, 0);
lean_inc(v_a_2971_);
lean_dec_ref_known(v___x_2970_, 1);
v___x_2972_ = lean_init_search_path();
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v_fst_2973_; lean_object* v_snd_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_3565_; 
lean_dec_ref_known(v___x_2972_, 1);
v_fst_2973_ = lean_ctor_get(v_a_2971_, 0);
v_snd_2974_ = lean_ctor_get(v_a_2971_, 1);
v_isSharedCheck_3565_ = !lean_is_exclusive(v_a_2971_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_2976_ = v_a_2971_;
v_isShared_2977_ = v_isSharedCheck_3565_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_snd_2974_);
lean_inc(v_fst_2973_);
lean_dec(v_a_2971_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_3565_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; uint8_t v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; uint8_t v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3148_; uint8_t v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v_nextMacroScope_3159_; lean_object* v_ngen_3160_; lean_object* v_auxDeclNGen_3161_; lean_object* v_traceState_3162_; lean_object* v_messages_3163_; lean_object* v_infoState_3164_; lean_object* v_snapshotTasks_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; uint8_t v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; uint8_t v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3262_; uint8_t v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; uint8_t v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; uint8_t v___y_3285_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; uint8_t v___x_3311_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; uint8_t v___x_3468_; uint8_t v___y_3470_; uint8_t v___x_3564_; 
v___x_2978_ = lean_obj_once(&l_main___closed__3, &l_main___closed__3_once, _init_l_main___closed__3);
v___x_2979_ = lean_box(0);
v___x_2980_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_2981_ = lean_obj_once(&l_main___closed__5, &l_main___closed__5_once, _init_l_main___closed__5);
v___x_2982_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_2983_ = lean_obj_once(&l_main___closed__8, &l_main___closed__8_once, _init_l_main___closed__8);
v___x_2984_ = lean_obj_once(&l_main___closed__9, &l_main___closed__9_once, _init_l_main___closed__9);
v___x_2985_ = lean_box(1);
v___x_2986_ = ((lean_object*)(l_main___closed__10));
v___x_2987_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_2988_ = 1;
v___x_2989_ = l_Lean_Option_set___at___00Lean_Environment_realizeConst_spec__0(v_snd_2974_, v___x_2987_, v___x_2988_);
v___x_2990_ = l_Lean_maxHeartbeats;
v___x_2991_ = lean_unsigned_to_nat(0u);
v___x_2992_ = l_Lean_Option_set___at___00main_spec__3(v___x_2989_, v___x_2990_, v___x_2991_);
v___x_3306_ = ((lean_object*)(l_main___closed__21));
lean_inc(v_name_2962_);
v___x_3307_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_3307_, 0, v_name_2962_);
lean_ctor_set_uint8(v___x_3307_, sizeof(void*)*1, v___x_2988_);
lean_ctor_set_uint8(v___x_3307_, sizeof(void*)*1 + 1, v___x_2988_);
lean_ctor_set_uint8(v___x_3307_, sizeof(void*)*1 + 2, v___x_2965_);
v___x_3308_ = lean_unsigned_to_nat(1u);
v___x_3309_ = lean_mk_empty_array_with_capacity(v___x_3308_);
v___x_3310_ = lean_array_push(v___x_3309_, v___x_3307_);
v___x_3311_ = 0;
v___x_3468_ = 2;
v___x_3564_ = lean_uint8_once(&l_main___closed__37, &l_main___closed__37_once, _init_l_main___closed__37);
if (v___x_3564_ == 0)
{
v___y_3470_ = v___x_2988_;
goto v___jp_3469_;
}
else
{
v___y_3470_ = v___x_2965_;
goto v___jp_3469_;
}
v___jp_2993_:
{
lean_object* v___x_3013_; lean_object* v_messages_3014_; lean_object* v_env_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3139_; 
v___x_3013_ = lean_st_ref_get(v___y_3007_);
lean_dec(v___y_3007_);
v_messages_3014_ = lean_ctor_get(v___x_3013_, 6);
v_env_3015_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3139_ == 0)
{
lean_object* v_unused_3140_; lean_object* v_unused_3141_; lean_object* v_unused_3142_; lean_object* v_unused_3143_; lean_object* v_unused_3144_; lean_object* v_unused_3145_; lean_object* v_unused_3146_; 
v_unused_3140_ = lean_ctor_get(v___x_3013_, 8);
lean_dec(v_unused_3140_);
v_unused_3141_ = lean_ctor_get(v___x_3013_, 7);
lean_dec(v_unused_3141_);
v_unused_3142_ = lean_ctor_get(v___x_3013_, 5);
lean_dec(v_unused_3142_);
v_unused_3143_ = lean_ctor_get(v___x_3013_, 4);
lean_dec(v_unused_3143_);
v_unused_3144_ = lean_ctor_get(v___x_3013_, 3);
lean_dec(v_unused_3144_);
v_unused_3145_ = lean_ctor_get(v___x_3013_, 2);
lean_dec(v_unused_3145_);
v_unused_3146_ = lean_ctor_get(v___x_3013_, 1);
lean_dec(v_unused_3146_);
v___x_3017_ = v___x_3013_;
v_isShared_3018_ = v_isSharedCheck_3139_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_messages_3014_);
lean_inc(v_env_3015_);
lean_dec(v___x_3013_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3139_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v_unreported_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
v_unreported_3019_ = lean_ctor_get(v_messages_3014_, 1);
v___x_3020_ = lean_box(0);
v___x_3021_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_unreported_3019_, v___x_3020_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3129_; 
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3129_ == 0)
{
lean_object* v_unused_3130_; 
v_unused_3130_ = lean_ctor_get(v___x_3021_, 0);
lean_dec(v_unused_3130_);
v___x_3023_ = v___x_3021_;
v_isShared_3024_ = v_isSharedCheck_3129_;
goto v_resetjp_3022_;
}
else
{
lean_dec(v___x_3021_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3129_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
uint8_t v___x_3025_; 
v___x_3025_ = l_Lean_MessageLog_hasErrors(v_messages_3014_);
lean_dec_ref(v_messages_3014_);
if (v___x_3025_ == 0)
{
lean_object* v___x_3026_; 
lean_del_object(v___x_3023_);
lean_inc_ref(v_env_3015_);
v___x_3026_ = l___private_LeanIR_0__mkIRSigData(v_env_3015_);
if (lean_obj_tag(v___x_3026_) == 0)
{
lean_object* v_a_3027_; lean_object* v___x_3028_; 
v_a_3027_ = lean_ctor_get(v___x_3026_, 0);
lean_inc(v_a_3027_);
lean_dec_ref_known(v___x_3026_, 1);
lean_inc_ref(v_env_3015_);
v___x_3028_ = l___private_LeanIR_0__mkIRData(v_env_3015_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_object* v_a_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3036_; 
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
lean_inc(v_a_3029_);
lean_dec_ref_known(v___x_3028_, 1);
v___x_3030_ = ((lean_object*)(l_main___closed__11));
lean_inc(v_head_2951_);
v___x_3031_ = l_System_FilePath_addExtension(v_head_2951_, v___x_3030_);
v___x_3032_ = l_Lean_Environment_mainModule(v_env_3015_);
v___x_3033_ = ((lean_object*)(l_main___closed__13));
v___x_3034_ = l_Lean_Name_append(v___x_3032_, v___x_3033_);
if (v_isShared_2977_ == 0)
{
lean_ctor_set(v___x_2976_, 1, v_a_3027_);
lean_ctor_set(v___x_2976_, 0, v___x_3031_);
v___x_3036_ = v___x_2976_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v___x_3031_);
lean_ctor_set(v_reuseFailAlloc_3108_, 1, v_a_3027_);
v___x_3036_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
lean_object* v___x_3038_; 
lean_inc(v_head_2951_);
if (v_isShared_2954_ == 0)
{
lean_ctor_set_tag(v___x_2953_, 0);
lean_ctor_set(v___x_2953_, 1, v_a_3029_);
v___x_3038_ = v___x_2953_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_head_2951_);
lean_ctor_set(v_reuseFailAlloc_3107_, 1, v_a_3029_);
v___x_3038_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3039_ = lean_unsigned_to_nat(2u);
v___x_3040_ = lean_mk_empty_array_with_capacity(v___x_3039_);
v___x_3041_ = lean_array_push(v___x_3040_, v___x_3036_);
v___x_3042_ = lean_array_push(v___x_3041_, v___x_3038_);
v___x_3043_ = l_Lean_saveModuleDataParts(v___x_3034_, v___x_3042_);
lean_dec_ref(v___x_3042_);
lean_dec(v___x_3034_);
if (lean_obj_tag(v___x_3043_) == 0)
{
uint8_t v___x_3044_; lean_object* v___x_3045_; 
lean_dec_ref_known(v___x_3043_, 1);
v___x_3044_ = 1;
v___x_3045_ = lean_io_prim_handle_mk(v_head_2955_, v___x_3044_);
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_object* v_a_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3051_; 
lean_dec(v_head_2955_);
v_a_3046_ = lean_ctor_get(v___x_3045_, 0);
lean_inc(v_a_3046_);
lean_dec_ref_known(v___x_3045_, 1);
v___x_3047_ = ((lean_object*)(l_main___closed__14));
v___x_3048_ = l_Lean_Options_empty;
v___x_3049_ = lean_obj_once(&l_main___closed__15, &l_main___closed__15_once, _init_l_main___closed__15);
lean_inc_ref(v___y_3005_);
lean_inc_ref(v___y_3010_);
lean_inc_ref(v___y_3012_);
lean_inc_ref(v___y_3008_);
lean_inc_ref(v___y_3011_);
lean_inc_ref(v___y_3004_);
lean_inc(v___y_3006_);
lean_inc_ref(v_env_3015_);
if (v_isShared_3018_ == 0)
{
lean_ctor_set(v___x_3017_, 8, v___y_3005_);
lean_ctor_set(v___x_3017_, 7, v___y_3010_);
lean_ctor_set(v___x_3017_, 6, v___y_3012_);
lean_ctor_set(v___x_3017_, 5, v___y_3008_);
lean_ctor_set(v___x_3017_, 4, v___y_3011_);
lean_ctor_set(v___x_3017_, 3, v___y_3003_);
lean_ctor_set(v___x_3017_, 2, v___y_3004_);
lean_ctor_set(v___x_3017_, 1, v___y_3006_);
v___x_3051_ = v___x_3017_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_env_3015_);
lean_ctor_set(v_reuseFailAlloc_3076_, 1, v___y_3006_);
lean_ctor_set(v_reuseFailAlloc_3076_, 2, v___y_3004_);
lean_ctor_set(v_reuseFailAlloc_3076_, 3, v___y_3003_);
lean_ctor_set(v_reuseFailAlloc_3076_, 4, v___y_3011_);
lean_ctor_set(v_reuseFailAlloc_3076_, 5, v___y_3008_);
lean_ctor_set(v_reuseFailAlloc_3076_, 6, v___y_3012_);
lean_ctor_set(v_reuseFailAlloc_3076_, 7, v___y_3010_);
lean_ctor_set(v_reuseFailAlloc_3076_, 8, v___y_3005_);
v___x_3051_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___f_3055_; lean_object* v___x_3056_; 
v___x_3052_ = lean_box(v___x_2988_);
v___x_3053_ = lean_box(v___x_2965_);
v___x_3054_ = lean_box(v___y_2994_);
lean_inc_ref(v___y_3000_);
lean_inc(v___y_2995_);
lean_inc(v___y_2996_);
lean_inc(v___y_2997_);
lean_inc(v___y_2998_);
lean_inc_ref(v___y_3002_);
lean_inc(v___y_2999_);
v___f_3055_ = lean_alloc_closure((void*)(l_main___lam__1___boxed), 19, 18);
lean_closure_set(v___f_3055_, 0, v___x_3051_);
lean_closure_set(v___f_3055_, 1, v___y_2999_);
lean_closure_set(v___f_3055_, 2, v___x_3048_);
lean_closure_set(v___f_3055_, 3, v_name_2962_);
lean_closure_set(v___f_3055_, 4, v_a_3046_);
lean_closure_set(v___f_3055_, 5, v___x_3052_);
lean_closure_set(v___f_3055_, 6, v_head_2951_);
lean_closure_set(v___f_3055_, 7, v___y_3002_);
lean_closure_set(v___f_3055_, 8, v___x_2991_);
lean_closure_set(v___f_3055_, 9, v___y_2998_);
lean_closure_set(v___f_3055_, 10, v___y_3001_);
lean_closure_set(v___f_3055_, 11, v___y_2997_);
lean_closure_set(v___f_3055_, 12, v___x_3049_);
lean_closure_set(v___f_3055_, 13, v___y_2996_);
lean_closure_set(v___f_3055_, 14, v___y_2995_);
lean_closure_set(v___f_3055_, 15, v___x_3053_);
lean_closure_set(v___f_3055_, 16, v___y_3000_);
lean_closure_set(v___f_3055_, 17, v___x_3054_);
v___x_3056_ = l_Lean_profileitIOUnsafe___redArg(v___x_3047_, v___x_2992_, v___f_3055_, v___y_3009_);
lean_dec_ref(v___x_2992_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v___x_3057_; uint8_t v___x_3058_; 
lean_dec_ref_known(v___x_3056_, 1);
v___x_3057_ = lean_display_cumulative_profiling_times();
v___x_3058_ = lean_unbox(v_fst_2973_);
lean_dec(v_fst_2973_);
if (v___x_3058_ == 0)
{
lean_dec_ref(v_env_3015_);
goto v___jp_2942_;
}
else
{
lean_object* v___x_3059_; 
v___x_3059_ = l_Lean_Environment_displayStats(v_env_3015_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_dec_ref_known(v___x_3059_, 1);
goto v___jp_2942_;
}
else
{
lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3067_; 
v_a_3060_ = lean_ctor_get(v___x_3059_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3062_ = v___x_3059_;
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_dec(v___x_3059_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3065_; 
if (v_isShared_3063_ == 0)
{
v___x_3065_ = v___x_3062_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_a_3060_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
}
}
else
{
lean_object* v_a_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3075_; 
lean_dec_ref(v_env_3015_);
lean_dec(v_fst_2973_);
v_a_3068_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3070_ = v___x_3056_;
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_a_3068_);
lean_dec(v___x_3056_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_a_3068_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
}
else
{
lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
lean_dec_ref_known(v___x_3045_, 1);
lean_del_object(v___x_3017_);
lean_dec_ref(v_env_3015_);
lean_dec(v___y_3009_);
lean_dec_ref(v___y_3003_);
lean_dec(v___y_3001_);
lean_dec_ref(v___x_2992_);
lean_dec(v_fst_2973_);
lean_dec(v_name_2962_);
lean_dec(v_head_2951_);
v___x_3077_ = ((lean_object*)(l_main___closed__16));
v___x_3078_ = lean_string_append(v___x_3077_, v_head_2955_);
lean_dec(v_head_2955_);
v___x_3079_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__1));
v___x_3080_ = lean_string_append(v___x_3078_, v___x_3079_);
v___x_3081_ = l_IO_eprintln___at___00main_spec__6(v___x_3080_);
if (lean_obj_tag(v___x_3081_) == 0)
{
lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3089_; 
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3089_ == 0)
{
lean_object* v_unused_3090_; 
v_unused_3090_ = lean_ctor_get(v___x_3081_, 0);
lean_dec(v_unused_3090_);
v___x_3083_ = v___x_3081_;
v_isShared_3084_ = v_isSharedCheck_3089_;
goto v_resetjp_3082_;
}
else
{
lean_dec(v___x_3081_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3089_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3085_; lean_object* v___x_3087_; 
v___x_3085_ = l_main___boxed__const__1;
if (v_isShared_3084_ == 0)
{
lean_ctor_set(v___x_3083_, 0, v___x_3085_);
v___x_3087_ = v___x_3083_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v___x_3085_);
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
lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3098_; 
v_a_3091_ = lean_ctor_get(v___x_3081_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3093_ = v___x_3081_;
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_3081_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3096_; 
if (v_isShared_3094_ == 0)
{
v___x_3096_ = v___x_3093_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_a_3091_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
}
}
else
{
lean_object* v_a_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3106_; 
lean_del_object(v___x_3017_);
lean_dec_ref(v_env_3015_);
lean_dec(v___y_3009_);
lean_dec_ref(v___y_3003_);
lean_dec(v___y_3001_);
lean_dec_ref(v___x_2992_);
lean_dec(v_fst_2973_);
lean_dec(v_name_2962_);
lean_dec(v_head_2955_);
lean_dec(v_head_2951_);
v_a_3099_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3101_ = v___x_3043_;
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_a_3099_);
lean_dec(v___x_3043_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3104_; 
if (v_isShared_3102_ == 0)
{
v___x_3104_ = v___x_3101_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_a_3099_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
}
}
}
else
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3116_; 
lean_dec(v_a_3027_);
lean_del_object(v___x_3017_);
lean_dec_ref(v_env_3015_);
lean_dec(v___y_3009_);
lean_dec_ref(v___y_3003_);
lean_dec(v___y_3001_);
lean_dec_ref(v___x_2992_);
lean_del_object(v___x_2976_);
lean_dec(v_fst_2973_);
lean_dec(v_name_2962_);
lean_dec(v_head_2955_);
lean_del_object(v___x_2953_);
lean_dec(v_head_2951_);
v_a_3109_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3111_ = v___x_3028_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_3028_);
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
else
{
lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3124_; 
lean_del_object(v___x_3017_);
lean_dec_ref(v_env_3015_);
lean_dec(v___y_3009_);
lean_dec_ref(v___y_3003_);
lean_dec(v___y_3001_);
lean_dec_ref(v___x_2992_);
lean_del_object(v___x_2976_);
lean_dec(v_fst_2973_);
lean_dec(v_name_2962_);
lean_dec(v_head_2955_);
lean_del_object(v___x_2953_);
lean_dec(v_head_2951_);
v_a_3117_ = lean_ctor_get(v___x_3026_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3119_ = v___x_3026_;
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_3026_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3122_; 
if (v_isShared_3120_ == 0)
{
v___x_3122_ = v___x_3119_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
}
else
{
lean_object* v___x_3125_; lean_object* v___x_3127_; 
lean_del_object(v___x_3017_);
lean_dec_ref(v_env_3015_);
lean_dec(v___y_3009_);
lean_dec_ref(v___y_3003_);
lean_dec(v___y_3001_);
lean_dec_ref(v___x_2992_);
lean_del_object(v___x_2976_);
lean_dec(v_fst_2973_);
lean_dec(v_name_2962_);
lean_dec(v_head_2955_);
lean_del_object(v___x_2953_);
lean_dec(v_head_2951_);
v___x_3125_ = l_main___boxed__const__1;
if (v_isShared_3024_ == 0)
{
lean_ctor_set(v___x_3023_, 0, v___x_3125_);
v___x_3127_ = v___x_3023_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v___x_3125_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
}
}
}
}
else
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3138_; 
lean_del_object(v___x_3017_);
lean_dec_ref(v_env_3015_);
lean_dec_ref(v_messages_3014_);
lean_dec(v___y_3009_);
lean_dec_ref(v___y_3003_);
lean_dec(v___y_3001_);
lean_dec_ref(v___x_2992_);
lean_del_object(v___x_2976_);
lean_dec(v_fst_2973_);
lean_dec(v_name_2962_);
lean_dec(v_head_2955_);
lean_del_object(v___x_2953_);
lean_dec(v_head_2951_);
v_a_3131_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3133_ = v___x_3021_;
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3021_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3136_; 
if (v_isShared_3134_ == 0)
{
v___x_3136_ = v___x_3133_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_a_3131_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
}
}
v___jp_3147_:
{
lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; size_t v_sz_3181_; size_t v___x_3182_; lean_object* v___x_3183_; 
lean_inc_ref(v___y_3167_);
v___x_3178_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3178_, 0, v___y_3177_);
lean_ctor_set(v___x_3178_, 1, v_nextMacroScope_3159_);
lean_ctor_set(v___x_3178_, 2, v_ngen_3160_);
lean_ctor_set(v___x_3178_, 3, v_auxDeclNGen_3161_);
lean_ctor_set(v___x_3178_, 4, v_traceState_3162_);
lean_ctor_set(v___x_3178_, 5, v___y_3167_);
lean_ctor_set(v___x_3178_, 6, v_messages_3163_);
lean_ctor_set(v___x_3178_, 7, v_infoState_3164_);
lean_ctor_set(v___x_3178_, 8, v_snapshotTasks_3165_);
v___x_3179_ = lean_st_ref_set(v___y_3166_, v___x_3178_);
v___x_3180_ = lean_box(0);
v_sz_3181_ = lean_array_size(v___y_3176_);
v___x_3182_ = ((size_t)0ULL);
v___x_3183_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(v___y_3176_, v_sz_3181_, v___x_3182_, v___x_3180_, v___y_3169_, v___y_3166_);
lean_dec_ref(v___y_3176_);
if (lean_obj_tag(v___x_3183_) == 0)
{
lean_dec_ref_known(v___x_3183_, 1);
lean_dec_ref(v___y_3169_);
lean_dec(v___y_3166_);
v___y_2994_ = v___y_3149_;
v___y_2995_ = v___y_3148_;
v___y_2996_ = v___y_3150_;
v___y_2997_ = v___y_3152_;
v___y_2998_ = v___y_3151_;
v___y_2999_ = v___y_3153_;
v___y_3000_ = v___y_3154_;
v___y_3001_ = v___y_3156_;
v___y_3002_ = v___y_3155_;
v___y_3003_ = v___y_3157_;
v___y_3004_ = v___y_3170_;
v___y_3005_ = v___y_3158_;
v___y_3006_ = v___y_3171_;
v___y_3007_ = v___y_3172_;
v___y_3008_ = v___y_3167_;
v___y_3009_ = v___y_3173_;
v___y_3010_ = v___y_3174_;
v___y_3011_ = v___y_3168_;
v___y_3012_ = v___y_3175_;
goto v___jp_2993_;
}
else
{
if (lean_obj_tag(v___x_3183_) == 0)
{
lean_dec_ref_known(v___x_3183_, 1);
lean_dec_ref(v___y_3169_);
lean_dec(v___y_3166_);
v___y_2994_ = v___y_3149_;
v___y_2995_ = v___y_3148_;
v___y_2996_ = v___y_3150_;
v___y_2997_ = v___y_3152_;
v___y_2998_ = v___y_3151_;
v___y_2999_ = v___y_3153_;
v___y_3000_ = v___y_3154_;
v___y_3001_ = v___y_3156_;
v___y_3002_ = v___y_3155_;
v___y_3003_ = v___y_3157_;
v___y_3004_ = v___y_3170_;
v___y_3005_ = v___y_3158_;
v___y_3006_ = v___y_3171_;
v___y_3007_ = v___y_3172_;
v___y_3008_ = v___y_3167_;
v___y_3009_ = v___y_3173_;
v___y_3010_ = v___y_3174_;
v___y_3011_ = v___y_3168_;
v___y_3012_ = v___y_3175_;
goto v___jp_2993_;
}
else
{
lean_object* v_a_3184_; uint8_t v___x_3185_; 
v_a_3184_ = lean_ctor_get(v___x_3183_, 0);
lean_inc(v_a_3184_);
lean_dec_ref_known(v___x_3183_, 1);
v___x_3185_ = l_Lean_Exception_isInterrupt(v_a_3184_);
if (v___x_3185_ == 0)
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3186_ = l_Lean_Exception_toMessageData(v_a_3184_);
v___x_3187_ = l_Lean_logError___at___00main_spec__14(v___x_3186_, v___y_3169_, v___y_3166_);
lean_dec(v___y_3166_);
lean_dec_ref(v___y_3169_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_dec_ref_known(v___x_3187_, 1);
v___y_2994_ = v___y_3149_;
v___y_2995_ = v___y_3148_;
v___y_2996_ = v___y_3150_;
v___y_2997_ = v___y_3152_;
v___y_2998_ = v___y_3151_;
v___y_2999_ = v___y_3153_;
v___y_3000_ = v___y_3154_;
v___y_3001_ = v___y_3156_;
v___y_3002_ = v___y_3155_;
v___y_3003_ = v___y_3157_;
v___y_3004_ = v___y_3170_;
v___y_3005_ = v___y_3158_;
v___y_3006_ = v___y_3171_;
v___y_3007_ = v___y_3172_;
v___y_3008_ = v___y_3167_;
v___y_3009_ = v___y_3173_;
v___y_3010_ = v___y_3174_;
v___y_3011_ = v___y_3168_;
v___y_3012_ = v___y_3175_;
goto v___jp_2993_;
}
else
{
lean_object* v___x_3188_; lean_object* v___x_3189_; 
lean_dec_ref_known(v___x_3187_, 1);
lean_dec(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___x_2992_);
lean_del_object(v___x_2976_);
lean_dec(v_fst_2973_);
lean_dec(v_name_2962_);
lean_dec(v_head_2955_);
lean_del_object(v___x_2953_);
lean_dec(v_head_2951_);
v___x_3188_ = lean_obj_once(&l_main___closed__20, &l_main___closed__20_once, _init_l_main___closed__20);
v___x_3189_ = l_panic___at___00main_spec__5(v___x_3188_);
return v___x_3189_;
}
}
else
{
lean_dec(v_a_3184_);
lean_dec_ref(v___y_3169_);
lean_dec(v___y_3166_);
v___y_2994_ = v___y_3149_;
v___y_2995_ = v___y_3148_;
v___y_2996_ = v___y_3150_;
v___y_2997_ = v___y_3152_;
v___y_2998_ = v___y_3151_;
v___y_2999_ = v___y_3153_;
v___y_3000_ = v___y_3154_;
v___y_3001_ = v___y_3156_;
v___y_3002_ = v___y_3155_;
v___y_3003_ = v___y_3157_;
v___y_3004_ = v___y_3170_;
v___y_3005_ = v___y_3158_;
v___y_3006_ = v___y_3171_;
v___y_3007_ = v___y_3172_;
v___y_3008_ = v___y_3167_;
v___y_3009_ = v___y_3173_;
v___y_3010_ = v___y_3174_;
v___y_3011_ = v___y_3168_;
v___y_3012_ = v___y_3175_;
goto v___jp_2993_;
}
}
}
}
v___jp_3190_:
{
lean_object* v___x_3215_; lean_object* v_fileName_3216_; lean_object* v_fileMap_3217_; lean_object* v_currRecDepth_3218_; lean_object* v_ref_3219_; lean_object* v_currNamespace_3220_; lean_object* v_openDecls_3221_; lean_object* v_initHeartbeats_3222_; lean_object* v_maxHeartbeats_3223_; lean_object* v_quotContext_3224_; lean_object* v_currMacroScope_3225_; lean_object* v_cancelTk_x3f_3226_; uint8_t v_suppressElabErrors_3227_; lean_object* v_inheritedTraceOptions_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3258_; 
v___x_3215_ = lean_st_ref_take(v___y_3214_);
v_fileName_3216_ = lean_ctor_get(v___y_3213_, 0);
v_fileMap_3217_ = lean_ctor_get(v___y_3213_, 1);
v_currRecDepth_3218_ = lean_ctor_get(v___y_3213_, 3);
v_ref_3219_ = lean_ctor_get(v___y_3213_, 5);
v_currNamespace_3220_ = lean_ctor_get(v___y_3213_, 6);
v_openDecls_3221_ = lean_ctor_get(v___y_3213_, 7);
v_initHeartbeats_3222_ = lean_ctor_get(v___y_3213_, 8);
v_maxHeartbeats_3223_ = lean_ctor_get(v___y_3213_, 9);
v_quotContext_3224_ = lean_ctor_get(v___y_3213_, 10);
v_currMacroScope_3225_ = lean_ctor_get(v___y_3213_, 11);
v_cancelTk_x3f_3226_ = lean_ctor_get(v___y_3213_, 12);
v_suppressElabErrors_3227_ = lean_ctor_get_uint8(v___y_3213_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3228_ = lean_ctor_get(v___y_3213_, 13);
v_isSharedCheck_3258_ = !lean_is_exclusive(v___y_3213_);
if (v_isSharedCheck_3258_ == 0)
{
lean_object* v_unused_3259_; lean_object* v_unused_3260_; 
v_unused_3259_ = lean_ctor_get(v___y_3213_, 4);
lean_dec(v_unused_3259_);
v_unused_3260_ = lean_ctor_get(v___y_3213_, 2);
lean_dec(v_unused_3260_);
v___x_3230_ = v___y_3213_;
v_isShared_3231_ = v_isSharedCheck_3258_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_inheritedTraceOptions_3228_);
lean_inc(v_cancelTk_x3f_3226_);
lean_inc(v_currMacroScope_3225_);
lean_inc(v_quotContext_3224_);
lean_inc(v_maxHeartbeats_3223_);
lean_inc(v_initHeartbeats_3222_);
lean_inc(v_openDecls_3221_);
lean_inc(v_currNamespace_3220_);
lean_inc(v_ref_3219_);
lean_inc(v_currRecDepth_3218_);
lean_inc(v_fileMap_3217_);
lean_inc(v_fileName_3216_);
lean_dec(v___y_3213_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3258_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v_env_3232_; lean_object* v_nextMacroScope_3233_; lean_object* v_ngen_3234_; lean_object* v_auxDeclNGen_3235_; lean_object* v_traceState_3236_; lean_object* v_messages_3237_; lean_object* v_infoState_3238_; lean_object* v_snapshotTasks_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3243_; 
v_env_3232_ = lean_ctor_get(v___x_3215_, 0);
lean_inc_ref(v_env_3232_);
v_nextMacroScope_3233_ = lean_ctor_get(v___x_3215_, 1);
lean_inc(v_nextMacroScope_3233_);
v_ngen_3234_ = lean_ctor_get(v___x_3215_, 2);
lean_inc_ref(v_ngen_3234_);
v_auxDeclNGen_3235_ = lean_ctor_get(v___x_3215_, 3);
lean_inc_ref(v_auxDeclNGen_3235_);
v_traceState_3236_ = lean_ctor_get(v___x_3215_, 4);
lean_inc_ref(v_traceState_3236_);
v_messages_3237_ = lean_ctor_get(v___x_3215_, 6);
lean_inc_ref(v_messages_3237_);
v_infoState_3238_ = lean_ctor_get(v___x_3215_, 7);
lean_inc_ref(v_infoState_3238_);
v_snapshotTasks_3239_ = lean_ctor_get(v___x_3215_, 8);
lean_inc_ref(v_snapshotTasks_3239_);
lean_dec(v___x_3215_);
v___x_3240_ = l_Lean_maxRecDepth;
v___x_3241_ = l_Lean_Option_get___at___00main_spec__9(v___x_2992_, v___x_3240_);
lean_inc_ref(v___x_2992_);
if (v_isShared_3231_ == 0)
{
lean_ctor_set(v___x_3230_, 4, v___x_3241_);
lean_ctor_set(v___x_3230_, 2, v___x_2992_);
v___x_3243_ = v___x_3230_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_fileName_3216_);
lean_ctor_set(v_reuseFailAlloc_3257_, 1, v_fileMap_3217_);
lean_ctor_set(v_reuseFailAlloc_3257_, 2, v___x_2992_);
lean_ctor_set(v_reuseFailAlloc_3257_, 3, v_currRecDepth_3218_);
lean_ctor_set(v_reuseFailAlloc_3257_, 4, v___x_3241_);
lean_ctor_set(v_reuseFailAlloc_3257_, 5, v_ref_3219_);
lean_ctor_set(v_reuseFailAlloc_3257_, 6, v_currNamespace_3220_);
lean_ctor_set(v_reuseFailAlloc_3257_, 7, v_openDecls_3221_);
lean_ctor_set(v_reuseFailAlloc_3257_, 8, v_initHeartbeats_3222_);
lean_ctor_set(v_reuseFailAlloc_3257_, 9, v_maxHeartbeats_3223_);
lean_ctor_set(v_reuseFailAlloc_3257_, 10, v_quotContext_3224_);
lean_ctor_set(v_reuseFailAlloc_3257_, 11, v_currMacroScope_3225_);
lean_ctor_set(v_reuseFailAlloc_3257_, 12, v_cancelTk_x3f_3226_);
lean_ctor_set(v_reuseFailAlloc_3257_, 13, v_inheritedTraceOptions_3228_);
lean_ctor_set_uint8(v_reuseFailAlloc_3257_, sizeof(void*)*14 + 1, v_suppressElabErrors_3227_);
v___x_3243_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
lean_object* v___x_3244_; uint8_t v___x_3245_; 
lean_ctor_set_uint8(v___x_3243_, sizeof(void*)*14, v___y_3207_);
v___x_3244_ = lean_array_get_size(v___y_3212_);
v___x_3245_ = lean_nat_dec_lt(v___x_2991_, v___x_3244_);
if (v___x_3245_ == 0)
{
lean_object* v___x_3246_; 
lean_inc_ref(v___y_3204_);
v___x_3246_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3204_, v_env_3232_, v___x_2985_);
v___y_3148_ = v___y_3192_;
v___y_3149_ = v___y_3191_;
v___y_3150_ = v___y_3193_;
v___y_3151_ = v___y_3195_;
v___y_3152_ = v___y_3194_;
v___y_3153_ = v___y_3196_;
v___y_3154_ = v___y_3197_;
v___y_3155_ = v___y_3199_;
v___y_3156_ = v___y_3198_;
v___y_3157_ = v___y_3200_;
v___y_3158_ = v___y_3201_;
v_nextMacroScope_3159_ = v_nextMacroScope_3233_;
v_ngen_3160_ = v_ngen_3234_;
v_auxDeclNGen_3161_ = v_auxDeclNGen_3235_;
v_traceState_3162_ = v_traceState_3236_;
v_messages_3163_ = v_messages_3237_;
v_infoState_3164_ = v_infoState_3238_;
v_snapshotTasks_3165_ = v_snapshotTasks_3239_;
v___y_3166_ = v___y_3214_;
v___y_3167_ = v___y_3202_;
v___y_3168_ = v___y_3203_;
v___y_3169_ = v___x_3243_;
v___y_3170_ = v___y_3205_;
v___y_3171_ = v___y_3206_;
v___y_3172_ = v___y_3208_;
v___y_3173_ = v___y_3209_;
v___y_3174_ = v___y_3210_;
v___y_3175_ = v___y_3211_;
v___y_3176_ = v___y_3212_;
v___y_3177_ = v___x_3246_;
goto v___jp_3147_;
}
else
{
uint8_t v___x_3247_; 
v___x_3247_ = lean_nat_dec_le(v___x_3244_, v___x_3244_);
if (v___x_3247_ == 0)
{
if (v___x_3245_ == 0)
{
lean_object* v___x_3248_; 
lean_inc_ref(v___y_3204_);
v___x_3248_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3204_, v_env_3232_, v___x_2985_);
v___y_3148_ = v___y_3192_;
v___y_3149_ = v___y_3191_;
v___y_3150_ = v___y_3193_;
v___y_3151_ = v___y_3195_;
v___y_3152_ = v___y_3194_;
v___y_3153_ = v___y_3196_;
v___y_3154_ = v___y_3197_;
v___y_3155_ = v___y_3199_;
v___y_3156_ = v___y_3198_;
v___y_3157_ = v___y_3200_;
v___y_3158_ = v___y_3201_;
v_nextMacroScope_3159_ = v_nextMacroScope_3233_;
v_ngen_3160_ = v_ngen_3234_;
v_auxDeclNGen_3161_ = v_auxDeclNGen_3235_;
v_traceState_3162_ = v_traceState_3236_;
v_messages_3163_ = v_messages_3237_;
v_infoState_3164_ = v_infoState_3238_;
v_snapshotTasks_3165_ = v_snapshotTasks_3239_;
v___y_3166_ = v___y_3214_;
v___y_3167_ = v___y_3202_;
v___y_3168_ = v___y_3203_;
v___y_3169_ = v___x_3243_;
v___y_3170_ = v___y_3205_;
v___y_3171_ = v___y_3206_;
v___y_3172_ = v___y_3208_;
v___y_3173_ = v___y_3209_;
v___y_3174_ = v___y_3210_;
v___y_3175_ = v___y_3211_;
v___y_3176_ = v___y_3212_;
v___y_3177_ = v___x_3248_;
goto v___jp_3147_;
}
else
{
size_t v___x_3249_; size_t v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3249_ = ((size_t)0ULL);
v___x_3250_ = lean_usize_of_nat(v___x_3244_);
v___x_3251_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3212_, v___x_3249_, v___x_3250_, v___x_2985_);
lean_inc_ref(v___y_3204_);
v___x_3252_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3204_, v_env_3232_, v___x_3251_);
v___y_3148_ = v___y_3192_;
v___y_3149_ = v___y_3191_;
v___y_3150_ = v___y_3193_;
v___y_3151_ = v___y_3195_;
v___y_3152_ = v___y_3194_;
v___y_3153_ = v___y_3196_;
v___y_3154_ = v___y_3197_;
v___y_3155_ = v___y_3199_;
v___y_3156_ = v___y_3198_;
v___y_3157_ = v___y_3200_;
v___y_3158_ = v___y_3201_;
v_nextMacroScope_3159_ = v_nextMacroScope_3233_;
v_ngen_3160_ = v_ngen_3234_;
v_auxDeclNGen_3161_ = v_auxDeclNGen_3235_;
v_traceState_3162_ = v_traceState_3236_;
v_messages_3163_ = v_messages_3237_;
v_infoState_3164_ = v_infoState_3238_;
v_snapshotTasks_3165_ = v_snapshotTasks_3239_;
v___y_3166_ = v___y_3214_;
v___y_3167_ = v___y_3202_;
v___y_3168_ = v___y_3203_;
v___y_3169_ = v___x_3243_;
v___y_3170_ = v___y_3205_;
v___y_3171_ = v___y_3206_;
v___y_3172_ = v___y_3208_;
v___y_3173_ = v___y_3209_;
v___y_3174_ = v___y_3210_;
v___y_3175_ = v___y_3211_;
v___y_3176_ = v___y_3212_;
v___y_3177_ = v___x_3252_;
goto v___jp_3147_;
}
}
else
{
size_t v___x_3253_; size_t v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; 
v___x_3253_ = ((size_t)0ULL);
v___x_3254_ = lean_usize_of_nat(v___x_3244_);
v___x_3255_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3212_, v___x_3253_, v___x_3254_, v___x_2985_);
lean_inc_ref(v___y_3204_);
v___x_3256_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3204_, v_env_3232_, v___x_3255_);
v___y_3148_ = v___y_3192_;
v___y_3149_ = v___y_3191_;
v___y_3150_ = v___y_3193_;
v___y_3151_ = v___y_3195_;
v___y_3152_ = v___y_3194_;
v___y_3153_ = v___y_3196_;
v___y_3154_ = v___y_3197_;
v___y_3155_ = v___y_3199_;
v___y_3156_ = v___y_3198_;
v___y_3157_ = v___y_3200_;
v___y_3158_ = v___y_3201_;
v_nextMacroScope_3159_ = v_nextMacroScope_3233_;
v_ngen_3160_ = v_ngen_3234_;
v_auxDeclNGen_3161_ = v_auxDeclNGen_3235_;
v_traceState_3162_ = v_traceState_3236_;
v_messages_3163_ = v_messages_3237_;
v_infoState_3164_ = v_infoState_3238_;
v_snapshotTasks_3165_ = v_snapshotTasks_3239_;
v___y_3166_ = v___y_3214_;
v___y_3167_ = v___y_3202_;
v___y_3168_ = v___y_3203_;
v___y_3169_ = v___x_3243_;
v___y_3170_ = v___y_3205_;
v___y_3171_ = v___y_3206_;
v___y_3172_ = v___y_3208_;
v___y_3173_ = v___y_3209_;
v___y_3174_ = v___y_3210_;
v___y_3175_ = v___y_3211_;
v___y_3176_ = v___y_3212_;
v___y_3177_ = v___x_3256_;
goto v___jp_3147_;
}
}
}
}
}
v___jp_3261_:
{
uint8_t v___x_3286_; 
v___x_3286_ = lean_bool_not(v___y_3285_);
if (v___x_3286_ == 0)
{
lean_inc(v___y_3280_);
v___y_3191_ = v___y_3263_;
v___y_3192_ = v___y_3262_;
v___y_3193_ = v___y_3264_;
v___y_3194_ = v___y_3266_;
v___y_3195_ = v___y_3265_;
v___y_3196_ = v___y_3267_;
v___y_3197_ = v___y_3268_;
v___y_3198_ = v___y_3270_;
v___y_3199_ = v___y_3269_;
v___y_3200_ = v___y_3271_;
v___y_3201_ = v___y_3272_;
v___y_3202_ = v___y_3273_;
v___y_3203_ = v___y_3274_;
v___y_3204_ = v___y_3275_;
v___y_3205_ = v___y_3276_;
v___y_3206_ = v___y_3277_;
v___y_3207_ = v___y_3278_;
v___y_3208_ = v___y_3280_;
v___y_3209_ = v___y_3281_;
v___y_3210_ = v___y_3282_;
v___y_3211_ = v___y_3284_;
v___y_3212_ = v___y_3283_;
v___y_3213_ = v___y_3279_;
v___y_3214_ = v___y_3280_;
goto v___jp_3190_;
}
else
{
lean_object* v___x_3287_; lean_object* v_env_3288_; lean_object* v_nextMacroScope_3289_; lean_object* v_ngen_3290_; lean_object* v_auxDeclNGen_3291_; lean_object* v_traceState_3292_; lean_object* v_messages_3293_; lean_object* v_infoState_3294_; lean_object* v_snapshotTasks_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3304_; 
v___x_3287_ = lean_st_ref_take(v___y_3280_);
v_env_3288_ = lean_ctor_get(v___x_3287_, 0);
v_nextMacroScope_3289_ = lean_ctor_get(v___x_3287_, 1);
v_ngen_3290_ = lean_ctor_get(v___x_3287_, 2);
v_auxDeclNGen_3291_ = lean_ctor_get(v___x_3287_, 3);
v_traceState_3292_ = lean_ctor_get(v___x_3287_, 4);
v_messages_3293_ = lean_ctor_get(v___x_3287_, 6);
v_infoState_3294_ = lean_ctor_get(v___x_3287_, 7);
v_snapshotTasks_3295_ = lean_ctor_get(v___x_3287_, 8);
v_isSharedCheck_3304_ = !lean_is_exclusive(v___x_3287_);
if (v_isSharedCheck_3304_ == 0)
{
lean_object* v_unused_3305_; 
v_unused_3305_ = lean_ctor_get(v___x_3287_, 5);
lean_dec(v_unused_3305_);
v___x_3297_ = v___x_3287_;
v_isShared_3298_ = v_isSharedCheck_3304_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_snapshotTasks_3295_);
lean_inc(v_infoState_3294_);
lean_inc(v_messages_3293_);
lean_inc(v_traceState_3292_);
lean_inc(v_auxDeclNGen_3291_);
lean_inc(v_ngen_3290_);
lean_inc(v_nextMacroScope_3289_);
lean_inc(v_env_3288_);
lean_dec(v___x_3287_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3304_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3299_; lean_object* v___x_3301_; 
v___x_3299_ = l_Lean_Kernel_enableDiag(v_env_3288_, v___y_3278_);
lean_inc_ref(v___y_3273_);
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 5, v___y_3273_);
lean_ctor_set(v___x_3297_, 0, v___x_3299_);
v___x_3301_ = v___x_3297_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v___x_3299_);
lean_ctor_set(v_reuseFailAlloc_3303_, 1, v_nextMacroScope_3289_);
lean_ctor_set(v_reuseFailAlloc_3303_, 2, v_ngen_3290_);
lean_ctor_set(v_reuseFailAlloc_3303_, 3, v_auxDeclNGen_3291_);
lean_ctor_set(v_reuseFailAlloc_3303_, 4, v_traceState_3292_);
lean_ctor_set(v_reuseFailAlloc_3303_, 5, v___y_3273_);
lean_ctor_set(v_reuseFailAlloc_3303_, 6, v_messages_3293_);
lean_ctor_set(v_reuseFailAlloc_3303_, 7, v_infoState_3294_);
lean_ctor_set(v_reuseFailAlloc_3303_, 8, v_snapshotTasks_3295_);
v___x_3301_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
lean_object* v___x_3302_; 
v___x_3302_ = lean_st_ref_set(v___y_3280_, v___x_3301_);
lean_inc(v___y_3280_);
v___y_3191_ = v___y_3263_;
v___y_3192_ = v___y_3262_;
v___y_3193_ = v___y_3264_;
v___y_3194_ = v___y_3266_;
v___y_3195_ = v___y_3265_;
v___y_3196_ = v___y_3267_;
v___y_3197_ = v___y_3268_;
v___y_3198_ = v___y_3270_;
v___y_3199_ = v___y_3269_;
v___y_3200_ = v___y_3271_;
v___y_3201_ = v___y_3272_;
v___y_3202_ = v___y_3273_;
v___y_3203_ = v___y_3274_;
v___y_3204_ = v___y_3275_;
v___y_3205_ = v___y_3276_;
v___y_3206_ = v___y_3277_;
v___y_3207_ = v___y_3278_;
v___y_3208_ = v___y_3280_;
v___y_3209_ = v___y_3281_;
v___y_3210_ = v___y_3282_;
v___y_3211_ = v___y_3284_;
v___y_3212_ = v___y_3283_;
v___y_3213_ = v___y_3279_;
v___y_3214_ = v___y_3280_;
goto v___jp_3190_;
}
}
}
}
v___jp_3312_:
{
lean_object* v___x_3321_; 
if (v_isShared_2950_ == 0)
{
lean_ctor_set_tag(v___x_2949_, 0);
lean_ctor_set(v___x_2949_, 1, v___y_3319_);
lean_ctor_set(v___x_2949_, 0, v___y_3314_);
v___x_3321_ = v___x_2949_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v___y_3314_);
lean_ctor_set(v_reuseFailAlloc_3416_, 1, v___y_3319_);
v___x_3321_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v_moduleData_3325_; lean_object* v___x_3326_; uint8_t v___x_3327_; 
v___x_3322_ = lean_box(0);
lean_inc_ref(v___y_3318_);
v___x_3323_ = l_Lean_EnvExtension_setState___redArg(v___y_3318_, v___y_3315_, v___x_3321_, v___x_3322_);
v___x_3324_ = l_Lean_Environment_header(v___x_3323_);
v_moduleData_3325_ = lean_ctor_get(v___x_3324_, 6);
lean_inc_ref(v_moduleData_3325_);
lean_dec_ref(v___x_3324_);
v___x_3326_ = lean_array_get_size(v_moduleData_3325_);
v___x_3327_ = lean_nat_dec_lt(v___y_3316_, v___x_3326_);
if (v___x_3327_ == 0)
{
lean_object* v___x_3328_; lean_object* v___x_3329_; 
lean_dec_ref(v_moduleData_3325_);
lean_dec_ref(v___x_3323_);
lean_dec(v___y_3317_);
lean_dec(v___y_3316_);
lean_dec(v___y_3313_);
lean_dec_ref(v___x_2992_);
lean_del_object(v___x_2976_);
lean_dec(v_fst_2973_);
lean_dec(v_name_2962_);
lean_dec(v_head_2955_);
lean_del_object(v___x_2953_);
lean_dec(v_head_2951_);
v___x_3328_ = lean_obj_once(&l_main___closed__22, &l_main___closed__22_once, _init_l_main___closed__22);
v___x_3329_ = l_panic___at___00main_spec__5(v___x_3328_);
return v___x_3329_;
}
else
{
lean_object* v_base_3330_; lean_object* v_private_3331_; lean_object* v_header_3332_; lean_object* v_serverBaseExts_3333_; lean_object* v_checked_3334_; lean_object* v_asyncConstsMap_3335_; lean_object* v_asyncCtx_x3f_3336_; lean_object* v_importRealizationCtx_x3f_3337_; lean_object* v_localRealizationCtxMap_3338_; lean_object* v_allRealizations_3339_; uint8_t v_isExporting_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3414_; 
v_base_3330_ = lean_ctor_get(v___x_3323_, 0);
lean_inc_ref(v_base_3330_);
v_private_3331_ = lean_ctor_get(v_base_3330_, 0);
lean_inc(v_private_3331_);
v_header_3332_ = lean_ctor_get(v_private_3331_, 5);
lean_inc_ref(v_header_3332_);
v_serverBaseExts_3333_ = lean_ctor_get(v___x_3323_, 1);
v_checked_3334_ = lean_ctor_get(v___x_3323_, 2);
v_asyncConstsMap_3335_ = lean_ctor_get(v___x_3323_, 3);
v_asyncCtx_x3f_3336_ = lean_ctor_get(v___x_3323_, 4);
v_importRealizationCtx_x3f_3337_ = lean_ctor_get(v___x_3323_, 5);
v_localRealizationCtxMap_3338_ = lean_ctor_get(v___x_3323_, 6);
v_allRealizations_3339_ = lean_ctor_get(v___x_3323_, 7);
v_isExporting_3340_ = lean_ctor_get_uint8(v___x_3323_, sizeof(void*)*8);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3323_);
if (v_isSharedCheck_3414_ == 0)
{
lean_object* v_unused_3415_; 
v_unused_3415_ = lean_ctor_get(v___x_3323_, 0);
lean_dec(v_unused_3415_);
v___x_3342_ = v___x_3323_;
v_isShared_3343_ = v_isSharedCheck_3414_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_allRealizations_3339_);
lean_inc(v_localRealizationCtxMap_3338_);
lean_inc(v_importRealizationCtx_x3f_3337_);
lean_inc(v_asyncCtx_x3f_3336_);
lean_inc(v_asyncConstsMap_3335_);
lean_inc(v_checked_3334_);
lean_inc(v_serverBaseExts_3333_);
lean_dec(v___x_3323_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3414_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v_public_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3412_; 
v_public_3344_ = lean_ctor_get(v_base_3330_, 1);
v_isSharedCheck_3412_ = !lean_is_exclusive(v_base_3330_);
if (v_isSharedCheck_3412_ == 0)
{
lean_object* v_unused_3413_; 
v_unused_3413_ = lean_ctor_get(v_base_3330_, 0);
lean_dec(v_unused_3413_);
v___x_3346_ = v_base_3330_;
v_isShared_3347_ = v_isSharedCheck_3412_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_public_3344_);
lean_dec(v_base_3330_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3412_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v_constants_3348_; uint8_t v_quotInit_3349_; lean_object* v_diagnostics_3350_; lean_object* v_const2ModIdx_3351_; lean_object* v_extensions_3352_; lean_object* v_irBaseExts_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3410_; 
v_constants_3348_ = lean_ctor_get(v_private_3331_, 0);
v_quotInit_3349_ = lean_ctor_get_uint8(v_private_3331_, sizeof(void*)*6);
v_diagnostics_3350_ = lean_ctor_get(v_private_3331_, 1);
v_const2ModIdx_3351_ = lean_ctor_get(v_private_3331_, 2);
v_extensions_3352_ = lean_ctor_get(v_private_3331_, 3);
v_irBaseExts_3353_ = lean_ctor_get(v_private_3331_, 4);
v_isSharedCheck_3410_ = !lean_is_exclusive(v_private_3331_);
if (v_isSharedCheck_3410_ == 0)
{
lean_object* v_unused_3411_; 
v_unused_3411_ = lean_ctor_get(v_private_3331_, 5);
lean_dec(v_unused_3411_);
v___x_3355_ = v_private_3331_;
v_isShared_3356_ = v_isSharedCheck_3410_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_irBaseExts_3353_);
lean_inc(v_extensions_3352_);
lean_inc(v_const2ModIdx_3351_);
lean_inc(v_diagnostics_3350_);
lean_inc(v_constants_3348_);
lean_dec(v_private_3331_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3410_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
uint32_t v_trustLevel_3357_; lean_object* v_mainModule_3358_; uint8_t v_isModule_3359_; lean_object* v_regions_3360_; lean_object* v_modules_3361_; lean_object* v_moduleName2Idx_3362_; lean_object* v_importAllModules_3363_; lean_object* v_moduleData_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3408_; 
v_trustLevel_3357_ = lean_ctor_get_uint32(v_header_3332_, sizeof(void*)*7);
v_mainModule_3358_ = lean_ctor_get(v_header_3332_, 0);
v_isModule_3359_ = lean_ctor_get_uint8(v_header_3332_, sizeof(void*)*7 + 4);
v_regions_3360_ = lean_ctor_get(v_header_3332_, 2);
v_modules_3361_ = lean_ctor_get(v_header_3332_, 3);
v_moduleName2Idx_3362_ = lean_ctor_get(v_header_3332_, 4);
v_importAllModules_3363_ = lean_ctor_get(v_header_3332_, 5);
v_moduleData_3364_ = lean_ctor_get(v_header_3332_, 6);
v_isSharedCheck_3408_ = !lean_is_exclusive(v_header_3332_);
if (v_isSharedCheck_3408_ == 0)
{
lean_object* v_unused_3409_; 
v_unused_3409_ = lean_ctor_get(v_header_3332_, 1);
lean_dec(v_unused_3409_);
v___x_3366_ = v_header_3332_;
v_isShared_3367_ = v_isSharedCheck_3408_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_moduleData_3364_);
lean_inc(v_importAllModules_3363_);
lean_inc(v_moduleName2Idx_3362_);
lean_inc(v_modules_3361_);
lean_inc(v_regions_3360_);
lean_inc(v_mainModule_3358_);
lean_dec(v_header_3332_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3408_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3368_; lean_object* v_imports_3369_; lean_object* v___x_3371_; 
v___x_3368_ = lean_array_fget(v_moduleData_3325_, v___y_3316_);
lean_dec_ref(v_moduleData_3325_);
v_imports_3369_ = lean_ctor_get(v___x_3368_, 0);
lean_inc_ref(v_imports_3369_);
lean_dec(v___x_3368_);
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 1, v_imports_3369_);
v___x_3371_ = v___x_3366_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(0, 7, 5);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_mainModule_3358_);
lean_ctor_set(v_reuseFailAlloc_3407_, 1, v_imports_3369_);
lean_ctor_set(v_reuseFailAlloc_3407_, 2, v_regions_3360_);
lean_ctor_set(v_reuseFailAlloc_3407_, 3, v_modules_3361_);
lean_ctor_set(v_reuseFailAlloc_3407_, 4, v_moduleName2Idx_3362_);
lean_ctor_set(v_reuseFailAlloc_3407_, 5, v_importAllModules_3363_);
lean_ctor_set(v_reuseFailAlloc_3407_, 6, v_moduleData_3364_);
lean_ctor_set_uint32(v_reuseFailAlloc_3407_, sizeof(void*)*7, v_trustLevel_3357_);
lean_ctor_set_uint8(v_reuseFailAlloc_3407_, sizeof(void*)*7 + 4, v_isModule_3359_);
v___x_3371_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
lean_object* v___x_3373_; 
if (v_isShared_3356_ == 0)
{
lean_ctor_set(v___x_3355_, 5, v___x_3371_);
v___x_3373_ = v___x_3355_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_constants_3348_);
lean_ctor_set(v_reuseFailAlloc_3406_, 1, v_diagnostics_3350_);
lean_ctor_set(v_reuseFailAlloc_3406_, 2, v_const2ModIdx_3351_);
lean_ctor_set(v_reuseFailAlloc_3406_, 3, v_extensions_3352_);
lean_ctor_set(v_reuseFailAlloc_3406_, 4, v_irBaseExts_3353_);
lean_ctor_set(v_reuseFailAlloc_3406_, 5, v___x_3371_);
lean_ctor_set_uint8(v_reuseFailAlloc_3406_, sizeof(void*)*6, v_quotInit_3349_);
v___x_3373_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
lean_object* v___x_3375_; 
if (v_isShared_3347_ == 0)
{
lean_ctor_set(v___x_3346_, 0, v___x_3373_);
v___x_3375_ = v___x_3346_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v___x_3373_);
lean_ctor_set(v_reuseFailAlloc_3405_, 1, v_public_3344_);
v___x_3375_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
lean_object* v___x_3377_; 
if (v_isShared_3343_ == 0)
{
lean_ctor_set(v___x_3342_, 0, v___x_3375_);
v___x_3377_ = v___x_3342_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v___x_3375_);
lean_ctor_set(v_reuseFailAlloc_3404_, 1, v_serverBaseExts_3333_);
lean_ctor_set(v_reuseFailAlloc_3404_, 2, v_checked_3334_);
lean_ctor_set(v_reuseFailAlloc_3404_, 3, v_asyncConstsMap_3335_);
lean_ctor_set(v_reuseFailAlloc_3404_, 4, v_asyncCtx_x3f_3336_);
lean_ctor_set(v_reuseFailAlloc_3404_, 5, v_importRealizationCtx_x3f_3337_);
lean_ctor_set(v_reuseFailAlloc_3404_, 6, v_localRealizationCtxMap_3338_);
lean_ctor_set(v_reuseFailAlloc_3404_, 7, v_allRealizations_3339_);
lean_ctor_set_uint8(v_reuseFailAlloc_3404_, sizeof(void*)*8, v_isExporting_3340_);
v___x_3377_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v_env_3400_; lean_object* v___x_3401_; uint8_t v___x_3402_; uint8_t v___x_3403_; 
v___x_3378_ = l_Lean_Compiler_LCNF_postponedCompileDeclsExt;
v___x_3379_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2986_, v___x_3378_, v___x_3377_, v___y_3316_, v___x_3311_);
lean_dec(v___y_3316_);
v___x_3380_ = l_Lean_firstFrontendMacroScope;
v___x_3381_ = lean_obj_once(&l_main___closed__23, &l_main___closed__23_once, _init_l_main___closed__23);
v___x_3382_ = ((lean_object*)(l_main___closed__26));
lean_inc_n(v___y_3317_, 3);
v___x_3383_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3383_, 0, v___y_3317_);
lean_ctor_set(v___x_3383_, 1, v___x_3308_);
lean_ctor_set(v___x_3383_, 2, v___x_2979_);
v___x_3384_ = lean_obj_once(&l_main___closed__27, &l_main___closed__27_once, _init_l_main___closed__27);
v___x_3385_ = lean_obj_once(&l_main___closed__30, &l_main___closed__30_once, _init_l_main___closed__30);
v___x_3386_ = lean_obj_once(&l_main___closed__31, &l_main___closed__31_once, _init_l_main___closed__31);
v___x_3387_ = lean_obj_once(&l_main___closed__32, &l_main___closed__32_once, _init_l_main___closed__32);
v___x_3388_ = ((lean_object*)(l_main___closed__33));
lean_inc_ref(v___x_3383_);
v___x_3389_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3377_);
lean_ctor_set(v___x_3389_, 1, v___x_3381_);
lean_ctor_set(v___x_3389_, 2, v___x_3382_);
lean_ctor_set(v___x_3389_, 3, v___x_3383_);
lean_ctor_set(v___x_3389_, 4, v___x_3384_);
lean_ctor_set(v___x_3389_, 5, v___x_3385_);
lean_ctor_set(v___x_3389_, 6, v___x_3386_);
lean_ctor_set(v___x_3389_, 7, v___x_3387_);
lean_ctor_set(v___x_3389_, 8, v___x_3388_);
v___x_3390_ = lean_st_mk_ref(v___x_3389_);
v___x_3391_ = l_Lean_inheritedTraceOptions;
v___x_3392_ = lean_st_ref_get(v___x_3391_);
v___x_3393_ = lean_st_ref_get(v___x_3390_);
v___x_3394_ = l_Lean_instInhabitedFileMap_default;
v___x_3395_ = lean_unsigned_to_nat(1000u);
v___x_3396_ = lean_box(0);
v___x_3397_ = l_Lean_Core_getMaxHeartbeats(v___x_2992_);
v___x_3398_ = lean_box(0);
lean_inc_ref(v___x_2992_);
lean_inc(v_head_2951_);
v___x_3399_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3399_, 0, v_head_2951_);
lean_ctor_set(v___x_3399_, 1, v___x_3394_);
lean_ctor_set(v___x_3399_, 2, v___x_2992_);
lean_ctor_set(v___x_3399_, 3, v___x_2991_);
lean_ctor_set(v___x_3399_, 4, v___x_3395_);
lean_ctor_set(v___x_3399_, 5, v___x_3396_);
lean_ctor_set(v___x_3399_, 6, v___y_3317_);
lean_ctor_set(v___x_3399_, 7, v___x_2979_);
lean_ctor_set(v___x_3399_, 8, v___x_2991_);
lean_ctor_set(v___x_3399_, 9, v___x_3397_);
lean_ctor_set(v___x_3399_, 10, v___y_3317_);
lean_ctor_set(v___x_3399_, 11, v___x_3380_);
lean_ctor_set(v___x_3399_, 12, v___x_3398_);
lean_ctor_set(v___x_3399_, 13, v___x_3392_);
lean_ctor_set_uint8(v___x_3399_, sizeof(void*)*14, v___x_2965_);
lean_ctor_set_uint8(v___x_3399_, sizeof(void*)*14 + 1, v___x_2965_);
v_env_3400_ = lean_ctor_get(v___x_3393_, 0);
lean_inc_ref(v_env_3400_);
lean_dec(v___x_3393_);
v___x_3401_ = l_Lean_diagnostics;
v___x_3402_ = l_Lean_Option_get___at___00main_spec__8(v___x_2992_, v___x_3401_);
v___x_3403_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3400_);
lean_dec_ref(v_env_3400_);
if (v___x_3403_ == 0)
{
if (v___x_3402_ == 0)
{
v___y_3262_ = v___x_3398_;
v___y_3263_ = v___x_3327_;
v___y_3264_ = v___x_3380_;
v___y_3265_ = v___x_3396_;
v___y_3266_ = v___x_2979_;
v___y_3267_ = v___x_3391_;
v___y_3268_ = v___x_3385_;
v___y_3269_ = v___x_3394_;
v___y_3270_ = v___y_3313_;
v___y_3271_ = v___x_3383_;
v___y_3272_ = v___x_3388_;
v___y_3273_ = v___x_3385_;
v___y_3274_ = v___x_3384_;
v___y_3275_ = v___x_3378_;
v___y_3276_ = v___x_3382_;
v___y_3277_ = v___x_3381_;
v___y_3278_ = v___x_3402_;
v___y_3279_ = v___x_3399_;
v___y_3280_ = v___x_3390_;
v___y_3281_ = v___y_3317_;
v___y_3282_ = v___x_3387_;
v___y_3283_ = v___x_3379_;
v___y_3284_ = v___x_3386_;
v___y_3285_ = v___x_3327_;
goto v___jp_3261_;
}
else
{
v___y_3262_ = v___x_3398_;
v___y_3263_ = v___x_3327_;
v___y_3264_ = v___x_3380_;
v___y_3265_ = v___x_3396_;
v___y_3266_ = v___x_2979_;
v___y_3267_ = v___x_3391_;
v___y_3268_ = v___x_3385_;
v___y_3269_ = v___x_3394_;
v___y_3270_ = v___y_3313_;
v___y_3271_ = v___x_3383_;
v___y_3272_ = v___x_3388_;
v___y_3273_ = v___x_3385_;
v___y_3274_ = v___x_3384_;
v___y_3275_ = v___x_3378_;
v___y_3276_ = v___x_3382_;
v___y_3277_ = v___x_3381_;
v___y_3278_ = v___x_3402_;
v___y_3279_ = v___x_3399_;
v___y_3280_ = v___x_3390_;
v___y_3281_ = v___y_3317_;
v___y_3282_ = v___x_3387_;
v___y_3283_ = v___x_3379_;
v___y_3284_ = v___x_3386_;
v___y_3285_ = v___x_3403_;
goto v___jp_3261_;
}
}
else
{
v___y_3262_ = v___x_3398_;
v___y_3263_ = v___x_3327_;
v___y_3264_ = v___x_3380_;
v___y_3265_ = v___x_3396_;
v___y_3266_ = v___x_2979_;
v___y_3267_ = v___x_3391_;
v___y_3268_ = v___x_3385_;
v___y_3269_ = v___x_3394_;
v___y_3270_ = v___y_3313_;
v___y_3271_ = v___x_3383_;
v___y_3272_ = v___x_3388_;
v___y_3273_ = v___x_3385_;
v___y_3274_ = v___x_3384_;
v___y_3275_ = v___x_3378_;
v___y_3276_ = v___x_3382_;
v___y_3277_ = v___x_3381_;
v___y_3278_ = v___x_3402_;
v___y_3279_ = v___x_3399_;
v___y_3280_ = v___x_3390_;
v___y_3281_ = v___y_3317_;
v___y_3282_ = v___x_3387_;
v___y_3283_ = v___x_3379_;
v___y_3284_ = v___x_3386_;
v___y_3285_ = v___x_3402_;
goto v___jp_3261_;
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
v___jp_3417_:
{
lean_object* v___x_3422_; lean_object* v_toEnvExtension_3423_; lean_object* v_asyncMode_3424_; lean_object* v___x_3425_; lean_object* v_importedEntries_3426_; lean_object* v_state_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; uint8_t v___x_3430_; 
v___x_3422_ = l_Lean_IR_declMapExt;
v_toEnvExtension_3423_ = lean_ctor_get(v___x_3422_, 0);
v_asyncMode_3424_ = lean_ctor_get(v_toEnvExtension_3423_, 2);
lean_inc(v___y_3420_);
lean_inc_ref(v___y_3421_);
v___x_3425_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2983_, v_toEnvExtension_3423_, v___y_3421_, v_asyncMode_3424_, v___y_3420_);
v_importedEntries_3426_ = lean_ctor_get(v___x_3425_, 0);
lean_inc_ref(v_importedEntries_3426_);
v_state_3427_ = lean_ctor_get(v___x_3425_, 1);
lean_inc(v_state_3427_);
lean_dec(v___x_3425_);
v___x_3428_ = lean_array_get_borrowed(v___x_2984_, v_importedEntries_3426_, v___y_3419_);
v___x_3429_ = lean_array_get_size(v___x_3428_);
v___x_3430_ = lean_nat_dec_lt(v___x_2991_, v___x_3429_);
if (v___x_3430_ == 0)
{
v___y_3313_ = v___y_3418_;
v___y_3314_ = v_importedEntries_3426_;
v___y_3315_ = v___y_3421_;
v___y_3316_ = v___y_3419_;
v___y_3317_ = v___y_3420_;
v___y_3318_ = v_toEnvExtension_3423_;
v___y_3319_ = v_state_3427_;
goto v___jp_3312_;
}
else
{
uint8_t v___x_3431_; 
v___x_3431_ = lean_nat_dec_le(v___x_3429_, v___x_3429_);
if (v___x_3431_ == 0)
{
if (v___x_3430_ == 0)
{
v___y_3313_ = v___y_3418_;
v___y_3314_ = v_importedEntries_3426_;
v___y_3315_ = v___y_3421_;
v___y_3316_ = v___y_3419_;
v___y_3317_ = v___y_3420_;
v___y_3318_ = v_toEnvExtension_3423_;
v___y_3319_ = v_state_3427_;
goto v___jp_3312_;
}
else
{
size_t v___x_3432_; size_t v___x_3433_; lean_object* v___x_3434_; 
v___x_3432_ = ((size_t)0ULL);
v___x_3433_ = lean_usize_of_nat(v___x_3429_);
lean_inc_ref(v___y_3421_);
v___x_3434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3421_, v___x_3428_, v___x_3432_, v___x_3433_, v_state_3427_);
v___y_3313_ = v___y_3418_;
v___y_3314_ = v_importedEntries_3426_;
v___y_3315_ = v___y_3421_;
v___y_3316_ = v___y_3419_;
v___y_3317_ = v___y_3420_;
v___y_3318_ = v_toEnvExtension_3423_;
v___y_3319_ = v___x_3434_;
goto v___jp_3312_;
}
}
else
{
size_t v___x_3435_; size_t v___x_3436_; lean_object* v___x_3437_; 
v___x_3435_ = ((size_t)0ULL);
v___x_3436_ = lean_usize_of_nat(v___x_3429_);
lean_inc_ref(v___y_3421_);
v___x_3437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3421_, v___x_3428_, v___x_3435_, v___x_3436_, v_state_3427_);
v___y_3313_ = v___y_3418_;
v___y_3314_ = v_importedEntries_3426_;
v___y_3315_ = v___y_3421_;
v___y_3316_ = v___y_3419_;
v___y_3317_ = v___y_3420_;
v___y_3318_ = v_toEnvExtension_3423_;
v___y_3319_ = v___x_3437_;
goto v___jp_3312_;
}
}
}
v___jp_3438_:
{
uint8_t v___x_3445_; 
v___x_3445_ = lean_nat_dec_lt(v___x_2991_, v___y_3441_);
if (v___x_3445_ == 0)
{
lean_dec(v___y_3441_);
lean_dec_ref(v___y_3440_);
v___y_3418_ = v___y_3439_;
v___y_3419_ = v___y_3442_;
v___y_3420_ = v___y_3443_;
v___y_3421_ = v___y_3444_;
goto v___jp_3417_;
}
else
{
uint8_t v___x_3446_; 
v___x_3446_ = lean_nat_dec_le(v___y_3441_, v___y_3441_);
if (v___x_3446_ == 0)
{
if (v___x_3445_ == 0)
{
lean_dec(v___y_3441_);
lean_dec_ref(v___y_3440_);
v___y_3418_ = v___y_3439_;
v___y_3419_ = v___y_3442_;
v___y_3420_ = v___y_3443_;
v___y_3421_ = v___y_3444_;
goto v___jp_3417_;
}
else
{
size_t v___x_3447_; size_t v___x_3448_; lean_object* v___x_3449_; 
v___x_3447_ = ((size_t)0ULL);
v___x_3448_ = lean_usize_of_nat(v___y_3441_);
lean_dec(v___y_3441_);
v___x_3449_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3440_, v___x_3447_, v___x_3448_, v___y_3444_);
lean_dec_ref(v___y_3440_);
v___y_3418_ = v___y_3439_;
v___y_3419_ = v___y_3442_;
v___y_3420_ = v___y_3443_;
v___y_3421_ = v___x_3449_;
goto v___jp_3417_;
}
}
else
{
size_t v___x_3450_; size_t v___x_3451_; lean_object* v___x_3452_; 
v___x_3450_ = ((size_t)0ULL);
v___x_3451_ = lean_usize_of_nat(v___y_3441_);
lean_dec(v___y_3441_);
v___x_3452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3440_, v___x_3450_, v___x_3451_, v___y_3444_);
lean_dec_ref(v___y_3440_);
v___y_3418_ = v___y_3439_;
v___y_3419_ = v___y_3442_;
v___y_3420_ = v___y_3443_;
v___y_3421_ = v___x_3452_;
goto v___jp_3417_;
}
}
}
v___jp_3453_:
{
lean_object* v___x_3459_; uint8_t v___x_3460_; 
v___x_3459_ = lean_array_get_size(v___y_3458_);
v___x_3460_ = lean_nat_dec_lt(v___x_2991_, v___x_3459_);
if (v___x_3460_ == 0)
{
v___y_3439_ = v___y_3455_;
v___y_3440_ = v___y_3458_;
v___y_3441_ = v___x_3459_;
v___y_3442_ = v___y_3454_;
v___y_3443_ = v___y_3457_;
v___y_3444_ = v___y_3456_;
goto v___jp_3438_;
}
else
{
uint8_t v___x_3461_; 
v___x_3461_ = lean_nat_dec_le(v___x_3459_, v___x_3459_);
if (v___x_3461_ == 0)
{
if (v___x_3460_ == 0)
{
v___y_3439_ = v___y_3455_;
v___y_3440_ = v___y_3458_;
v___y_3441_ = v___x_3459_;
v___y_3442_ = v___y_3454_;
v___y_3443_ = v___y_3457_;
v___y_3444_ = v___y_3456_;
goto v___jp_3438_;
}
else
{
size_t v___x_3462_; size_t v___x_3463_; lean_object* v___x_3464_; 
v___x_3462_ = ((size_t)0ULL);
v___x_3463_ = lean_usize_of_nat(v___x_3459_);
v___x_3464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v___y_3458_, v___x_3462_, v___x_3463_, v___y_3456_);
v___y_3439_ = v___y_3455_;
v___y_3440_ = v___y_3458_;
v___y_3441_ = v___x_3459_;
v___y_3442_ = v___y_3454_;
v___y_3443_ = v___y_3457_;
v___y_3444_ = v___x_3464_;
goto v___jp_3438_;
}
}
else
{
size_t v___x_3465_; size_t v___x_3466_; lean_object* v___x_3467_; 
v___x_3465_ = ((size_t)0ULL);
v___x_3466_ = lean_usize_of_nat(v___x_3459_);
v___x_3467_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v___y_3458_, v___x_3465_, v___x_3466_, v___y_3456_);
v___y_3439_ = v___y_3455_;
v___y_3440_ = v___y_3458_;
v___y_3441_ = v___x_3459_;
v___y_3442_ = v___y_3454_;
v___y_3443_ = v___y_3457_;
v___y_3444_ = v___x_3467_;
goto v___jp_3438_;
}
}
}
v___jp_3469_:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___f_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; 
v___x_3471_ = l_Lean_instInhabitedImportState_default;
v___x_3472_ = lean_box(v___x_3311_);
v___x_3473_ = lean_box(v___y_3470_);
v___x_3474_ = lean_box(v___x_2988_);
v___x_3475_ = lean_box(v___x_3468_);
v___x_3476_ = lean_box(v___x_2965_);
lean_inc_ref(v___x_2992_);
lean_inc(v_name_2962_);
v___f_3477_ = lean_alloc_closure((void*)(l_main___lam__0___boxed), 11, 10);
lean_closure_set(v___f_3477_, 0, v___x_3471_);
lean_closure_set(v___f_3477_, 1, v___x_3310_);
lean_closure_set(v___f_3477_, 2, v___x_3472_);
lean_closure_set(v___f_3477_, 3, v_importArts_2963_);
lean_closure_set(v___f_3477_, 4, v___x_3473_);
lean_closure_set(v___f_3477_, 5, v___x_3474_);
lean_closure_set(v___f_3477_, 6, v_name_2962_);
lean_closure_set(v___f_3477_, 7, v___x_3475_);
lean_closure_set(v___f_3477_, 8, v___x_2992_);
lean_closure_set(v___f_3477_, 9, v___x_3476_);
v___x_3478_ = lean_alloc_closure((void*)(l_Lean_withImporting___boxed), 3, 2);
lean_closure_set(v___x_3478_, 0, lean_box(0));
lean_closure_set(v___x_3478_, 1, v___f_3477_);
v___x_3479_ = lean_box(0);
v___x_3480_ = l_Lean_profileitIOUnsafe___redArg(v___x_3306_, v___x_2992_, v___x_3478_, v___x_3479_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v_a_3481_; lean_object* v___x_3482_; lean_object* v_ext_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v_a_3481_ = lean_ctor_get(v___x_3480_, 0);
lean_inc(v_a_3481_);
lean_dec_ref_known(v___x_3480_, 1);
v___x_3482_ = l_Lean_Compiler_CSimp_ext;
v_ext_3483_ = lean_ctor_get(v___x_3482_, 1);
lean_inc(v_name_2962_);
v___x_3484_ = l_Lean_Environment_setMainModule(v_a_3481_, v_name_2962_);
lean_inc_ref(v_ext_3483_);
v___x_3485_ = l_main___elam__0___redArg(v___x_3479_, v___x_2978_, v_ext_3483_, v___x_3484_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v_a_3486_; lean_object* v___x_3487_; lean_object* v_ext_3488_; lean_object* v___x_3489_; 
v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
lean_inc(v_a_3486_);
lean_dec_ref_known(v___x_3485_, 1);
v___x_3487_ = l_Lean_Meta_instanceExtension;
v_ext_3488_ = lean_ctor_get(v___x_3487_, 1);
lean_inc_ref(v_ext_3488_);
v___x_3489_ = l_main___elam__0___redArg(v___x_3479_, v___x_2978_, v_ext_3488_, v_a_3486_);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v_a_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; 
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
lean_inc(v_a_3490_);
lean_dec_ref_known(v___x_3489_, 1);
v___x_3491_ = l_Lean_classExtension;
v___x_3492_ = l_main___elam__0___redArg(v___x_3479_, v___x_2980_, v___x_3491_, v_a_3490_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
lean_inc(v_a_3493_);
lean_dec_ref_known(v___x_3492_, 1);
v___x_3494_ = l_Lean_Meta_Match_Extension_extension;
v___x_3495_ = l_main___elam__0___redArg(v___x_3479_, v___x_2981_, v___x_3494_, v_a_3493_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3523_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3498_ = v___x_3495_;
v_isShared_3499_ = v_isSharedCheck_3523_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3495_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3523_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3500_; 
v___x_3500_ = l_Lean_Environment_getModuleIdx_x3f(v_a_3496_, v_name_2962_);
if (lean_obj_tag(v___x_3500_) == 1)
{
lean_object* v_val_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; uint8_t v___x_3506_; 
lean_del_object(v___x_3498_);
v_val_3501_ = lean_ctor_get(v___x_3500_, 0);
lean_inc(v_val_3501_);
lean_dec_ref_known(v___x_3500_, 1);
v___x_3502_ = l_Lean_Compiler_LCNF_impureSigExt;
v___x_3503_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2982_, v___x_3502_, v_a_3496_, v_val_3501_, v___x_3311_);
v___x_3504_ = lean_array_get_size(v___x_3503_);
v___x_3505_ = ((lean_object*)(l_main___closed__34));
v___x_3506_ = lean_nat_dec_lt(v___x_2991_, v___x_3504_);
if (v___x_3506_ == 0)
{
lean_dec_ref(v___x_3503_);
v___y_3454_ = v_val_3501_;
v___y_3455_ = v___x_3479_;
v___y_3456_ = v_a_3496_;
v___y_3457_ = v___x_3479_;
v___y_3458_ = v___x_3505_;
goto v___jp_3453_;
}
else
{
uint8_t v___x_3507_; 
v___x_3507_ = lean_nat_dec_le(v___x_3504_, v___x_3504_);
if (v___x_3507_ == 0)
{
if (v___x_3506_ == 0)
{
lean_dec_ref(v___x_3503_);
v___y_3454_ = v_val_3501_;
v___y_3455_ = v___x_3479_;
v___y_3456_ = v_a_3496_;
v___y_3457_ = v___x_3479_;
v___y_3458_ = v___x_3505_;
goto v___jp_3453_;
}
else
{
size_t v___x_3508_; size_t v___x_3509_; lean_object* v___x_3510_; 
v___x_3508_ = ((size_t)0ULL);
v___x_3509_ = lean_usize_of_nat(v___x_3504_);
lean_inc(v_a_3496_);
v___x_3510_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_3496_, v___x_3503_, v___x_3508_, v___x_3509_, v___x_3505_);
lean_dec_ref(v___x_3503_);
v___y_3454_ = v_val_3501_;
v___y_3455_ = v___x_3479_;
v___y_3456_ = v_a_3496_;
v___y_3457_ = v___x_3479_;
v___y_3458_ = v___x_3510_;
goto v___jp_3453_;
}
}
else
{
size_t v___x_3511_; size_t v___x_3512_; lean_object* v___x_3513_; 
v___x_3511_ = ((size_t)0ULL);
v___x_3512_ = lean_usize_of_nat(v___x_3504_);
lean_inc(v_a_3496_);
v___x_3513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_3496_, v___x_3503_, v___x_3511_, v___x_3512_, v___x_3505_);
lean_dec_ref(v___x_3503_);
v___y_3454_ = v_val_3501_;
v___y_3455_ = v___x_3479_;
v___y_3456_ = v_a_3496_;
v___y_3457_ = v___x_3479_;
v___y_3458_ = v___x_3513_;
goto v___jp_3453_;
}
}
}
else
{
lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3521_; 
lean_dec(v___x_3500_);
lean_dec(v_a_3496_);
lean_dec_ref(v___x_2992_);
lean_del_object(v___x_2976_);
lean_dec(v_fst_2973_);
lean_dec(v_head_2955_);
lean_del_object(v___x_2953_);
lean_dec(v_head_2951_);
lean_del_object(v___x_2949_);
v___x_3514_ = ((lean_object*)(l_main___closed__35));
v___x_3515_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2962_, v___x_2988_);
v___x_3516_ = lean_string_append(v___x_3514_, v___x_3515_);
lean_dec_ref(v___x_3515_);
v___x_3517_ = ((lean_object*)(l_main___closed__36));
v___x_3518_ = lean_string_append(v___x_3516_, v___x_3517_);
v___x_3519_ = lean_mk_io_user_error(v___x_3518_);
if (v_isShared_3499_ == 0)
{
lean_ctor_set_tag(v___x_3498_, 1);
lean_ctor_set(v___x_3498_, 0, v___x_3519_);
v___x_3521_ = v___x_3498_;
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
else
{
lean_object* v_a_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3531_; 
lean_dec_ref(v___x_2992_);
lean_del_object(v___x_2976_);
lean_dec(v_fst_2973_);
lean_dec(v_name_2962_);
lean_dec(v_head_2955_);
lean_del_object(v___x_2953_);
lean_dec(v_head_2951_);
lean_del_object(v___x_2949_);
v_a_3524_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3526_ = v___x_3495_;
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_a_3524_);
lean_dec(v___x_3495_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v___x_3529_; 
if (v_isShared_3527_ == 0)
{
v___x_3529_ = v___x_3526_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v_a_3524_);
v___x_3529_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
return v___x_3529_;
}
}
}
}
else
{
lean_object* v_a_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3539_; 
lean_dec_ref(v___x_2992_);
lean_del_object(v___x_2976_);
lean_dec(v_fst_2973_);
lean_dec(v_name_2962_);
lean_dec(v_head_2955_);
lean_del_object(v___x_2953_);
lean_dec(v_head_2951_);
lean_del_object(v___x_2949_);
v_a_3532_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3534_ = v___x_3492_;
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_a_3532_);
lean_dec(v___x_3492_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3537_; 
if (v_isShared_3535_ == 0)
{
v___x_3537_ = v___x_3534_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_a_3532_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
}
else
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
lean_dec_ref(v___x_2992_);
lean_del_object(v___x_2976_);
lean_dec(v_fst_2973_);
lean_dec(v_name_2962_);
lean_dec(v_head_2955_);
lean_del_object(v___x_2953_);
lean_dec(v_head_2951_);
lean_del_object(v___x_2949_);
v_a_3540_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3542_ = v___x_3489_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3489_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3545_; 
if (v_isShared_3543_ == 0)
{
v___x_3545_ = v___x_3542_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_a_3540_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
}
else
{
lean_object* v_a_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3555_; 
lean_dec_ref(v___x_2992_);
lean_del_object(v___x_2976_);
lean_dec(v_fst_2973_);
lean_dec(v_name_2962_);
lean_dec(v_head_2955_);
lean_del_object(v___x_2953_);
lean_dec(v_head_2951_);
lean_del_object(v___x_2949_);
v_a_3548_ = lean_ctor_get(v___x_3485_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3550_ = v___x_3485_;
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_a_3548_);
lean_dec(v___x_3485_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3553_; 
if (v_isShared_3551_ == 0)
{
v___x_3553_ = v___x_3550_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_a_3548_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
}
else
{
lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3563_; 
lean_dec_ref(v___x_2992_);
lean_del_object(v___x_2976_);
lean_dec(v_fst_2973_);
lean_dec(v_name_2962_);
lean_dec(v_head_2955_);
lean_del_object(v___x_2953_);
lean_dec(v_head_2951_);
lean_del_object(v___x_2949_);
v_a_3556_ = lean_ctor_get(v___x_3480_, 0);
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3558_ = v___x_3480_;
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3480_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3561_; 
if (v_isShared_3559_ == 0)
{
v___x_3561_ = v___x_3558_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_a_3556_);
v___x_3561_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
return v___x_3561_;
}
}
}
}
}
}
else
{
lean_object* v_a_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3573_; 
lean_dec(v_a_2971_);
lean_dec(v_importArts_2963_);
lean_dec(v_name_2962_);
lean_dec(v_head_2955_);
lean_del_object(v___x_2953_);
lean_dec(v_head_2951_);
lean_del_object(v___x_2949_);
v_a_3566_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_3573_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3568_ = v___x_2972_;
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_a_3566_);
lean_dec(v___x_2972_);
v___x_3568_ = lean_box(0);
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
v_resetjp_3567_:
{
lean_object* v___x_3571_; 
if (v_isShared_3569_ == 0)
{
v___x_3571_ = v___x_3568_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v_a_3566_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
return v___x_3571_;
}
}
}
}
else
{
lean_object* v_a_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3581_; 
lean_dec(v_importArts_2963_);
lean_dec(v_name_2962_);
lean_dec(v_head_2955_);
lean_del_object(v___x_2953_);
lean_dec(v_head_2951_);
lean_del_object(v___x_2949_);
v_a_3574_ = lean_ctor_get(v___x_2970_, 0);
v_isSharedCheck_3581_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3576_ = v___x_2970_;
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_a_3574_);
lean_dec(v___x_2970_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v___x_3579_; 
if (v_isShared_3577_ == 0)
{
v___x_3579_ = v___x_3576_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v_a_3574_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
return v___x_3579_;
}
}
}
}
}
else
{
lean_object* v_a_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3590_; 
lean_del_object(v___x_2958_);
lean_dec(v_tail_2956_);
lean_dec(v_head_2955_);
lean_del_object(v___x_2953_);
lean_dec(v_head_2951_);
lean_del_object(v___x_2949_);
v_a_3583_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3585_ = v___x_2960_;
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_a_3583_);
lean_dec(v___x_2960_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3588_; 
if (v_isShared_3586_ == 0)
{
v___x_3588_ = v___x_3585_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_a_3583_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_tail_2945_, 2);
lean_dec(v_tail_2946_);
lean_dec_ref_known(v_args_2920_, 2);
goto v___jp_2922_;
}
}
else
{
lean_dec(v_tail_2945_);
lean_dec_ref_known(v_args_2920_, 2);
goto v___jp_2922_;
}
}
else
{
lean_dec(v_args_2920_);
goto v___jp_2922_;
}
v___jp_2922_:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___x_2923_ = ((lean_object*)(l_main___closed__0));
v___x_2924_ = l_IO_println___at___00Lean_Environment_displayStats_spec__1(v___x_2923_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2932_; 
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2932_ == 0)
{
lean_object* v_unused_2933_; 
v_unused_2933_ = lean_ctor_get(v___x_2924_, 0);
lean_dec(v_unused_2933_);
v___x_2926_ = v___x_2924_;
v_isShared_2927_ = v_isSharedCheck_2932_;
goto v_resetjp_2925_;
}
else
{
lean_dec(v___x_2924_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2932_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2928_; lean_object* v___x_2930_; 
v___x_2928_ = l_main___boxed__const__1;
if (v_isShared_2927_ == 0)
{
lean_ctor_set(v___x_2926_, 0, v___x_2928_);
v___x_2930_ = v___x_2926_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v___x_2928_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
else
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
v_a_2934_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2924_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2924_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
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
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
v___jp_2942_:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; 
v___x_2943_ = l_main___boxed__const__2;
v___x_2944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2943_);
return v___x_2944_;
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_3596_, lean_object* v_a_3597_){
_start:
{
lean_object* v_res_3598_; 
v_res_3598_ = _lean_main(v_args_3596_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1(lean_object* v_as_3599_, lean_object* v_as_x27_3600_, lean_object* v_b_3601_, lean_object* v_a_3602_){
_start:
{
lean_object* v___x_3604_; 
v___x_3604_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_3600_, v_b_3601_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___boxed(lean_object* v_as_3605_, lean_object* v_as_x27_3606_, lean_object* v_b_3607_, lean_object* v_a_3608_, lean_object* v___y_3609_){
_start:
{
lean_object* v_res_3610_; 
v_res_3610_ = l_List_forIn_x27_loop___at___00main_spec__1(v_as_3605_, v_as_x27_3606_, v_b_3607_, v_a_3608_);
lean_dec(v_as_x27_3606_);
lean_dec(v_as_3605_);
return v_res_3610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16(lean_object* v___y_3611_, lean_object* v___y_3612_){
_start:
{
lean_object* v___x_3614_; 
v___x_3614_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_3612_);
return v___x_3614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___boxed(lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_){
_start:
{
lean_object* v_res_3618_; 
v_res_3618_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16(v___y_3615_, v___y_3616_);
lean_dec(v___y_3616_);
lean_dec_ref(v___y_3615_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17(lean_object* v_00_u03b2_3619_, lean_object* v_m_3620_, lean_object* v_a_3621_, lean_object* v_fallback_3622_){
_start:
{
lean_object* v___x_3623_; 
v___x_3623_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_m_3620_, v_a_3621_, v_fallback_3622_);
return v___x_3623_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___boxed(lean_object* v_00_u03b2_3624_, lean_object* v_m_3625_, lean_object* v_a_3626_, lean_object* v_fallback_3627_){
_start:
{
lean_object* v_res_3628_; 
v_res_3628_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17(v_00_u03b2_3624_, v_m_3625_, v_a_3626_, v_fallback_3627_);
lean_dec(v_fallback_3627_);
lean_dec_ref(v_a_3626_);
lean_dec_ref(v_m_3625_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18(lean_object* v_00_u03b2_3629_, lean_object* v_m_3630_, lean_object* v_a_3631_, lean_object* v_b_3632_){
_start:
{
lean_object* v___x_3633_; 
v___x_3633_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_m_3630_, v_a_3631_, v_b_3632_);
return v___x_3633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21(lean_object* v_n_3634_, lean_object* v_as_3635_, lean_object* v_lo_3636_, lean_object* v_hi_3637_, lean_object* v_w_3638_, lean_object* v_hlo_3639_, lean_object* v_hhi_3640_){
_start:
{
lean_object* v___x_3641_; 
v___x_3641_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_3634_, v_as_3635_, v_lo_3636_, v_hi_3637_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___boxed(lean_object* v_n_3642_, lean_object* v_as_3643_, lean_object* v_lo_3644_, lean_object* v_hi_3645_, lean_object* v_w_3646_, lean_object* v_hlo_3647_, lean_object* v_hhi_3648_){
_start:
{
lean_object* v_res_3649_; 
v_res_3649_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21(v_n_3642_, v_as_3643_, v_lo_3644_, v_hi_3645_, v_w_3646_, v_hlo_3647_, v_hhi_3648_);
lean_dec(v_hi_3645_);
lean_dec(v_n_3642_);
return v_res_3649_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21(lean_object* v_00_u03b2_3650_, lean_object* v_a_3651_, lean_object* v_fallback_3652_, lean_object* v_x_3653_){
_start:
{
lean_object* v___x_3654_; 
v___x_3654_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_3651_, v_fallback_3652_, v_x_3653_);
return v___x_3654_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___boxed(lean_object* v_00_u03b2_3655_, lean_object* v_a_3656_, lean_object* v_fallback_3657_, lean_object* v_x_3658_){
_start:
{
lean_object* v_res_3659_; 
v_res_3659_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21(v_00_u03b2_3655_, v_a_3656_, v_fallback_3657_, v_x_3658_);
lean_dec(v_x_3658_);
lean_dec(v_fallback_3657_);
lean_dec_ref(v_a_3656_);
return v_res_3659_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23(lean_object* v_00_u03b2_3660_, lean_object* v_a_3661_, lean_object* v_x_3662_){
_start:
{
uint8_t v___x_3663_; 
v___x_3663_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_3661_, v_x_3662_);
return v___x_3663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___boxed(lean_object* v_00_u03b2_3664_, lean_object* v_a_3665_, lean_object* v_x_3666_){
_start:
{
uint8_t v_res_3667_; lean_object* v_r_3668_; 
v_res_3667_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23(v_00_u03b2_3664_, v_a_3665_, v_x_3666_);
lean_dec(v_x_3666_);
lean_dec_ref(v_a_3665_);
v_r_3668_ = lean_box(v_res_3667_);
return v_r_3668_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24(lean_object* v_00_u03b2_3669_, lean_object* v_data_3670_){
_start:
{
lean_object* v___x_3671_; 
v___x_3671_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(v_data_3670_);
return v___x_3671_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25(lean_object* v_00_u03b2_3672_, lean_object* v_a_3673_, lean_object* v_b_3674_, lean_object* v_x_3675_){
_start:
{
lean_object* v___x_3676_; 
v___x_3676_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_3673_, v_b_3674_, v_x_3675_);
return v___x_3676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31(lean_object* v_n_3677_, lean_object* v_lo_3678_, lean_object* v_hi_3679_, lean_object* v_hhi_3680_, lean_object* v_pivot_3681_, lean_object* v_as_3682_, lean_object* v_i_3683_, lean_object* v_k_3684_, lean_object* v_ilo_3685_, lean_object* v_ik_3686_, lean_object* v_w_3687_){
_start:
{
lean_object* v___x_3688_; 
v___x_3688_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_3679_, v_pivot_3681_, v_as_3682_, v_i_3683_, v_k_3684_);
return v___x_3688_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___boxed(lean_object* v_n_3689_, lean_object* v_lo_3690_, lean_object* v_hi_3691_, lean_object* v_hhi_3692_, lean_object* v_pivot_3693_, lean_object* v_as_3694_, lean_object* v_i_3695_, lean_object* v_k_3696_, lean_object* v_ilo_3697_, lean_object* v_ik_3698_, lean_object* v_w_3699_){
_start:
{
lean_object* v_res_3700_; 
v_res_3700_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31(v_n_3689_, v_lo_3690_, v_hi_3691_, v_hhi_3692_, v_pivot_3693_, v_as_3694_, v_i_3695_, v_k_3696_, v_ilo_3697_, v_ik_3698_, v_w_3699_);
lean_dec_ref(v_pivot_3693_);
lean_dec(v_hi_3691_);
lean_dec(v_lo_3690_);
lean_dec(v_n_3689_);
return v_res_3700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40(lean_object* v_as_3701_, size_t v_sz_3702_, size_t v_i_3703_, lean_object* v_b_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_){
_start:
{
lean_object* v___x_3708_; 
v___x_3708_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_3701_, v_sz_3702_, v_i_3703_, v_b_3704_, v___y_3705_);
return v___x_3708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___boxed(lean_object* v_as_3709_, lean_object* v_sz_3710_, lean_object* v_i_3711_, lean_object* v_b_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_){
_start:
{
size_t v_sz_boxed_3716_; size_t v_i_boxed_3717_; lean_object* v_res_3718_; 
v_sz_boxed_3716_ = lean_unbox_usize(v_sz_3710_);
lean_dec(v_sz_3710_);
v_i_boxed_3717_ = lean_unbox_usize(v_i_3711_);
lean_dec(v_i_3711_);
v_res_3718_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40(v_as_3709_, v_sz_boxed_3716_, v_i_boxed_3717_, v_b_3712_, v___y_3713_, v___y_3714_);
lean_dec(v___y_3714_);
lean_dec_ref(v___y_3713_);
lean_dec_ref(v_as_3709_);
return v_res_3718_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35(lean_object* v_00_u03b2_3719_, lean_object* v_i_3720_, lean_object* v_source_3721_, lean_object* v_target_3722_){
_start:
{
lean_object* v___x_3723_; 
v___x_3723_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(v_i_3720_, v_source_3721_, v_target_3722_);
return v___x_3723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42(uint8_t v___x_3724_, lean_object* v_as_3725_, size_t v_sz_3726_, size_t v_i_3727_, lean_object* v_b_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_){
_start:
{
lean_object* v___x_3732_; 
v___x_3732_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_3724_, v_as_3725_, v_sz_3726_, v_i_3727_, v_b_3728_, v___y_3729_);
return v___x_3732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___boxed(lean_object* v___x_3733_, lean_object* v_as_3734_, lean_object* v_sz_3735_, lean_object* v_i_3736_, lean_object* v_b_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_){
_start:
{
uint8_t v___x_40698__boxed_3741_; size_t v_sz_boxed_3742_; size_t v_i_boxed_3743_; lean_object* v_res_3744_; 
v___x_40698__boxed_3741_ = lean_unbox(v___x_3733_);
v_sz_boxed_3742_ = lean_unbox_usize(v_sz_3735_);
lean_dec(v_sz_3735_);
v_i_boxed_3743_ = lean_unbox_usize(v_i_3736_);
lean_dec(v_i_3736_);
v_res_3744_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42(v___x_40698__boxed_3741_, v_as_3734_, v_sz_boxed_3742_, v_i_boxed_3743_, v_b_3737_, v___y_3738_, v___y_3739_);
lean_dec(v___y_3739_);
lean_dec_ref(v___y_3738_);
lean_dec_ref(v_as_3734_);
return v_res_3744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51(lean_object* v_as_3745_, size_t v_sz_3746_, size_t v_i_3747_, lean_object* v_b_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_){
_start:
{
lean_object* v___x_3752_; 
v___x_3752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_3745_, v_sz_3746_, v_i_3747_, v_b_3748_, v___y_3749_);
return v___x_3752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___boxed(lean_object* v_as_3753_, lean_object* v_sz_3754_, lean_object* v_i_3755_, lean_object* v_b_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_){
_start:
{
size_t v_sz_boxed_3760_; size_t v_i_boxed_3761_; lean_object* v_res_3762_; 
v_sz_boxed_3760_ = lean_unbox_usize(v_sz_3754_);
lean_dec(v_sz_3754_);
v_i_boxed_3761_ = lean_unbox_usize(v_i_3755_);
lean_dec(v_i_3755_);
v_res_3762_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51(v_as_3753_, v_sz_boxed_3760_, v_i_boxed_3761_, v_b_3756_, v___y_3757_, v___y_3758_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec_ref(v_as_3753_);
return v_res_3762_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44(lean_object* v_00_u03b2_3763_, lean_object* v_x_3764_, lean_object* v_x_3765_){
_start:
{
lean_object* v___x_3766_; 
v___x_3766_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(v_x_3764_, v_x_3765_);
return v___x_3766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49(uint8_t v___x_3767_, lean_object* v_as_3768_, size_t v_sz_3769_, size_t v_i_3770_, lean_object* v_b_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_){
_start:
{
lean_object* v___x_3775_; 
v___x_3775_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_3767_, v_as_3768_, v_sz_3769_, v_i_3770_, v_b_3771_, v___y_3772_);
return v___x_3775_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___boxed(lean_object* v___x_3776_, lean_object* v_as_3777_, lean_object* v_sz_3778_, lean_object* v_i_3779_, lean_object* v_b_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_){
_start:
{
uint8_t v___x_40729__boxed_3784_; size_t v_sz_boxed_3785_; size_t v_i_boxed_3786_; lean_object* v_res_3787_; 
v___x_40729__boxed_3784_ = lean_unbox(v___x_3776_);
v_sz_boxed_3785_ = lean_unbox_usize(v_sz_3778_);
lean_dec(v_sz_3778_);
v_i_boxed_3786_ = lean_unbox_usize(v_i_3779_);
lean_dec(v_i_3779_);
v_res_3787_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49(v___x_40729__boxed_3784_, v_as_3777_, v_sz_boxed_3785_, v_i_boxed_3786_, v_b_3780_, v___y_3781_, v___y_3782_);
lean_dec(v___y_3782_);
lean_dec_ref(v___y_3781_);
lean_dec_ref(v_as_3777_);
return v_res_3787_;
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
