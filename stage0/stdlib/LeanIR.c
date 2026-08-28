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
lean_object* lean_string_utf8_byte_size(lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
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
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_setOption(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_main___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_main___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_main___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "internal exception "};
static const lean_object* l_main___lam__1___closed__0 = (const lean_object*)&l_main___lam__1___closed__0_value;
static const lean_string_object l_main___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l_main___lam__1___closed__1 = (const lean_object*)&l_main___lam__1___closed__1_value;
static const lean_string_object l_main___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " (unknown)"};
static const lean_object* l_main___lam__1___closed__2 = (const lean_object*)&l_main___lam__1___closed__2_value;
LEAN_EXPORT lean_object* l_main___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
lean_object* v___x_359_; lean_object* v___x_18417__overap_360_; lean_object* v___x_361_; 
v___x_359_ = lean_obj_once(&l_panic___at___00main_spec__5___closed__0, &l_panic___at___00main_spec__5___closed__0_once, _init_l_panic___at___00main_spec__5___closed__0);
v___x_18417__overap_360_ = lean_panic_fn_borrowed(v___x_359_, v_msg_357_);
v___x_361_ = lean_apply_1(v___x_18417__overap_360_, lean_box(0));
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
uint8_t v___x_35139__boxed_512_; uint8_t v___y_35140__boxed_513_; uint8_t v___x_35141__boxed_514_; uint8_t v___x_35142__boxed_515_; uint8_t v___x_35144__boxed_516_; lean_object* v_res_517_; 
v___x_35139__boxed_512_ = lean_unbox(v___x_503_);
v___y_35140__boxed_513_ = lean_unbox(v___y_505_);
v___x_35141__boxed_514_ = lean_unbox(v___x_506_);
v___x_35142__boxed_515_ = lean_unbox(v___x_508_);
v___x_35144__boxed_516_ = lean_unbox(v___x_510_);
v_res_517_ = l_main___lam__0(v___x_501_, v___x_502_, v___x_35139__boxed_512_, v_importArts_504_, v___y_35140__boxed_513_, v___x_35141__boxed_514_, v_name_507_, v___x_35142__boxed_515_, v___x_509_, v___x_35144__boxed_516_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_main___lam__1(lean_object* v___x_521_, lean_object* v___x_522_, lean_object* v___x_523_, lean_object* v_name_524_, lean_object* v_a_525_, uint8_t v___x_526_, lean_object* v___x_527_, lean_object* v_head_528_, lean_object* v___x_529_, lean_object* v___x_530_, lean_object* v___x_531_, lean_object* v___x_532_, lean_object* v___x_533_, lean_object* v___x_534_, lean_object* v___x_535_, lean_object* v___x_536_, uint8_t v___x_537_){
_start:
{
lean_object* v_a_540_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v_env_547_; lean_object* v___x_548_; uint8_t v___x_549_; lean_object* v_fileName_551_; lean_object* v_fileMap_552_; lean_object* v_currRecDepth_553_; lean_object* v_ref_554_; lean_object* v_currNamespace_555_; lean_object* v_openDecls_556_; lean_object* v_initHeartbeats_557_; lean_object* v_maxHeartbeats_558_; lean_object* v_quotContext_559_; lean_object* v_currMacroScope_560_; lean_object* v_cancelTk_x3f_561_; uint8_t v_suppressElabErrors_562_; lean_object* v_inheritedTraceOptions_563_; lean_object* v___y_564_; uint8_t v___y_596_; uint8_t v___x_616_; 
v___x_543_ = lean_io_get_num_heartbeats();
v___x_544_ = lean_st_mk_ref(v___x_521_);
v___x_545_ = lean_st_ref_get(v___x_522_);
v___x_546_ = lean_st_ref_get(v___x_544_);
v_env_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc_ref(v_env_547_);
lean_dec(v___x_546_);
v___x_548_ = l_Lean_diagnostics;
v___x_549_ = l_Lean_Option_get___at___00main_spec__8(v___x_523_, v___x_548_);
v___x_616_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_547_);
lean_dec_ref(v_env_547_);
if (v___x_549_ == 0)
{
if (v___x_616_ == 0)
{
v___y_596_ = v___x_526_;
goto v___jp_595_;
}
else
{
v___y_596_ = v___x_549_;
goto v___jp_595_;
}
}
else
{
v___y_596_ = v___x_616_;
goto v___jp_595_;
}
v___jp_539_:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = lean_mk_io_user_error(v_a_540_);
v___x_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
return v___x_542_;
}
v___jp_550_:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_565_ = l_Lean_maxRecDepth;
v___x_566_ = l_Lean_Option_get___at___00main_spec__9(v___x_523_, v___x_565_);
v___x_567_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_567_, 0, v_fileName_551_);
lean_ctor_set(v___x_567_, 1, v_fileMap_552_);
lean_ctor_set(v___x_567_, 2, v___x_523_);
lean_ctor_set(v___x_567_, 3, v_currRecDepth_553_);
lean_ctor_set(v___x_567_, 4, v___x_566_);
lean_ctor_set(v___x_567_, 5, v_ref_554_);
lean_ctor_set(v___x_567_, 6, v_currNamespace_555_);
lean_ctor_set(v___x_567_, 7, v_openDecls_556_);
lean_ctor_set(v___x_567_, 8, v_initHeartbeats_557_);
lean_ctor_set(v___x_567_, 9, v_maxHeartbeats_558_);
lean_ctor_set(v___x_567_, 10, v_quotContext_559_);
lean_ctor_set(v___x_567_, 11, v_currMacroScope_560_);
lean_ctor_set(v___x_567_, 12, v_cancelTk_x3f_561_);
lean_ctor_set(v___x_567_, 13, v_inheritedTraceOptions_563_);
lean_ctor_set_uint8(v___x_567_, sizeof(void*)*14, v___x_549_);
lean_ctor_set_uint8(v___x_567_, sizeof(void*)*14 + 1, v_suppressElabErrors_562_);
v___x_568_ = l_Lean_Compiler_LCNF_emitC(v_name_524_, v___x_567_, v___y_564_);
lean_dec(v___y_564_);
lean_dec_ref_known(v___x_567_, 14);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_a_569_);
lean_dec_ref_known(v___x_568_, 1);
v___x_570_ = lean_st_ref_get(v___x_544_);
lean_dec(v___x_544_);
lean_dec(v___x_570_);
v___x_571_ = lean_string_to_utf8(v_a_569_);
lean_dec(v_a_569_);
v___x_572_ = lean_io_prim_handle_write(v_a_525_, v___x_571_);
lean_dec_ref(v___x_571_);
return v___x_572_;
}
else
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_594_; 
lean_dec(v___x_544_);
v_a_573_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_594_ == 0)
{
v___x_575_ = v___x_568_;
v_isShared_576_ = v_isSharedCheck_594_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_568_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_594_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
if (lean_obj_tag(v_a_573_) == 0)
{
lean_object* v_msg_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_581_; 
v_msg_577_ = lean_ctor_get(v_a_573_, 1);
lean_inc_ref(v_msg_577_);
lean_dec_ref_known(v_a_573_, 2);
v___x_578_ = l_Lean_MessageData_toString(v_msg_577_);
v___x_579_ = lean_mk_io_user_error(v___x_578_);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_579_);
v___x_581_ = v___x_575_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_579_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
else
{
lean_object* v_id_583_; lean_object* v___x_584_; 
lean_del_object(v___x_575_);
v_id_583_ = lean_ctor_get(v_a_573_, 0);
lean_inc(v_id_583_);
lean_dec_ref_known(v_a_573_, 2);
v___x_584_ = l_Lean_InternalExceptionId_getName(v_id_583_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
lean_dec(v_id_583_);
v_a_585_ = lean_ctor_get(v___x_584_, 0);
lean_inc(v_a_585_);
lean_dec_ref_known(v___x_584_, 1);
v___x_586_ = ((lean_object*)(l_main___lam__1___closed__0));
v___x_587_ = l_Lean_Name_toString(v_a_585_, v___x_526_);
v___x_588_ = lean_string_append(v___x_586_, v___x_587_);
lean_dec_ref(v___x_587_);
v_a_540_ = v___x_588_;
goto v___jp_539_;
}
else
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
lean_dec_ref_known(v___x_584_, 1);
v___x_589_ = ((lean_object*)(l_main___lam__1___closed__1));
v___x_590_ = l_Nat_reprFast(v_id_583_);
v___x_591_ = lean_string_append(v___x_589_, v___x_590_);
lean_dec_ref(v___x_590_);
v___x_592_ = ((lean_object*)(l_main___lam__1___closed__2));
v___x_593_ = lean_string_append(v___x_591_, v___x_592_);
v_a_540_ = v___x_593_;
goto v___jp_539_;
}
}
}
}
}
v___jp_595_:
{
if (v___y_596_ == 0)
{
lean_object* v___x_597_; lean_object* v_env_598_; lean_object* v_nextMacroScope_599_; lean_object* v_ngen_600_; lean_object* v_auxDeclNGen_601_; lean_object* v_traceState_602_; lean_object* v_messages_603_; lean_object* v_infoState_604_; lean_object* v_snapshotTasks_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_614_; 
v___x_597_ = lean_st_ref_take(v___x_544_);
v_env_598_ = lean_ctor_get(v___x_597_, 0);
v_nextMacroScope_599_ = lean_ctor_get(v___x_597_, 1);
v_ngen_600_ = lean_ctor_get(v___x_597_, 2);
v_auxDeclNGen_601_ = lean_ctor_get(v___x_597_, 3);
v_traceState_602_ = lean_ctor_get(v___x_597_, 4);
v_messages_603_ = lean_ctor_get(v___x_597_, 6);
v_infoState_604_ = lean_ctor_get(v___x_597_, 7);
v_snapshotTasks_605_ = lean_ctor_get(v___x_597_, 8);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_614_ == 0)
{
lean_object* v_unused_615_; 
v_unused_615_ = lean_ctor_get(v___x_597_, 5);
lean_dec(v_unused_615_);
v___x_607_ = v___x_597_;
v_isShared_608_ = v_isSharedCheck_614_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_snapshotTasks_605_);
lean_inc(v_infoState_604_);
lean_inc(v_messages_603_);
lean_inc(v_traceState_602_);
lean_inc(v_auxDeclNGen_601_);
lean_inc(v_ngen_600_);
lean_inc(v_nextMacroScope_599_);
lean_inc(v_env_598_);
lean_dec(v___x_597_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_614_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_609_; lean_object* v___x_611_; 
v___x_609_ = l_Lean_Kernel_enableDiag(v_env_598_, v___x_549_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 5, v___x_527_);
lean_ctor_set(v___x_607_, 0, v___x_609_);
v___x_611_ = v___x_607_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_nextMacroScope_599_);
lean_ctor_set(v_reuseFailAlloc_613_, 2, v_ngen_600_);
lean_ctor_set(v_reuseFailAlloc_613_, 3, v_auxDeclNGen_601_);
lean_ctor_set(v_reuseFailAlloc_613_, 4, v_traceState_602_);
lean_ctor_set(v_reuseFailAlloc_613_, 5, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_613_, 6, v_messages_603_);
lean_ctor_set(v_reuseFailAlloc_613_, 7, v_infoState_604_);
lean_ctor_set(v_reuseFailAlloc_613_, 8, v_snapshotTasks_605_);
v___x_611_ = v_reuseFailAlloc_613_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_612_; 
v___x_612_ = lean_st_ref_put(v___x_544_, v___x_611_);
lean_inc(v___x_544_);
lean_inc(v___x_532_);
v_fileName_551_ = v_head_528_;
v_fileMap_552_ = v___x_529_;
v_currRecDepth_553_ = v___x_530_;
v_ref_554_ = v___x_531_;
v_currNamespace_555_ = v___x_532_;
v_openDecls_556_ = v___x_533_;
v_initHeartbeats_557_ = v___x_543_;
v_maxHeartbeats_558_ = v___x_534_;
v_quotContext_559_ = v___x_532_;
v_currMacroScope_560_ = v___x_535_;
v_cancelTk_x3f_561_ = v___x_536_;
v_suppressElabErrors_562_ = v___x_537_;
v_inheritedTraceOptions_563_ = v___x_545_;
v___y_564_ = v___x_544_;
goto v___jp_550_;
}
}
}
else
{
lean_dec_ref(v___x_527_);
lean_inc(v___x_544_);
lean_inc(v___x_532_);
v_fileName_551_ = v_head_528_;
v_fileMap_552_ = v___x_529_;
v_currRecDepth_553_ = v___x_530_;
v_ref_554_ = v___x_531_;
v_currNamespace_555_ = v___x_532_;
v_openDecls_556_ = v___x_533_;
v_initHeartbeats_557_ = v___x_543_;
v_maxHeartbeats_558_ = v___x_534_;
v_quotContext_559_ = v___x_532_;
v_currMacroScope_560_ = v___x_535_;
v_cancelTk_x3f_561_ = v___x_536_;
v_suppressElabErrors_562_ = v___x_537_;
v_inheritedTraceOptions_563_ = v___x_545_;
v___y_564_ = v___x_544_;
goto v___jp_550_;
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__1___boxed(lean_object** _args){
lean_object* v___x_617_ = _args[0];
lean_object* v___x_618_ = _args[1];
lean_object* v___x_619_ = _args[2];
lean_object* v_name_620_ = _args[3];
lean_object* v_a_621_ = _args[4];
lean_object* v___x_622_ = _args[5];
lean_object* v___x_623_ = _args[6];
lean_object* v_head_624_ = _args[7];
lean_object* v___x_625_ = _args[8];
lean_object* v___x_626_ = _args[9];
lean_object* v___x_627_ = _args[10];
lean_object* v___x_628_ = _args[11];
lean_object* v___x_629_ = _args[12];
lean_object* v___x_630_ = _args[13];
lean_object* v___x_631_ = _args[14];
lean_object* v___x_632_ = _args[15];
lean_object* v___x_633_ = _args[16];
lean_object* v___y_634_ = _args[17];
_start:
{
uint8_t v___x_35225__boxed_635_; uint8_t v___x_35236__boxed_636_; lean_object* v_res_637_; 
v___x_35225__boxed_635_ = lean_unbox(v___x_622_);
v___x_35236__boxed_636_ = lean_unbox(v___x_633_);
v_res_637_ = l_main___lam__1(v___x_617_, v___x_618_, v___x_619_, v_name_620_, v_a_621_, v___x_35225__boxed_635_, v___x_623_, v_head_624_, v___x_625_, v___x_626_, v___x_627_, v___x_628_, v___x_629_, v___x_630_, v___x_631_, v___x_632_, v___x_35236__boxed_636_);
lean_dec(v_a_621_);
lean_dec(v___x_618_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(lean_object* v_s_638_){
_start:
{
lean_object* v___x_640_; lean_object* v_putStr_641_; lean_object* v___x_642_; 
v___x_640_ = lean_get_stderr();
v_putStr_641_ = lean_ctor_get(v___x_640_, 4);
lean_inc_ref(v_putStr_641_);
lean_dec_ref(v___x_640_);
v___x_642_ = lean_apply_2(v_putStr_641_, v_s_638_, lean_box(0));
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8___boxed(lean_object* v_s_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v_s_643_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6(lean_object* v_s_646_){
_start:
{
uint32_t v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_648_ = 10;
v___x_649_ = lean_string_push(v_s_646_, v___x_648_);
v___x_650_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v___x_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6___boxed(lean_object* v_s_651_, lean_object* v_a_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_IO_eprintln___at___00main_spec__6(v_s_651_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(lean_object* v_o_657_, lean_object* v_k_658_, lean_object* v_v_659_){
_start:
{
lean_object* v_map_660_; uint8_t v_hasTrace_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_675_; 
v_map_660_ = lean_ctor_get(v_o_657_, 0);
v_hasTrace_661_ = lean_ctor_get_uint8(v_o_657_, sizeof(void*)*1);
v_isSharedCheck_675_ = !lean_is_exclusive(v_o_657_);
if (v_isSharedCheck_675_ == 0)
{
v___x_663_ = v_o_657_;
v_isShared_664_ = v_isSharedCheck_675_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_map_660_);
lean_dec(v_o_657_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_675_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_665_, 0, v_v_659_);
lean_inc(v_k_658_);
v___x_666_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_658_, v___x_665_, v_map_660_);
if (v_hasTrace_661_ == 0)
{
lean_object* v___x_667_; uint8_t v___x_668_; lean_object* v___x_670_; 
v___x_667_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_668_ = l_Lean_Name_isPrefixOf(v___x_667_, v_k_658_);
lean_dec(v_k_658_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 0, v___x_666_);
v___x_670_ = v___x_663_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_666_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
lean_ctor_set_uint8(v___x_670_, sizeof(void*)*1, v___x_668_);
return v___x_670_;
}
}
else
{
lean_object* v___x_673_; 
lean_dec(v_k_658_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 0, v___x_666_);
v___x_673_ = v___x_663_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_666_);
lean_ctor_set_uint8(v_reuseFailAlloc_674_, sizeof(void*)*1, v_hasTrace_661_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00main_spec__3(lean_object* v_opts_676_, lean_object* v_opt_677_, lean_object* v_val_678_){
_start:
{
lean_object* v_name_679_; lean_object* v___x_680_; 
v_name_679_ = lean_ctor_get(v_opt_677_, 0);
lean_inc(v_name_679_);
lean_dec_ref(v_opt_677_);
v___x_680_ = l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(v_opts_676_, v_name_679_, v_val_678_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(lean_object* v___y_682_, lean_object* v_as_683_, size_t v_i_684_, size_t v_stop_685_, lean_object* v_b_686_){
_start:
{
lean_object* v___y_688_; uint8_t v___x_692_; 
v___x_692_ = lean_usize_dec_eq(v_i_684_, v_stop_685_);
if (v___x_692_ == 0)
{
lean_object* v_fst_693_; lean_object* v_snd_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___y_698_; 
v_fst_693_ = lean_ctor_get(v_b_686_, 0);
v_snd_694_ = lean_ctor_get(v_b_686_, 1);
v___x_695_ = lean_array_uget_borrowed(v_as_683_, v_i_684_);
v___x_696_ = l_Lean_IR_Decl_name(v___x_695_);
if (lean_obj_tag(v___x_696_) == 1)
{
lean_object* v_pre_711_; lean_object* v_str_712_; lean_object* v___x_713_; uint8_t v___x_714_; 
v_pre_711_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_pre_711_);
v_str_712_ = lean_ctor_get(v___x_696_, 1);
lean_inc_ref(v_str_712_);
v___x_713_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___closed__0));
v___x_714_ = lean_string_dec_eq(v_str_712_, v___x_713_);
lean_dec_ref(v_str_712_);
if (v___x_714_ == 0)
{
lean_dec(v_pre_711_);
lean_inc_ref(v___x_696_);
v___y_698_ = v___x_696_;
goto v___jp_697_;
}
else
{
v___y_698_ = v_pre_711_;
goto v___jp_697_;
}
}
else
{
lean_inc(v___x_696_);
v___y_698_ = v___x_696_;
goto v___jp_697_;
}
v___jp_697_:
{
uint8_t v___x_699_; 
lean_inc_ref(v___y_682_);
v___x_699_ = l_Lean_isExtern(v___y_682_, v___y_698_);
if (v___x_699_ == 0)
{
lean_dec(v___x_696_);
v___y_688_ = v_b_686_;
goto v___jp_687_;
}
else
{
lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_708_; 
lean_inc(v_snd_694_);
lean_inc(v_fst_693_);
v_isSharedCheck_708_ = !lean_is_exclusive(v_b_686_);
if (v_isSharedCheck_708_ == 0)
{
lean_object* v_unused_709_; lean_object* v_unused_710_; 
v_unused_709_ = lean_ctor_get(v_b_686_, 1);
lean_dec(v_unused_709_);
v_unused_710_ = lean_ctor_get(v_b_686_, 0);
lean_dec(v_unused_710_);
v___x_701_ = v_b_686_;
v_isShared_702_ = v_isSharedCheck_708_;
goto v_resetjp_700_;
}
else
{
lean_dec(v_b_686_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_708_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_706_; 
lean_inc_n(v___x_695_, 2);
v___x_703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_695_);
lean_ctor_set(v___x_703_, 1, v_fst_693_);
v___x_704_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(v_snd_694_, v___x_696_, v___x_695_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 1, v___x_704_);
lean_ctor_set(v___x_701_, 0, v___x_703_);
v___x_706_ = v___x_701_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_703_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v___x_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
v___y_688_ = v___x_706_;
goto v___jp_687_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_682_);
return v_b_686_;
}
v___jp_687_:
{
size_t v___x_689_; size_t v___x_690_; 
v___x_689_ = ((size_t)1ULL);
v___x_690_ = lean_usize_add(v_i_684_, v___x_689_);
v_i_684_ = v___x_690_;
v_b_686_ = v___y_688_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___boxed(lean_object* v___y_715_, lean_object* v_as_716_, lean_object* v_i_717_, lean_object* v_stop_718_, lean_object* v_b_719_){
_start:
{
size_t v_i_boxed_720_; size_t v_stop_boxed_721_; lean_object* v_res_722_; 
v_i_boxed_720_ = lean_unbox_usize(v_i_717_);
lean_dec(v_i_717_);
v_stop_boxed_721_ = lean_unbox_usize(v_stop_718_);
lean_dec(v_stop_718_);
v_res_722_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_715_, v_as_716_, v_i_boxed_720_, v_stop_boxed_721_, v_b_719_);
lean_dec_ref(v_as_716_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg(lean_object* v_as_x27_724_, lean_object* v_b_725_){
_start:
{
if (lean_obj_tag(v_as_x27_724_) == 0)
{
lean_object* v___x_727_; 
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v_b_725_);
return v___x_727_;
}
else
{
lean_object* v_head_728_; lean_object* v_tail_729_; lean_object* v_fst_730_; lean_object* v_snd_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_756_; 
v_head_728_ = lean_ctor_get(v_as_x27_724_, 0);
v_tail_729_ = lean_ctor_get(v_as_x27_724_, 1);
v_fst_730_ = lean_ctor_get(v_b_725_, 0);
v_snd_731_ = lean_ctor_get(v_b_725_, 1);
v_isSharedCheck_756_ = !lean_is_exclusive(v_b_725_);
if (v_isSharedCheck_756_ == 0)
{
v___x_733_ = v_b_725_;
v_isShared_734_ = v_isSharedCheck_756_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_snd_731_);
lean_inc(v_fst_730_);
lean_dec(v_b_725_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_756_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_735_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0));
v___x_736_ = lean_string_dec_eq(v_head_728_, v___x_735_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; 
lean_inc(v_head_728_);
v___x_737_ = l___private_LeanIR_0__setConfigOption(v_snd_731_, v_head_728_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v___x_740_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_a_738_);
lean_dec_ref_known(v___x_737_, 1);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 1, v_a_738_);
v___x_740_ = v___x_733_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_fst_730_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_a_738_);
v___x_740_ = v_reuseFailAlloc_742_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
v_as_x27_724_ = v_tail_729_;
v_b_725_ = v___x_740_;
goto _start;
}
}
else
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
lean_del_object(v___x_733_);
lean_dec(v_fst_730_);
v_a_743_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v___x_737_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_737_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_743_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
else
{
lean_object* v___x_751_; lean_object* v___x_753_; 
lean_dec(v_fst_730_);
v___x_751_ = lean_box(v___x_736_);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 0, v___x_751_);
v___x_753_ = v___x_733_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v_snd_731_);
v___x_753_ = v_reuseFailAlloc_755_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
v_as_x27_724_ = v_tail_729_;
v_b_725_ = v___x_753_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg___boxed(lean_object* v_as_x27_757_, lean_object* v_b_758_, lean_object* v___y_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_757_, v_b_758_);
lean_dec(v_as_x27_757_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(lean_object* v_as_761_, size_t v_i_762_, size_t v_stop_763_, lean_object* v_b_764_){
_start:
{
uint8_t v___x_765_; 
v___x_765_ = lean_usize_dec_eq(v_i_762_, v_stop_763_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; lean_object* v_toEnvExtension_767_; lean_object* v_asyncMode_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; size_t v___x_772_; size_t v___x_773_; 
v___x_766_ = l_Lean_Compiler_LCNF_impureSigExt;
v_toEnvExtension_767_ = lean_ctor_get(v___x_766_, 0);
v_asyncMode_768_ = lean_ctor_get(v_toEnvExtension_767_, 2);
v___x_769_ = lean_box(0);
v___x_770_ = lean_array_uget_borrowed(v_as_761_, v_i_762_);
lean_inc(v___x_770_);
v___x_771_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_766_, v_b_764_, v___x_770_, v_asyncMode_768_, v___x_769_);
v___x_772_ = ((size_t)1ULL);
v___x_773_ = lean_usize_add(v_i_762_, v___x_772_);
v_i_762_ = v___x_773_;
v_b_764_ = v___x_771_;
goto _start;
}
else
{
return v_b_764_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18___boxed(lean_object* v_as_775_, lean_object* v_i_776_, lean_object* v_stop_777_, lean_object* v_b_778_){
_start:
{
size_t v_i_boxed_779_; size_t v_stop_boxed_780_; lean_object* v_res_781_; 
v_i_boxed_779_ = lean_unbox_usize(v_i_776_);
lean_dec(v_i_776_);
v_stop_boxed_780_ = lean_unbox_usize(v_stop_777_);
lean_dec(v_stop_777_);
v_res_781_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_as_775_, v_i_boxed_779_, v_stop_boxed_780_, v_b_778_);
lean_dec_ref(v_as_775_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(lean_object* v_as_785_, size_t v_sz_786_, size_t v_i_787_, lean_object* v_b_788_, lean_object* v___y_789_){
_start:
{
uint8_t v___x_791_; 
v___x_791_ = lean_usize_dec_lt(v_i_787_, v_sz_786_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; 
v___x_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_792_, 0, v_b_788_);
return v___x_792_;
}
else
{
uint8_t v___x_793_; lean_object* v_a_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
lean_dec_ref(v_b_788_);
v___x_793_ = 0;
v_a_794_ = lean_array_uget_borrowed(v_as_785_, v_i_787_);
lean_inc(v_a_794_);
v___x_795_ = l_Lean_Message_toString(v_a_794_, v___x_793_);
v___x_796_ = l_IO_eprintln___at___00main_spec__6(v___x_795_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v___x_797_; size_t v___x_798_; size_t v___x_799_; 
lean_dec_ref_known(v___x_796_, 1);
v___x_797_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_798_ = ((size_t)1ULL);
v___x_799_ = lean_usize_add(v_i_787_, v___x_798_);
v_i_787_ = v___x_799_;
v_b_788_ = v___x_797_;
goto _start;
}
else
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_813_; 
v_a_801_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_813_ == 0)
{
v___x_803_ = v___x_796_;
v_isShared_804_ = v_isSharedCheck_813_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v___x_796_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_813_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v_ref_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_811_; 
v_ref_805_ = lean_ctor_get(v___y_789_, 5);
v___x_806_ = lean_io_error_to_string(v_a_801_);
v___x_807_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
v___x_808_ = l_Lean_MessageData_ofFormat(v___x_807_);
lean_inc(v_ref_805_);
v___x_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_809_, 0, v_ref_805_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 0, v___x_809_);
v___x_811_ = v___x_803_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_809_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___boxed(lean_object* v_as_814_, lean_object* v_sz_815_, lean_object* v_i_816_, lean_object* v_b_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
size_t v_sz_boxed_820_; size_t v_i_boxed_821_; lean_object* v_res_822_; 
v_sz_boxed_820_ = lean_unbox_usize(v_sz_815_);
lean_dec(v_sz_815_);
v_i_boxed_821_ = lean_unbox_usize(v_i_816_);
lean_dec(v_i_816_);
v_res_822_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_814_, v_sz_boxed_820_, v_i_boxed_821_, v_b_817_, v___y_818_);
lean_dec_ref(v___y_818_);
lean_dec_ref(v_as_814_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(lean_object* v_as_823_, size_t v_sz_824_, size_t v_i_825_, lean_object* v_b_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
uint8_t v___x_830_; 
v___x_830_ = lean_usize_dec_lt(v_i_825_, v_sz_824_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; 
v___x_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_831_, 0, v_b_826_);
return v___x_831_;
}
else
{
uint8_t v___x_832_; lean_object* v_a_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
lean_dec_ref(v_b_826_);
v___x_832_ = 0;
v_a_833_ = lean_array_uget_borrowed(v_as_823_, v_i_825_);
lean_inc(v_a_833_);
v___x_834_ = l_Lean_Message_toString(v_a_833_, v___x_832_);
v___x_835_ = l_IO_eprintln___at___00main_spec__6(v___x_834_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v___x_836_; size_t v___x_837_; size_t v___x_838_; lean_object* v___x_839_; 
lean_dec_ref_known(v___x_835_, 1);
v___x_836_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_837_ = ((size_t)1ULL);
v___x_838_ = lean_usize_add(v_i_825_, v___x_837_);
v___x_839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_823_, v_sz_824_, v___x_838_, v___x_836_, v___y_827_);
return v___x_839_;
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_852_; 
v_a_840_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_852_ == 0)
{
v___x_842_ = v___x_835_;
v_isShared_843_ = v_isSharedCheck_852_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_835_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_852_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v_ref_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_850_; 
v_ref_844_ = lean_ctor_get(v___y_827_, 5);
v___x_845_ = lean_io_error_to_string(v_a_840_);
v___x_846_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
v___x_847_ = l_Lean_MessageData_ofFormat(v___x_846_);
lean_inc(v_ref_844_);
v___x_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_848_, 0, v_ref_844_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_848_);
v___x_850_ = v___x_842_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_848_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27___boxed(lean_object* v_as_853_, lean_object* v_sz_854_, lean_object* v_i_855_, lean_object* v_b_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
size_t v_sz_boxed_860_; size_t v_i_boxed_861_; lean_object* v_res_862_; 
v_sz_boxed_860_ = lean_unbox_usize(v_sz_854_);
lean_dec(v_sz_854_);
v_i_boxed_861_ = lean_unbox_usize(v_i_855_);
lean_dec(v_i_855_);
v_res_862_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(v_as_853_, v_sz_boxed_860_, v_i_boxed_861_, v_b_856_, v___y_857_, v___y_858_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec_ref(v_as_853_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(lean_object* v_as_866_, size_t v_sz_867_, size_t v_i_868_, lean_object* v_b_869_, lean_object* v___y_870_){
_start:
{
uint8_t v___x_872_; 
v___x_872_ = lean_usize_dec_lt(v_i_868_, v_sz_867_);
if (v___x_872_ == 0)
{
lean_object* v___x_873_; 
v___x_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_873_, 0, v_b_869_);
return v___x_873_;
}
else
{
uint8_t v___x_874_; lean_object* v_a_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
lean_dec_ref(v_b_869_);
v___x_874_ = 0;
v_a_875_ = lean_array_uget_borrowed(v_as_866_, v_i_868_);
lean_inc(v_a_875_);
v___x_876_ = l_Lean_Message_toString(v_a_875_, v___x_874_);
v___x_877_ = l_IO_eprintln___at___00main_spec__6(v___x_876_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v___x_878_; size_t v___x_879_; size_t v___x_880_; 
lean_dec_ref_known(v___x_877_, 1);
v___x_878_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_879_ = ((size_t)1ULL);
v___x_880_ = lean_usize_add(v_i_868_, v___x_879_);
v_i_868_ = v___x_880_;
v_b_869_ = v___x_878_;
goto _start;
}
else
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_894_; 
v_a_882_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_894_ == 0)
{
v___x_884_ = v___x_877_;
v_isShared_885_ = v_isSharedCheck_894_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_877_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_894_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v_ref_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_892_; 
v_ref_886_ = lean_ctor_get(v___y_870_, 5);
v___x_887_ = lean_io_error_to_string(v_a_882_);
v___x_888_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
v___x_889_ = l_Lean_MessageData_ofFormat(v___x_888_);
lean_inc(v_ref_886_);
v___x_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_890_, 0, v_ref_886_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 0, v___x_890_);
v___x_892_ = v___x_884_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___boxed(lean_object* v_as_895_, lean_object* v_sz_896_, lean_object* v_i_897_, lean_object* v_b_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
size_t v_sz_boxed_901_; size_t v_i_boxed_902_; lean_object* v_res_903_; 
v_sz_boxed_901_ = lean_unbox_usize(v_sz_896_);
lean_dec(v_sz_896_);
v_i_boxed_902_ = lean_unbox_usize(v_i_897_);
lean_dec(v_i_897_);
v_res_903_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_895_, v_sz_boxed_901_, v_i_boxed_902_, v_b_898_, v___y_899_);
lean_dec_ref(v___y_899_);
lean_dec_ref(v_as_895_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(lean_object* v_as_904_, size_t v_sz_905_, size_t v_i_906_, lean_object* v_b_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
uint8_t v___x_911_; 
v___x_911_ = lean_usize_dec_lt(v_i_906_, v_sz_905_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; 
v___x_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_912_, 0, v_b_907_);
return v___x_912_;
}
else
{
uint8_t v___x_913_; lean_object* v_a_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
lean_dec_ref(v_b_907_);
v___x_913_ = 0;
v_a_914_ = lean_array_uget_borrowed(v_as_904_, v_i_906_);
lean_inc(v_a_914_);
v___x_915_ = l_Lean_Message_toString(v_a_914_, v___x_913_);
v___x_916_ = l_IO_eprintln___at___00main_spec__6(v___x_915_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v___x_917_; size_t v___x_918_; size_t v___x_919_; lean_object* v___x_920_; 
lean_dec_ref_known(v___x_916_, 1);
v___x_917_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_918_ = ((size_t)1ULL);
v___x_919_ = lean_usize_add(v_i_906_, v___x_918_);
v___x_920_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_904_, v_sz_905_, v___x_919_, v___x_917_, v___y_908_);
return v___x_920_;
}
else
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_933_; 
v_a_921_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_933_ == 0)
{
v___x_923_ = v___x_916_;
v_isShared_924_ = v_isSharedCheck_933_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_916_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_933_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v_ref_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_931_; 
v_ref_925_ = lean_ctor_get(v___y_908_, 5);
v___x_926_ = lean_io_error_to_string(v_a_921_);
v___x_927_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
v___x_928_ = l_Lean_MessageData_ofFormat(v___x_927_);
lean_inc(v_ref_925_);
v___x_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_929_, 0, v_ref_925_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v___x_929_);
v___x_931_ = v___x_923_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_929_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38___boxed(lean_object* v_as_934_, lean_object* v_sz_935_, lean_object* v_i_936_, lean_object* v_b_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
size_t v_sz_boxed_941_; size_t v_i_boxed_942_; lean_object* v_res_943_; 
v_sz_boxed_941_ = lean_unbox_usize(v_sz_935_);
lean_dec(v_sz_935_);
v_i_boxed_942_ = lean_unbox_usize(v_i_936_);
lean_dec(v_i_936_);
v_res_943_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(v_as_934_, v_sz_boxed_941_, v_i_boxed_942_, v_b_937_, v___y_938_, v___y_939_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec_ref(v_as_934_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(lean_object* v_init_944_, lean_object* v_n_945_, lean_object* v_b_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
if (lean_obj_tag(v_n_945_) == 0)
{
lean_object* v_cs_950_; lean_object* v___x_951_; lean_object* v___x_952_; size_t v_sz_953_; size_t v___x_954_; lean_object* v___x_955_; 
v_cs_950_ = lean_ctor_get(v_n_945_, 0);
v___x_951_ = lean_box(0);
v___x_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
lean_ctor_set(v___x_952_, 1, v_b_946_);
v_sz_953_ = lean_array_size(v_cs_950_);
v___x_954_ = ((size_t)0ULL);
v___x_955_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(v_init_944_, v_cs_950_, v_sz_953_, v___x_954_, v___x_952_, v___y_947_, v___y_948_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_970_; 
v_a_956_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_970_ == 0)
{
v___x_958_ = v___x_955_;
v_isShared_959_ = v_isSharedCheck_970_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_955_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_970_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v_fst_960_; 
v_fst_960_ = lean_ctor_get(v_a_956_, 0);
if (lean_obj_tag(v_fst_960_) == 0)
{
lean_object* v_snd_961_; lean_object* v___x_962_; lean_object* v___x_964_; 
v_snd_961_ = lean_ctor_get(v_a_956_, 1);
lean_inc(v_snd_961_);
lean_dec(v_a_956_);
v___x_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_962_, 0, v_snd_961_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 0, v___x_962_);
v___x_964_ = v___x_958_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_962_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
else
{
lean_object* v_val_966_; lean_object* v___x_968_; 
lean_inc_ref(v_fst_960_);
lean_dec(v_a_956_);
v_val_966_ = lean_ctor_get(v_fst_960_, 0);
lean_inc(v_val_966_);
lean_dec_ref_known(v_fst_960_, 1);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 0, v_val_966_);
v___x_968_ = v___x_958_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_val_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
else
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_978_; 
v_a_971_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_978_ == 0)
{
v___x_973_ = v___x_955_;
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_955_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_976_; 
if (v_isShared_974_ == 0)
{
v___x_976_ = v___x_973_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_a_971_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
else
{
lean_object* v_vs_979_; lean_object* v___x_980_; lean_object* v___x_981_; size_t v_sz_982_; size_t v___x_983_; lean_object* v___x_984_; 
v_vs_979_ = lean_ctor_get(v_n_945_, 0);
v___x_980_ = lean_box(0);
v___x_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
lean_ctor_set(v___x_981_, 1, v_b_946_);
v_sz_982_ = lean_array_size(v_vs_979_);
v___x_983_ = ((size_t)0ULL);
v___x_984_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(v_vs_979_, v_sz_982_, v___x_983_, v___x_981_, v___y_947_, v___y_948_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_999_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_999_ == 0)
{
v___x_987_ = v___x_984_;
v_isShared_988_ = v_isSharedCheck_999_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_984_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_999_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v_fst_989_; 
v_fst_989_ = lean_ctor_get(v_a_985_, 0);
if (lean_obj_tag(v_fst_989_) == 0)
{
lean_object* v_snd_990_; lean_object* v___x_991_; lean_object* v___x_993_; 
v_snd_990_ = lean_ctor_get(v_a_985_, 1);
lean_inc(v_snd_990_);
lean_dec(v_a_985_);
v___x_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_991_, 0, v_snd_990_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v___x_991_);
v___x_993_ = v___x_987_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_991_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
else
{
lean_object* v_val_995_; lean_object* v___x_997_; 
lean_inc_ref(v_fst_989_);
lean_dec(v_a_985_);
v_val_995_ = lean_ctor_get(v_fst_989_, 0);
lean_inc(v_val_995_);
lean_dec_ref_known(v_fst_989_, 1);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v_val_995_);
v___x_997_ = v___x_987_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_val_995_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
v_a_1000_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_984_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_984_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(lean_object* v_init_1008_, lean_object* v_as_1009_, size_t v_sz_1010_, size_t v_i_1011_, lean_object* v_b_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
uint8_t v___x_1016_; 
v___x_1016_ = lean_usize_dec_lt(v_i_1011_, v_sz_1010_);
if (v___x_1016_ == 0)
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1017_, 0, v_b_1012_);
return v___x_1017_;
}
else
{
lean_object* v_snd_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1052_; 
v_snd_1018_ = lean_ctor_get(v_b_1012_, 1);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_b_1012_);
if (v_isSharedCheck_1052_ == 0)
{
lean_object* v_unused_1053_; 
v_unused_1053_ = lean_ctor_get(v_b_1012_, 0);
lean_dec(v_unused_1053_);
v___x_1020_ = v_b_1012_;
v_isShared_1021_ = v_isSharedCheck_1052_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_snd_1018_);
lean_dec(v_b_1012_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1052_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v_a_1022_; lean_object* v___x_1023_; 
v_a_1022_ = lean_array_uget_borrowed(v_as_1009_, v_i_1011_);
lean_inc(v_snd_1018_);
v___x_1023_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_1008_, v_a_1022_, v_snd_1018_, v___y_1013_, v___y_1014_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1043_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1026_ = v___x_1023_;
v_isShared_1027_ = v_isSharedCheck_1043_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1023_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1043_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
if (lean_obj_tag(v_a_1024_) == 0)
{
lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1028_, 0, v_a_1024_);
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 0, v___x_1028_);
v___x_1030_ = v___x_1020_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1028_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v_snd_1018_);
v___x_1030_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_object* v___x_1032_; 
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v___x_1030_);
v___x_1032_ = v___x_1026_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1036_; lean_object* v___x_1038_; 
lean_del_object(v___x_1026_);
lean_dec(v_snd_1018_);
v_a_1035_ = lean_ctor_get(v_a_1024_, 0);
lean_inc(v_a_1035_);
lean_dec_ref_known(v_a_1024_, 1);
v___x_1036_ = lean_box(0);
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 1, v_a_1035_);
lean_ctor_set(v___x_1020_, 0, v___x_1036_);
v___x_1038_ = v___x_1020_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_a_1035_);
v___x_1038_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
size_t v___x_1039_; size_t v___x_1040_; 
v___x_1039_ = ((size_t)1ULL);
v___x_1040_ = lean_usize_add(v_i_1011_, v___x_1039_);
v_i_1011_ = v___x_1040_;
v_b_1012_ = v___x_1038_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
lean_del_object(v___x_1020_);
lean_dec(v_snd_1018_);
v_a_1044_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___x_1023_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1023_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37___boxed(lean_object* v_init_1054_, lean_object* v_as_1055_, lean_object* v_sz_1056_, lean_object* v_i_1057_, lean_object* v_b_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
size_t v_sz_boxed_1062_; size_t v_i_boxed_1063_; lean_object* v_res_1064_; 
v_sz_boxed_1062_ = lean_unbox_usize(v_sz_1056_);
lean_dec(v_sz_1056_);
v_i_boxed_1063_ = lean_unbox_usize(v_i_1057_);
lean_dec(v_i_1057_);
v_res_1064_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(v_init_1054_, v_as_1055_, v_sz_boxed_1062_, v_i_boxed_1063_, v_b_1058_, v___y_1059_, v___y_1060_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec_ref(v_as_1055_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26___boxed(lean_object* v_init_1065_, lean_object* v_n_1066_, lean_object* v_b_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_1065_, v_n_1066_, v_b_1067_, v___y_1068_, v___y_1069_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec_ref(v_n_1066_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__12(lean_object* v_t_1072_, lean_object* v_init_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v_root_1077_; lean_object* v_tail_1078_; lean_object* v___x_1079_; 
v_root_1077_ = lean_ctor_get(v_t_1072_, 0);
v_tail_1078_ = lean_ctor_get(v_t_1072_, 1);
v___x_1079_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_1073_, v_root_1077_, v_init_1073_, v___y_1074_, v___y_1075_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1116_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1082_ = v___x_1079_;
v_isShared_1083_ = v_isSharedCheck_1116_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1079_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1116_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
if (lean_obj_tag(v_a_1080_) == 0)
{
lean_object* v_a_1084_; lean_object* v___x_1086_; 
v_a_1084_ = lean_ctor_get(v_a_1080_, 0);
lean_inc(v_a_1084_);
lean_dec_ref_known(v_a_1080_, 1);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v_a_1084_);
v___x_1086_ = v___x_1082_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1084_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; size_t v_sz_1091_; size_t v___x_1092_; lean_object* v___x_1093_; 
lean_del_object(v___x_1082_);
v_a_1088_ = lean_ctor_get(v_a_1080_, 0);
lean_inc(v_a_1088_);
lean_dec_ref_known(v_a_1080_, 1);
v___x_1089_ = lean_box(0);
v___x_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
lean_ctor_set(v___x_1090_, 1, v_a_1088_);
v_sz_1091_ = lean_array_size(v_tail_1078_);
v___x_1092_ = ((size_t)0ULL);
v___x_1093_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(v_tail_1078_, v_sz_1091_, v___x_1092_, v___x_1090_, v___y_1074_, v___y_1075_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1107_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1096_ = v___x_1093_;
v_isShared_1097_ = v_isSharedCheck_1107_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_1093_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1107_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v_fst_1098_; 
v_fst_1098_ = lean_ctor_get(v_a_1094_, 0);
if (lean_obj_tag(v_fst_1098_) == 0)
{
lean_object* v_snd_1099_; lean_object* v___x_1101_; 
v_snd_1099_ = lean_ctor_get(v_a_1094_, 1);
lean_inc(v_snd_1099_);
lean_dec(v_a_1094_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 0, v_snd_1099_);
v___x_1101_ = v___x_1096_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_snd_1099_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
else
{
lean_object* v_val_1103_; lean_object* v___x_1105_; 
lean_inc_ref(v_fst_1098_);
lean_dec(v_a_1094_);
v_val_1103_ = lean_ctor_get(v_fst_1098_, 0);
lean_inc(v_val_1103_);
lean_dec_ref_known(v_fst_1098_, 1);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 0, v_val_1103_);
v___x_1105_ = v___x_1096_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_val_1103_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
v_a_1108_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1093_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1093_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
}
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
v_a_1117_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1079_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1079_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__12___boxed(lean_object* v_t_1125_, lean_object* v_init_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Lean_PersistentArray_forIn___at___00main_spec__12(v_t_1125_, v_init_1126_, v___y_1127_, v___y_1128_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec_ref(v_t_1125_);
return v_res_1130_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0(uint8_t v_suppressElabErrors_1138_, uint8_t v___x_1139_, lean_object* v___x_1140_, lean_object* v_x_1141_){
_start:
{
if (lean_obj_tag(v_x_1141_) == 1)
{
lean_object* v_pre_1142_; 
v_pre_1142_ = lean_ctor_get(v_x_1141_, 0);
switch(lean_obj_tag(v_pre_1142_))
{
case 1:
{
lean_object* v_pre_1143_; 
v_pre_1143_ = lean_ctor_get(v_pre_1142_, 0);
switch(lean_obj_tag(v_pre_1143_))
{
case 0:
{
lean_object* v_str_1144_; lean_object* v_str_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; 
v_str_1144_ = lean_ctor_get(v_x_1141_, 1);
v_str_1145_ = lean_ctor_get(v_pre_1142_, 1);
v___x_1146_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0));
v___x_1147_ = lean_string_dec_eq(v_str_1145_, v___x_1146_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; uint8_t v___x_1149_; 
v___x_1148_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1));
v___x_1149_ = lean_string_dec_eq(v_str_1145_, v___x_1148_);
if (v___x_1149_ == 0)
{
return v___x_1149_;
}
else
{
lean_object* v___x_1150_; uint8_t v___x_1151_; 
v___x_1150_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2));
v___x_1151_ = lean_string_dec_eq(v_str_1144_, v___x_1150_);
if (v___x_1151_ == 0)
{
return v___x_1151_;
}
else
{
return v_suppressElabErrors_1138_;
}
}
}
else
{
lean_object* v___x_1152_; uint8_t v___x_1153_; 
v___x_1152_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3));
v___x_1153_ = lean_string_dec_eq(v_str_1144_, v___x_1152_);
if (v___x_1153_ == 0)
{
return v___x_1153_;
}
else
{
return v_suppressElabErrors_1138_;
}
}
}
case 1:
{
lean_object* v_pre_1154_; 
v_pre_1154_ = lean_ctor_get(v_pre_1143_, 0);
if (lean_obj_tag(v_pre_1154_) == 0)
{
lean_object* v_str_1155_; lean_object* v_str_1156_; lean_object* v_str_1157_; lean_object* v___x_1158_; uint8_t v___x_1159_; 
v_str_1155_ = lean_ctor_get(v_x_1141_, 1);
v_str_1156_ = lean_ctor_get(v_pre_1142_, 1);
v_str_1157_ = lean_ctor_get(v_pre_1143_, 1);
v___x_1158_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4));
v___x_1159_ = lean_string_dec_eq(v_str_1157_, v___x_1158_);
if (v___x_1159_ == 0)
{
return v___x_1159_;
}
else
{
lean_object* v___x_1160_; uint8_t v___x_1161_; 
v___x_1160_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5));
v___x_1161_ = lean_string_dec_eq(v_str_1156_, v___x_1160_);
if (v___x_1161_ == 0)
{
return v___x_1161_;
}
else
{
lean_object* v___x_1162_; uint8_t v___x_1163_; 
v___x_1162_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6));
v___x_1163_ = lean_string_dec_eq(v_str_1155_, v___x_1162_);
if (v___x_1163_ == 0)
{
return v___x_1163_;
}
else
{
return v_suppressElabErrors_1138_;
}
}
}
}
else
{
return v___x_1139_;
}
}
default: 
{
return v___x_1139_;
}
}
}
case 0:
{
lean_object* v_str_1164_; uint8_t v___x_1165_; 
v_str_1164_ = lean_ctor_get(v_x_1141_, 1);
v___x_1165_ = lean_string_dec_eq(v_str_1164_, v___x_1140_);
if (v___x_1165_ == 0)
{
return v___x_1165_;
}
else
{
return v_suppressElabErrors_1138_;
}
}
default: 
{
return v___x_1139_;
}
}
}
else
{
return v___x_1139_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___boxed(lean_object* v_suppressElabErrors_1166_, lean_object* v___x_1167_, lean_object* v___x_1168_, lean_object* v_x_1169_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1170_; uint8_t v___x_36119__boxed_1171_; uint8_t v_res_1172_; lean_object* v_r_1173_; 
v_suppressElabErrors_boxed_1170_ = lean_unbox(v_suppressElabErrors_1166_);
v___x_36119__boxed_1171_ = lean_unbox(v___x_1167_);
v_res_1172_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0(v_suppressElabErrors_boxed_1170_, v___x_36119__boxed_1171_, v___x_1168_, v_x_1169_);
lean_dec(v_x_1169_);
lean_dec_ref(v___x_1168_);
v_r_1173_ = lean_box(v_res_1172_);
return v_r_1173_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0(void){
_start:
{
lean_object* v___x_1174_; double v___x_1175_; 
v___x_1174_ = lean_unsigned_to_nat(0u);
v___x_1175_ = lean_float_of_nat(v___x_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(uint8_t v___x_1177_, lean_object* v_as_1178_, size_t v_sz_1179_, size_t v_i_1180_, lean_object* v_b_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v_a_1186_; uint8_t v___x_1190_; 
v___x_1190_ = lean_usize_dec_lt(v_i_1180_, v_sz_1179_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; 
v___x_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1191_, 0, v_b_1181_);
return v___x_1191_;
}
else
{
lean_object* v_a_1192_; lean_object* v_fst_1193_; lean_object* v_snd_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1270_; 
v_a_1192_ = lean_array_uget(v_as_1178_, v_i_1180_);
v_fst_1193_ = lean_ctor_get(v_a_1192_, 0);
v_snd_1194_ = lean_ctor_get(v_a_1192_, 1);
v_isSharedCheck_1270_ = !lean_is_exclusive(v_a_1192_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1196_ = v_a_1192_;
v_isShared_1197_ = v_isSharedCheck_1270_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_snd_1194_);
lean_inc(v_fst_1193_);
lean_dec(v_a_1192_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1270_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v_fst_1198_; lean_object* v_snd_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1269_; 
v_fst_1198_ = lean_ctor_get(v_fst_1193_, 0);
v_snd_1199_ = lean_ctor_get(v_fst_1193_, 1);
v_isSharedCheck_1269_ = !lean_is_exclusive(v_fst_1193_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1201_ = v_fst_1193_;
v_isShared_1202_ = v_isSharedCheck_1269_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_snd_1199_);
lean_inc(v_fst_1198_);
lean_dec(v_fst_1193_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1269_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; double v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v_fileName_1208_; lean_object* v_fileMap_1209_; uint8_t v_suppressElabErrors_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1217_; 
v___x_1203_ = lean_box(0);
v___x_1204_ = lean_box(0);
v___x_1205_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0);
v___x_1206_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1));
v___x_1207_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1207_, 0, v___x_1203_);
lean_ctor_set(v___x_1207_, 1, v___x_1204_);
lean_ctor_set(v___x_1207_, 2, v___x_1206_);
lean_ctor_set_float(v___x_1207_, sizeof(void*)*3, v___x_1205_);
lean_ctor_set_float(v___x_1207_, sizeof(void*)*3 + 8, v___x_1205_);
lean_ctor_set_uint8(v___x_1207_, sizeof(void*)*3 + 16, v___x_1190_);
v_fileName_1208_ = lean_ctor_get(v___y_1182_, 0);
v_fileMap_1209_ = lean_ctor_get(v___y_1182_, 1);
v_suppressElabErrors_1210_ = lean_ctor_get_uint8(v___y_1182_, sizeof(void*)*14 + 1);
v___x_1211_ = lean_box(0);
v___x_1212_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_1213_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_1214_ = l_Lean_MessageData_nil;
v___x_1215_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1207_);
lean_ctor_set(v___x_1215_, 1, v___x_1214_);
lean_ctor_set(v___x_1215_, 2, v_snd_1194_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set_tag(v___x_1201_, 8);
lean_ctor_set(v___x_1201_, 1, v___x_1215_);
lean_ctor_set(v___x_1201_, 0, v___x_1213_);
v___x_1217_ = v___x_1201_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1213_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v___x_1215_);
v___x_1217_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
uint8_t v___x_1218_; lean_object* v___x_1219_; lean_object* v___y_1221_; lean_object* v___y_1222_; 
v___x_1218_ = 0;
lean_inc_ref(v_fileMap_1209_);
lean_inc_ref(v_fileName_1208_);
v___x_1219_ = l_Lean_Elab_mkMessageCore(v_fileName_1208_, v_fileMap_1209_, v___x_1217_, v___x_1218_, v_fst_1198_, v_snd_1199_);
lean_dec(v_snd_1199_);
lean_dec(v_fst_1198_);
if (v_suppressElabErrors_1210_ == 0)
{
v___y_1221_ = v___y_1182_;
v___y_1222_ = v___y_1183_;
goto v___jp_1220_;
}
else
{
lean_object* v_data_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___f_1266_; uint8_t v___x_1267_; 
v_data_1263_ = lean_ctor_get(v___x_1219_, 4);
lean_inc(v_data_1263_);
v___x_1264_ = lean_box(v_suppressElabErrors_1210_);
v___x_1265_ = lean_box(v___x_1177_);
v___f_1266_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1266_, 0, v___x_1264_);
lean_closure_set(v___f_1266_, 1, v___x_1265_);
lean_closure_set(v___f_1266_, 2, v___x_1212_);
v___x_1267_ = l_Lean_MessageData_hasTag(v___f_1266_, v_data_1263_);
if (v___x_1267_ == 0)
{
lean_dec_ref(v___x_1219_);
lean_del_object(v___x_1196_);
v_a_1186_ = v___x_1211_;
goto v___jp_1185_;
}
else
{
v___y_1221_ = v___y_1182_;
v___y_1222_ = v___y_1183_;
goto v___jp_1220_;
}
}
v___jp_1220_:
{
lean_object* v___x_1223_; lean_object* v_fileName_1224_; lean_object* v_pos_1225_; lean_object* v_endPos_1226_; uint8_t v_keepFullRange_1227_; uint8_t v_severity_1228_; uint8_t v_isSilent_1229_; lean_object* v_caption_1230_; lean_object* v_data_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1262_; 
v___x_1223_ = lean_st_ref_take(v___y_1222_);
v_fileName_1224_ = lean_ctor_get(v___x_1219_, 0);
v_pos_1225_ = lean_ctor_get(v___x_1219_, 1);
v_endPos_1226_ = lean_ctor_get(v___x_1219_, 2);
v_keepFullRange_1227_ = lean_ctor_get_uint8(v___x_1219_, sizeof(void*)*5);
v_severity_1228_ = lean_ctor_get_uint8(v___x_1219_, sizeof(void*)*5 + 1);
v_isSilent_1229_ = lean_ctor_get_uint8(v___x_1219_, sizeof(void*)*5 + 2);
v_caption_1230_ = lean_ctor_get(v___x_1219_, 3);
v_data_1231_ = lean_ctor_get(v___x_1219_, 4);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1233_ = v___x_1219_;
v_isShared_1234_ = v_isSharedCheck_1262_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_data_1231_);
lean_inc(v_caption_1230_);
lean_inc(v_endPos_1226_);
lean_inc(v_pos_1225_);
lean_inc(v_fileName_1224_);
lean_dec(v___x_1219_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1262_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v_currNamespace_1235_; lean_object* v_openDecls_1236_; lean_object* v_env_1237_; lean_object* v_nextMacroScope_1238_; lean_object* v_ngen_1239_; lean_object* v_auxDeclNGen_1240_; lean_object* v_traceState_1241_; lean_object* v_cache_1242_; lean_object* v_messages_1243_; lean_object* v_infoState_1244_; lean_object* v_snapshotTasks_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1261_; 
v_currNamespace_1235_ = lean_ctor_get(v___y_1221_, 6);
v_openDecls_1236_ = lean_ctor_get(v___y_1221_, 7);
v_env_1237_ = lean_ctor_get(v___x_1223_, 0);
v_nextMacroScope_1238_ = lean_ctor_get(v___x_1223_, 1);
v_ngen_1239_ = lean_ctor_get(v___x_1223_, 2);
v_auxDeclNGen_1240_ = lean_ctor_get(v___x_1223_, 3);
v_traceState_1241_ = lean_ctor_get(v___x_1223_, 4);
v_cache_1242_ = lean_ctor_get(v___x_1223_, 5);
v_messages_1243_ = lean_ctor_get(v___x_1223_, 6);
v_infoState_1244_ = lean_ctor_get(v___x_1223_, 7);
v_snapshotTasks_1245_ = lean_ctor_get(v___x_1223_, 8);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1247_ = v___x_1223_;
v_isShared_1248_ = v_isSharedCheck_1261_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_snapshotTasks_1245_);
lean_inc(v_infoState_1244_);
lean_inc(v_messages_1243_);
lean_inc(v_cache_1242_);
lean_inc(v_traceState_1241_);
lean_inc(v_auxDeclNGen_1240_);
lean_inc(v_ngen_1239_);
lean_inc(v_nextMacroScope_1238_);
lean_inc(v_env_1237_);
lean_dec(v___x_1223_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1261_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
lean_inc(v_openDecls_1236_);
lean_inc(v_currNamespace_1235_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 1, v_openDecls_1236_);
lean_ctor_set(v___x_1196_, 0, v_currNamespace_1235_);
v___x_1250_ = v___x_1196_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_currNamespace_1235_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_openDecls_1236_);
v___x_1250_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
lean_object* v___x_1251_; lean_object* v___x_1253_; 
v___x_1251_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
lean_ctor_set(v___x_1251_, 1, v_data_1231_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 4, v___x_1251_);
v___x_1253_ = v___x_1233_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_fileName_1224_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v_pos_1225_);
lean_ctor_set(v_reuseFailAlloc_1259_, 2, v_endPos_1226_);
lean_ctor_set(v_reuseFailAlloc_1259_, 3, v_caption_1230_);
lean_ctor_set(v_reuseFailAlloc_1259_, 4, v___x_1251_);
lean_ctor_set_uint8(v_reuseFailAlloc_1259_, sizeof(void*)*5, v_keepFullRange_1227_);
lean_ctor_set_uint8(v_reuseFailAlloc_1259_, sizeof(void*)*5 + 1, v_severity_1228_);
lean_ctor_set_uint8(v_reuseFailAlloc_1259_, sizeof(void*)*5 + 2, v_isSilent_1229_);
v___x_1253_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1254_; lean_object* v___x_1256_; 
v___x_1254_ = l_Lean_MessageLog_add(v___x_1253_, v_messages_1243_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 6, v___x_1254_);
v___x_1256_ = v___x_1247_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_env_1237_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v_nextMacroScope_1238_);
lean_ctor_set(v_reuseFailAlloc_1258_, 2, v_ngen_1239_);
lean_ctor_set(v_reuseFailAlloc_1258_, 3, v_auxDeclNGen_1240_);
lean_ctor_set(v_reuseFailAlloc_1258_, 4, v_traceState_1241_);
lean_ctor_set(v_reuseFailAlloc_1258_, 5, v_cache_1242_);
lean_ctor_set(v_reuseFailAlloc_1258_, 6, v___x_1254_);
lean_ctor_set(v_reuseFailAlloc_1258_, 7, v_infoState_1244_);
lean_ctor_set(v_reuseFailAlloc_1258_, 8, v_snapshotTasks_1245_);
v___x_1256_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
lean_object* v___x_1257_; 
v___x_1257_ = lean_st_ref_put(v___y_1222_, v___x_1256_);
v_a_1186_ = v___x_1211_;
goto v___jp_1185_;
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
v___jp_1185_:
{
size_t v___x_1187_; size_t v___x_1188_; 
v___x_1187_ = ((size_t)1ULL);
v___x_1188_ = lean_usize_add(v_i_1180_, v___x_1187_);
v_i_1180_ = v___x_1188_;
v_b_1181_ = v_a_1186_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___boxed(lean_object* v___x_1271_, lean_object* v_as_1272_, lean_object* v_sz_1273_, lean_object* v_i_1274_, lean_object* v_b_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
uint8_t v___x_36192__boxed_1279_; size_t v_sz_boxed_1280_; size_t v_i_boxed_1281_; lean_object* v_res_1282_; 
v___x_36192__boxed_1279_ = lean_unbox(v___x_1271_);
v_sz_boxed_1280_ = lean_unbox_usize(v_sz_1273_);
lean_dec(v_sz_1273_);
v_i_boxed_1281_ = lean_unbox_usize(v_i_1274_);
lean_dec(v_i_1274_);
v_res_1282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(v___x_36192__boxed_1279_, v_as_1272_, v_sz_boxed_1280_, v_i_boxed_1281_, v_b_1275_, v___y_1276_, v___y_1277_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec_ref(v_as_1272_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(lean_object* v_opts_1283_, lean_object* v_opt_1284_){
_start:
{
lean_object* v_name_1285_; lean_object* v_map_1286_; lean_object* v___x_1287_; 
v_name_1285_ = lean_ctor_get(v_opt_1284_, 0);
v_map_1286_ = lean_ctor_get(v_opts_1283_, 0);
v___x_1287_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1286_, v_name_1285_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v___x_1288_; 
v___x_1288_ = lean_box(0);
return v___x_1288_;
}
else
{
lean_object* v_val_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1298_; 
v_val_1289_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1291_ = v___x_1287_;
v_isShared_1292_ = v_isSharedCheck_1298_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_val_1289_);
lean_dec(v___x_1287_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1298_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
if (lean_obj_tag(v_val_1289_) == 0)
{
lean_object* v_v_1293_; lean_object* v___x_1295_; 
v_v_1293_ = lean_ctor_get(v_val_1289_, 0);
lean_inc_ref(v_v_1293_);
lean_dec_ref_known(v_val_1289_, 1);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 0, v_v_1293_);
v___x_1295_ = v___x_1291_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_v_1293_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
else
{
lean_object* v___x_1297_; 
lean_del_object(v___x_1291_);
lean_dec(v_val_1289_);
v___x_1297_ = lean_box(0);
return v___x_1297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15___boxed(lean_object* v_opts_1299_, lean_object* v_opt_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(v_opts_1299_, v_opt_1300_);
lean_dec_ref(v_opt_1300_);
lean_dec_ref(v_opts_1299_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(lean_object* v_a_1302_, lean_object* v_fallback_1303_, lean_object* v_x_1304_){
_start:
{
if (lean_obj_tag(v_x_1304_) == 0)
{
lean_inc(v_fallback_1303_);
return v_fallback_1303_;
}
else
{
lean_object* v_key_1305_; lean_object* v_value_1306_; lean_object* v_tail_1307_; lean_object* v_fst_1308_; lean_object* v_snd_1309_; lean_object* v_fst_1310_; lean_object* v_snd_1311_; uint8_t v_decide_1312_; 
v_key_1305_ = lean_ctor_get(v_x_1304_, 0);
v_value_1306_ = lean_ctor_get(v_x_1304_, 1);
v_tail_1307_ = lean_ctor_get(v_x_1304_, 2);
v_fst_1308_ = lean_ctor_get(v_key_1305_, 0);
v_snd_1309_ = lean_ctor_get(v_key_1305_, 1);
v_fst_1310_ = lean_ctor_get(v_a_1302_, 0);
v_snd_1311_ = lean_ctor_get(v_a_1302_, 1);
v_decide_1312_ = lean_nat_dec_eq(v_fst_1308_, v_fst_1310_);
if (v_decide_1312_ == 0)
{
v_x_1304_ = v_tail_1307_;
goto _start;
}
else
{
uint8_t v_decide_1314_; 
v_decide_1314_ = lean_nat_dec_eq(v_snd_1309_, v_snd_1311_);
if (v_decide_1314_ == 0)
{
v_x_1304_ = v_tail_1307_;
goto _start;
}
else
{
lean_inc(v_value_1306_);
return v_value_1306_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg___boxed(lean_object* v_a_1316_, lean_object* v_fallback_1317_, lean_object* v_x_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_1316_, v_fallback_1317_, v_x_1318_);
lean_dec(v_x_1318_);
lean_dec(v_fallback_1317_);
lean_dec_ref(v_a_1316_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(lean_object* v_m_1320_, lean_object* v_a_1321_, lean_object* v_fallback_1322_){
_start:
{
lean_object* v_buckets_1323_; lean_object* v_fst_1324_; lean_object* v_snd_1325_; lean_object* v___x_1326_; uint64_t v___x_1327_; uint64_t v___x_1328_; uint64_t v___x_1329_; uint64_t v___x_1330_; uint64_t v___x_1331_; uint64_t v_fold_1332_; uint64_t v___x_1333_; uint64_t v___x_1334_; uint64_t v___x_1335_; size_t v___x_1336_; size_t v___x_1337_; size_t v___x_1338_; size_t v___x_1339_; size_t v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v_buckets_1323_ = lean_ctor_get(v_m_1320_, 1);
v_fst_1324_ = lean_ctor_get(v_a_1321_, 0);
v_snd_1325_ = lean_ctor_get(v_a_1321_, 1);
v___x_1326_ = lean_array_get_size(v_buckets_1323_);
v___x_1327_ = l_String_instHashableRaw_hash(v_fst_1324_);
v___x_1328_ = l_String_instHashableRaw_hash(v_snd_1325_);
v___x_1329_ = lean_uint64_mix_hash(v___x_1327_, v___x_1328_);
v___x_1330_ = 32ULL;
v___x_1331_ = lean_uint64_shift_right(v___x_1329_, v___x_1330_);
v_fold_1332_ = lean_uint64_xor(v___x_1329_, v___x_1331_);
v___x_1333_ = 16ULL;
v___x_1334_ = lean_uint64_shift_right(v_fold_1332_, v___x_1333_);
v___x_1335_ = lean_uint64_xor(v_fold_1332_, v___x_1334_);
v___x_1336_ = lean_uint64_to_usize(v___x_1335_);
v___x_1337_ = lean_usize_of_nat(v___x_1326_);
v___x_1338_ = ((size_t)1ULL);
v___x_1339_ = lean_usize_sub(v___x_1337_, v___x_1338_);
v___x_1340_ = lean_usize_land(v___x_1336_, v___x_1339_);
v___x_1341_ = lean_array_uget_borrowed(v_buckets_1323_, v___x_1340_);
v___x_1342_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_1321_, v_fallback_1322_, v___x_1341_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg___boxed(lean_object* v_m_1343_, lean_object* v_a_1344_, lean_object* v_fallback_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_m_1343_, v_a_1344_, v_fallback_1345_);
lean_dec(v_fallback_1345_);
lean_dec_ref(v_a_1344_);
lean_dec_ref(v_m_1343_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(lean_object* v_x_1347_, lean_object* v_x_1348_){
_start:
{
if (lean_obj_tag(v_x_1348_) == 0)
{
return v_x_1347_;
}
else
{
lean_object* v_key_1349_; lean_object* v_value_1350_; lean_object* v_tail_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1378_; 
v_key_1349_ = lean_ctor_get(v_x_1348_, 0);
v_value_1350_ = lean_ctor_get(v_x_1348_, 1);
v_tail_1351_ = lean_ctor_get(v_x_1348_, 2);
v_isSharedCheck_1378_ = !lean_is_exclusive(v_x_1348_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1353_ = v_x_1348_;
v_isShared_1354_ = v_isSharedCheck_1378_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_tail_1351_);
lean_inc(v_value_1350_);
lean_inc(v_key_1349_);
lean_dec(v_x_1348_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1378_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v_fst_1355_; lean_object* v_snd_1356_; lean_object* v___x_1357_; uint64_t v___x_1358_; uint64_t v___x_1359_; uint64_t v___x_1360_; uint64_t v___x_1361_; uint64_t v___x_1362_; uint64_t v_fold_1363_; uint64_t v___x_1364_; uint64_t v___x_1365_; uint64_t v___x_1366_; size_t v___x_1367_; size_t v___x_1368_; size_t v___x_1369_; size_t v___x_1370_; size_t v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1374_; 
v_fst_1355_ = lean_ctor_get(v_key_1349_, 0);
v_snd_1356_ = lean_ctor_get(v_key_1349_, 1);
v___x_1357_ = lean_array_get_size(v_x_1347_);
v___x_1358_ = l_String_instHashableRaw_hash(v_fst_1355_);
v___x_1359_ = l_String_instHashableRaw_hash(v_snd_1356_);
v___x_1360_ = lean_uint64_mix_hash(v___x_1358_, v___x_1359_);
v___x_1361_ = 32ULL;
v___x_1362_ = lean_uint64_shift_right(v___x_1360_, v___x_1361_);
v_fold_1363_ = lean_uint64_xor(v___x_1360_, v___x_1362_);
v___x_1364_ = 16ULL;
v___x_1365_ = lean_uint64_shift_right(v_fold_1363_, v___x_1364_);
v___x_1366_ = lean_uint64_xor(v_fold_1363_, v___x_1365_);
v___x_1367_ = lean_uint64_to_usize(v___x_1366_);
v___x_1368_ = lean_usize_of_nat(v___x_1357_);
v___x_1369_ = ((size_t)1ULL);
v___x_1370_ = lean_usize_sub(v___x_1368_, v___x_1369_);
v___x_1371_ = lean_usize_land(v___x_1367_, v___x_1370_);
v___x_1372_ = lean_array_uget_borrowed(v_x_1347_, v___x_1371_);
lean_inc(v___x_1372_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 2, v___x_1372_);
v___x_1374_ = v___x_1353_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_key_1349_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v_value_1350_);
lean_ctor_set(v_reuseFailAlloc_1377_, 2, v___x_1372_);
v___x_1374_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
lean_object* v___x_1375_; 
v___x_1375_ = lean_array_uset(v_x_1347_, v___x_1371_, v___x_1374_);
v_x_1347_ = v___x_1375_;
v_x_1348_ = v_tail_1351_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(lean_object* v_i_1379_, lean_object* v_source_1380_, lean_object* v_target_1381_){
_start:
{
lean_object* v___x_1382_; uint8_t v___x_1383_; 
v___x_1382_ = lean_array_get_size(v_source_1380_);
v___x_1383_ = lean_nat_dec_lt(v_i_1379_, v___x_1382_);
if (v___x_1383_ == 0)
{
lean_dec_ref(v_source_1380_);
lean_dec(v_i_1379_);
return v_target_1381_;
}
else
{
lean_object* v_es_1384_; lean_object* v___x_1385_; lean_object* v_source_1386_; lean_object* v_target_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v_es_1384_ = lean_array_fget(v_source_1380_, v_i_1379_);
v___x_1385_ = lean_box(0);
v_source_1386_ = lean_array_fset(v_source_1380_, v_i_1379_, v___x_1385_);
v_target_1387_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(v_target_1381_, v_es_1384_);
v___x_1388_ = lean_unsigned_to_nat(1u);
v___x_1389_ = lean_nat_add(v_i_1379_, v___x_1388_);
lean_dec(v_i_1379_);
v_i_1379_ = v___x_1389_;
v_source_1380_ = v_source_1386_;
v_target_1381_ = v_target_1387_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(lean_object* v_data_1391_){
_start:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v_nbuckets_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1392_ = lean_array_get_size(v_data_1391_);
v___x_1393_ = lean_unsigned_to_nat(2u);
v_nbuckets_1394_ = lean_nat_mul(v___x_1392_, v___x_1393_);
v___x_1395_ = lean_unsigned_to_nat(0u);
v___x_1396_ = lean_box(0);
v___x_1397_ = lean_mk_array(v_nbuckets_1394_, v___x_1396_);
v___x_1398_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(v___x_1395_, v_data_1391_, v___x_1397_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(lean_object* v_a_1399_, lean_object* v_b_1400_, lean_object* v_x_1401_){
_start:
{
if (lean_obj_tag(v_x_1401_) == 0)
{
lean_dec(v_b_1400_);
lean_dec_ref(v_a_1399_);
return v_x_1401_;
}
else
{
lean_object* v_key_1402_; lean_object* v_value_1403_; lean_object* v_tail_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1420_; 
v_key_1402_ = lean_ctor_get(v_x_1401_, 0);
v_value_1403_ = lean_ctor_get(v_x_1401_, 1);
v_tail_1404_ = lean_ctor_get(v_x_1401_, 2);
v_isSharedCheck_1420_ = !lean_is_exclusive(v_x_1401_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1406_ = v_x_1401_;
v_isShared_1407_ = v_isSharedCheck_1420_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_tail_1404_);
lean_inc(v_value_1403_);
lean_inc(v_key_1402_);
lean_dec(v_x_1401_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1420_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v_fst_1413_; lean_object* v_snd_1414_; lean_object* v_fst_1415_; lean_object* v_snd_1416_; uint8_t v_decide_1417_; 
v_fst_1413_ = lean_ctor_get(v_key_1402_, 0);
v_snd_1414_ = lean_ctor_get(v_key_1402_, 1);
v_fst_1415_ = lean_ctor_get(v_a_1399_, 0);
v_snd_1416_ = lean_ctor_get(v_a_1399_, 1);
v_decide_1417_ = lean_nat_dec_eq(v_fst_1413_, v_fst_1415_);
if (v_decide_1417_ == 0)
{
goto v___jp_1408_;
}
else
{
uint8_t v_decide_1418_; 
v_decide_1418_ = lean_nat_dec_eq(v_snd_1414_, v_snd_1416_);
if (v_decide_1418_ == 0)
{
goto v___jp_1408_;
}
else
{
lean_object* v___x_1419_; 
lean_del_object(v___x_1406_);
lean_dec(v_value_1403_);
lean_dec(v_key_1402_);
v___x_1419_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1419_, 0, v_a_1399_);
lean_ctor_set(v___x_1419_, 1, v_b_1400_);
lean_ctor_set(v___x_1419_, 2, v_tail_1404_);
return v___x_1419_;
}
}
v___jp_1408_:
{
lean_object* v___x_1409_; lean_object* v___x_1411_; 
v___x_1409_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_1399_, v_b_1400_, v_tail_1404_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 2, v___x_1409_);
v___x_1411_ = v___x_1406_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_key_1402_);
lean_ctor_set(v_reuseFailAlloc_1412_, 1, v_value_1403_);
lean_ctor_set(v_reuseFailAlloc_1412_, 2, v___x_1409_);
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
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(lean_object* v_a_1421_, lean_object* v_x_1422_){
_start:
{
if (lean_obj_tag(v_x_1422_) == 0)
{
uint8_t v___x_1423_; 
v___x_1423_ = 0;
return v___x_1423_;
}
else
{
lean_object* v_key_1424_; lean_object* v_tail_1425_; lean_object* v_fst_1426_; lean_object* v_snd_1427_; lean_object* v_fst_1428_; lean_object* v_snd_1429_; uint8_t v_decide_1430_; 
v_key_1424_ = lean_ctor_get(v_x_1422_, 0);
v_tail_1425_ = lean_ctor_get(v_x_1422_, 2);
v_fst_1426_ = lean_ctor_get(v_key_1424_, 0);
v_snd_1427_ = lean_ctor_get(v_key_1424_, 1);
v_fst_1428_ = lean_ctor_get(v_a_1421_, 0);
v_snd_1429_ = lean_ctor_get(v_a_1421_, 1);
v_decide_1430_ = lean_nat_dec_eq(v_fst_1426_, v_fst_1428_);
if (v_decide_1430_ == 0)
{
v_x_1422_ = v_tail_1425_;
goto _start;
}
else
{
uint8_t v_decide_1432_; 
v_decide_1432_ = lean_nat_dec_eq(v_snd_1427_, v_snd_1429_);
if (v_decide_1432_ == 0)
{
v_x_1422_ = v_tail_1425_;
goto _start;
}
else
{
return v_decide_1432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg___boxed(lean_object* v_a_1434_, lean_object* v_x_1435_){
_start:
{
uint8_t v_res_1436_; lean_object* v_r_1437_; 
v_res_1436_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_1434_, v_x_1435_);
lean_dec(v_x_1435_);
lean_dec_ref(v_a_1434_);
v_r_1437_ = lean_box(v_res_1436_);
return v_r_1437_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(lean_object* v_m_1438_, lean_object* v_a_1439_, lean_object* v_b_1440_){
_start:
{
lean_object* v_size_1441_; lean_object* v_buckets_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1489_; 
v_size_1441_ = lean_ctor_get(v_m_1438_, 0);
v_buckets_1442_ = lean_ctor_get(v_m_1438_, 1);
v_isSharedCheck_1489_ = !lean_is_exclusive(v_m_1438_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1444_ = v_m_1438_;
v_isShared_1445_ = v_isSharedCheck_1489_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_buckets_1442_);
lean_inc(v_size_1441_);
lean_dec(v_m_1438_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1489_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v_fst_1446_; lean_object* v_snd_1447_; lean_object* v___x_1448_; uint64_t v___x_1449_; uint64_t v___x_1450_; uint64_t v___x_1451_; uint64_t v___x_1452_; uint64_t v___x_1453_; uint64_t v_fold_1454_; uint64_t v___x_1455_; uint64_t v___x_1456_; uint64_t v___x_1457_; size_t v___x_1458_; size_t v___x_1459_; size_t v___x_1460_; size_t v___x_1461_; size_t v___x_1462_; lean_object* v_bkt_1463_; uint8_t v___x_1464_; 
v_fst_1446_ = lean_ctor_get(v_a_1439_, 0);
v_snd_1447_ = lean_ctor_get(v_a_1439_, 1);
v___x_1448_ = lean_array_get_size(v_buckets_1442_);
v___x_1449_ = l_String_instHashableRaw_hash(v_fst_1446_);
v___x_1450_ = l_String_instHashableRaw_hash(v_snd_1447_);
v___x_1451_ = lean_uint64_mix_hash(v___x_1449_, v___x_1450_);
v___x_1452_ = 32ULL;
v___x_1453_ = lean_uint64_shift_right(v___x_1451_, v___x_1452_);
v_fold_1454_ = lean_uint64_xor(v___x_1451_, v___x_1453_);
v___x_1455_ = 16ULL;
v___x_1456_ = lean_uint64_shift_right(v_fold_1454_, v___x_1455_);
v___x_1457_ = lean_uint64_xor(v_fold_1454_, v___x_1456_);
v___x_1458_ = lean_uint64_to_usize(v___x_1457_);
v___x_1459_ = lean_usize_of_nat(v___x_1448_);
v___x_1460_ = ((size_t)1ULL);
v___x_1461_ = lean_usize_sub(v___x_1459_, v___x_1460_);
v___x_1462_ = lean_usize_land(v___x_1458_, v___x_1461_);
v_bkt_1463_ = lean_array_uget_borrowed(v_buckets_1442_, v___x_1462_);
v___x_1464_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_1439_, v_bkt_1463_);
if (v___x_1464_ == 0)
{
lean_object* v___x_1465_; lean_object* v_size_x27_1466_; lean_object* v___x_1467_; lean_object* v_buckets_x27_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; uint8_t v___x_1474_; 
v___x_1465_ = lean_unsigned_to_nat(1u);
v_size_x27_1466_ = lean_nat_add(v_size_1441_, v___x_1465_);
lean_dec(v_size_1441_);
lean_inc(v_bkt_1463_);
v___x_1467_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1467_, 0, v_a_1439_);
lean_ctor_set(v___x_1467_, 1, v_b_1440_);
lean_ctor_set(v___x_1467_, 2, v_bkt_1463_);
v_buckets_x27_1468_ = lean_array_uset(v_buckets_1442_, v___x_1462_, v___x_1467_);
v___x_1469_ = lean_unsigned_to_nat(4u);
v___x_1470_ = lean_nat_mul(v_size_x27_1466_, v___x_1469_);
v___x_1471_ = lean_unsigned_to_nat(3u);
v___x_1472_ = lean_nat_div(v___x_1470_, v___x_1471_);
lean_dec(v___x_1470_);
v___x_1473_ = lean_array_get_size(v_buckets_x27_1468_);
v___x_1474_ = lean_nat_dec_le(v___x_1472_, v___x_1473_);
lean_dec(v___x_1472_);
if (v___x_1474_ == 0)
{
lean_object* v_val_1475_; lean_object* v___x_1477_; 
v_val_1475_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(v_buckets_x27_1468_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 1, v_val_1475_);
lean_ctor_set(v___x_1444_, 0, v_size_x27_1466_);
v___x_1477_ = v___x_1444_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_size_x27_1466_);
lean_ctor_set(v_reuseFailAlloc_1478_, 1, v_val_1475_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
else
{
lean_object* v___x_1480_; 
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 1, v_buckets_x27_1468_);
lean_ctor_set(v___x_1444_, 0, v_size_x27_1466_);
v___x_1480_ = v___x_1444_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_size_x27_1466_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_buckets_x27_1468_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
else
{
lean_object* v___x_1482_; lean_object* v_buckets_x27_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1487_; 
lean_inc(v_bkt_1463_);
v___x_1482_ = lean_box(0);
v_buckets_x27_1483_ = lean_array_uset(v_buckets_1442_, v___x_1462_, v___x_1482_);
v___x_1484_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_1439_, v_b_1440_, v_bkt_1463_);
v___x_1485_ = lean_array_uset(v_buckets_x27_1483_, v___x_1462_, v___x_1484_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 1, v___x_1485_);
v___x_1487_ = v___x_1444_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_size_1441_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v___x_1485_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(uint8_t v___x_1492_, lean_object* v_as_1493_, size_t v_sz_1494_, size_t v_i_1495_, lean_object* v_b_1496_, lean_object* v___y_1497_){
_start:
{
uint8_t v___x_1499_; 
v___x_1499_ = lean_usize_dec_lt(v_i_1495_, v_sz_1494_);
if (v___x_1499_ == 0)
{
lean_object* v___x_1500_; 
v___x_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1500_, 0, v_b_1496_);
return v___x_1500_;
}
else
{
lean_object* v_snd_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1538_; 
v_snd_1501_ = lean_ctor_get(v_b_1496_, 1);
v_isSharedCheck_1538_ = !lean_is_exclusive(v_b_1496_);
if (v_isSharedCheck_1538_ == 0)
{
lean_object* v_unused_1539_; 
v_unused_1539_ = lean_ctor_get(v_b_1496_, 0);
lean_dec(v_unused_1539_);
v___x_1503_ = v_b_1496_;
v_isShared_1504_ = v_isSharedCheck_1538_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_snd_1501_);
lean_dec(v_b_1496_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1538_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v_ref_1505_; lean_object* v_a_1506_; lean_object* v_ref_1507_; lean_object* v_msg_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1537_; 
v_ref_1505_ = lean_ctor_get(v___y_1497_, 5);
v_a_1506_ = lean_array_uget(v_as_1493_, v_i_1495_);
v_ref_1507_ = lean_ctor_get(v_a_1506_, 0);
v_msg_1508_ = lean_ctor_get(v_a_1506_, 1);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_a_1506_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1510_ = v_a_1506_;
v_isShared_1511_ = v_isSharedCheck_1537_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_msg_1508_);
lean_inc(v_ref_1507_);
lean_dec(v_a_1506_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1537_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1512_; lean_object* v___y_1514_; lean_object* v___y_1515_; lean_object* v_ref_1529_; lean_object* v___y_1531_; lean_object* v___x_1534_; 
v___x_1512_ = lean_box(0);
v_ref_1529_ = l_Lean_replaceRef(v_ref_1507_, v_ref_1505_);
lean_dec(v_ref_1507_);
v___x_1534_ = l_Lean_Syntax_getPos_x3f(v_ref_1529_, v___x_1492_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_unsigned_to_nat(0u);
v___y_1531_ = v___x_1535_;
goto v___jp_1530_;
}
else
{
lean_object* v_val_1536_; 
v_val_1536_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_val_1536_);
lean_dec_ref_known(v___x_1534_, 1);
v___y_1531_ = v_val_1536_;
goto v___jp_1530_;
}
v___jp_1513_:
{
lean_object* v___x_1517_; 
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 1, v___y_1515_);
lean_ctor_set(v___x_1503_, 0, v___y_1514_);
v___x_1517_ = v___x_1503_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___y_1514_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v___y_1515_);
v___x_1517_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v_pos2traces_1521_; lean_object* v___x_1523_; 
v___x_1518_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1519_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1501_, v___x_1517_, v___x_1518_);
v___x_1520_ = lean_array_push(v___x_1519_, v_msg_1508_);
v_pos2traces_1521_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1501_, v___x_1517_, v___x_1520_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 1, v_pos2traces_1521_);
lean_ctor_set(v___x_1510_, 0, v___x_1512_);
v___x_1523_ = v___x_1510_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1512_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v_pos2traces_1521_);
v___x_1523_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
size_t v___x_1524_; size_t v___x_1525_; 
v___x_1524_ = ((size_t)1ULL);
v___x_1525_ = lean_usize_add(v_i_1495_, v___x_1524_);
v_i_1495_ = v___x_1525_;
v_b_1496_ = v___x_1523_;
goto _start;
}
}
}
v___jp_1530_:
{
lean_object* v___x_1532_; 
v___x_1532_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1529_, v___x_1492_);
lean_dec(v_ref_1529_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_inc(v___y_1531_);
v___y_1514_ = v___y_1531_;
v___y_1515_ = v___y_1531_;
goto v___jp_1513_;
}
else
{
lean_object* v_val_1533_; 
v_val_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_val_1533_);
lean_dec_ref_known(v___x_1532_, 1);
v___y_1514_ = v___y_1531_;
v___y_1515_ = v_val_1533_;
goto v___jp_1513_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___boxed(lean_object* v___x_1540_, lean_object* v_as_1541_, lean_object* v_sz_1542_, lean_object* v_i_1543_, lean_object* v_b_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
uint8_t v___x_36661__boxed_1547_; size_t v_sz_boxed_1548_; size_t v_i_boxed_1549_; lean_object* v_res_1550_; 
v___x_36661__boxed_1547_ = lean_unbox(v___x_1540_);
v_sz_boxed_1548_ = lean_unbox_usize(v_sz_1542_);
lean_dec(v_sz_1542_);
v_i_boxed_1549_ = lean_unbox_usize(v_i_1543_);
lean_dec(v_i_1543_);
v_res_1550_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_36661__boxed_1547_, v_as_1541_, v_sz_boxed_1548_, v_i_boxed_1549_, v_b_1544_, v___y_1545_);
lean_dec_ref(v___y_1545_);
lean_dec_ref(v_as_1541_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(uint8_t v___x_1551_, lean_object* v_as_1552_, size_t v_sz_1553_, size_t v_i_1554_, lean_object* v_b_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
uint8_t v___x_1559_; 
v___x_1559_ = lean_usize_dec_lt(v_i_1554_, v_sz_1553_);
if (v___x_1559_ == 0)
{
lean_object* v___x_1560_; 
v___x_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1560_, 0, v_b_1555_);
return v___x_1560_;
}
else
{
lean_object* v_snd_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1598_; 
v_snd_1561_ = lean_ctor_get(v_b_1555_, 1);
v_isSharedCheck_1598_ = !lean_is_exclusive(v_b_1555_);
if (v_isSharedCheck_1598_ == 0)
{
lean_object* v_unused_1599_; 
v_unused_1599_ = lean_ctor_get(v_b_1555_, 0);
lean_dec(v_unused_1599_);
v___x_1563_ = v_b_1555_;
v_isShared_1564_ = v_isSharedCheck_1598_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_snd_1561_);
lean_dec(v_b_1555_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1598_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v_ref_1565_; lean_object* v_a_1566_; lean_object* v_ref_1567_; lean_object* v_msg_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1597_; 
v_ref_1565_ = lean_ctor_get(v___y_1556_, 5);
v_a_1566_ = lean_array_uget(v_as_1552_, v_i_1554_);
v_ref_1567_ = lean_ctor_get(v_a_1566_, 0);
v_msg_1568_ = lean_ctor_get(v_a_1566_, 1);
v_isSharedCheck_1597_ = !lean_is_exclusive(v_a_1566_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1570_ = v_a_1566_;
v_isShared_1571_ = v_isSharedCheck_1597_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_msg_1568_);
lean_inc(v_ref_1567_);
lean_dec(v_a_1566_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1597_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1572_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v_ref_1589_; lean_object* v___y_1591_; lean_object* v___x_1594_; 
v___x_1572_ = lean_box(0);
v_ref_1589_ = l_Lean_replaceRef(v_ref_1567_, v_ref_1565_);
lean_dec(v_ref_1567_);
v___x_1594_ = l_Lean_Syntax_getPos_x3f(v_ref_1589_, v___x_1551_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v___x_1595_; 
v___x_1595_ = lean_unsigned_to_nat(0u);
v___y_1591_ = v___x_1595_;
goto v___jp_1590_;
}
else
{
lean_object* v_val_1596_; 
v_val_1596_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_val_1596_);
lean_dec_ref_known(v___x_1594_, 1);
v___y_1591_ = v_val_1596_;
goto v___jp_1590_;
}
v___jp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 1, v___y_1575_);
lean_ctor_set(v___x_1563_, 0, v___y_1574_);
v___x_1577_ = v___x_1563_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___y_1574_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v___y_1575_);
v___x_1577_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v_pos2traces_1581_; lean_object* v___x_1583_; 
v___x_1578_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1579_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1561_, v___x_1577_, v___x_1578_);
v___x_1580_ = lean_array_push(v___x_1579_, v_msg_1568_);
v_pos2traces_1581_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1561_, v___x_1577_, v___x_1580_);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 1, v_pos2traces_1581_);
lean_ctor_set(v___x_1570_, 0, v___x_1572_);
v___x_1583_ = v___x_1570_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1572_);
lean_ctor_set(v_reuseFailAlloc_1587_, 1, v_pos2traces_1581_);
v___x_1583_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
size_t v___x_1584_; size_t v___x_1585_; lean_object* v___x_1586_; 
v___x_1584_ = ((size_t)1ULL);
v___x_1585_ = lean_usize_add(v_i_1554_, v___x_1584_);
v___x_1586_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_1551_, v_as_1552_, v_sz_1553_, v___x_1585_, v___x_1583_, v___y_1556_);
return v___x_1586_;
}
}
}
v___jp_1590_:
{
lean_object* v___x_1592_; 
v___x_1592_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1589_, v___x_1551_);
lean_dec(v_ref_1589_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_inc(v___y_1591_);
v___y_1574_ = v___y_1591_;
v___y_1575_ = v___y_1591_;
goto v___jp_1573_;
}
else
{
lean_object* v_val_1593_; 
v_val_1593_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_val_1593_);
lean_dec_ref_known(v___x_1592_, 1);
v___y_1574_ = v___y_1591_;
v___y_1575_ = v_val_1593_;
goto v___jp_1573_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40___boxed(lean_object* v___x_1600_, lean_object* v_as_1601_, lean_object* v_sz_1602_, lean_object* v_i_1603_, lean_object* v_b_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
uint8_t v___x_36742__boxed_1608_; size_t v_sz_boxed_1609_; size_t v_i_boxed_1610_; lean_object* v_res_1611_; 
v___x_36742__boxed_1608_ = lean_unbox(v___x_1600_);
v_sz_boxed_1609_ = lean_unbox_usize(v_sz_1602_);
lean_dec(v_sz_1602_);
v_i_boxed_1610_ = lean_unbox_usize(v_i_1603_);
lean_dec(v_i_1603_);
v_res_1611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(v___x_36742__boxed_1608_, v_as_1601_, v_sz_boxed_1609_, v_i_boxed_1610_, v_b_1604_, v___y_1605_, v___y_1606_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec_ref(v_as_1601_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(lean_object* v_init_1612_, uint8_t v___x_1613_, lean_object* v_n_1614_, lean_object* v_b_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
if (lean_obj_tag(v_n_1614_) == 0)
{
lean_object* v_cs_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; size_t v_sz_1622_; size_t v___x_1623_; lean_object* v___x_1624_; 
v_cs_1619_ = lean_ctor_get(v_n_1614_, 0);
v___x_1620_ = lean_box(0);
v___x_1621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1620_);
lean_ctor_set(v___x_1621_, 1, v_b_1615_);
v_sz_1622_ = lean_array_size(v_cs_1619_);
v___x_1623_ = ((size_t)0ULL);
v___x_1624_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(v_init_1612_, v___x_1613_, v_cs_1619_, v_sz_1622_, v___x_1623_, v___x_1621_, v___y_1616_, v___y_1617_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1639_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1627_ = v___x_1624_;
v_isShared_1628_ = v_isSharedCheck_1639_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1624_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1639_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v_fst_1629_; 
v_fst_1629_ = lean_ctor_get(v_a_1625_, 0);
if (lean_obj_tag(v_fst_1629_) == 0)
{
lean_object* v_snd_1630_; lean_object* v___x_1631_; lean_object* v___x_1633_; 
v_snd_1630_ = lean_ctor_get(v_a_1625_, 1);
lean_inc(v_snd_1630_);
lean_dec(v_a_1625_);
v___x_1631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1631_, 0, v_snd_1630_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 0, v___x_1631_);
v___x_1633_ = v___x_1627_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1631_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
else
{
lean_object* v_val_1635_; lean_object* v___x_1637_; 
lean_inc_ref(v_fst_1629_);
lean_dec(v_a_1625_);
v_val_1635_ = lean_ctor_get(v_fst_1629_, 0);
lean_inc(v_val_1635_);
lean_dec_ref_known(v_fst_1629_, 1);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 0, v_val_1635_);
v___x_1637_ = v___x_1627_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_val_1635_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
v_a_1640_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1624_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1624_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1645_; 
if (v_isShared_1643_ == 0)
{
v___x_1645_ = v___x_1642_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1640_);
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
lean_object* v_vs_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; size_t v_sz_1651_; size_t v___x_1652_; lean_object* v___x_1653_; 
v_vs_1648_ = lean_ctor_get(v_n_1614_, 0);
v___x_1649_ = lean_box(0);
v___x_1650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1649_);
lean_ctor_set(v___x_1650_, 1, v_b_1615_);
v_sz_1651_ = lean_array_size(v_vs_1648_);
v___x_1652_ = ((size_t)0ULL);
v___x_1653_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(v___x_1613_, v_vs_1648_, v_sz_1651_, v___x_1652_, v___x_1650_, v___y_1616_, v___y_1617_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1668_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1656_ = v___x_1653_;
v_isShared_1657_ = v_isSharedCheck_1668_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1653_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1668_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v_fst_1658_; 
v_fst_1658_ = lean_ctor_get(v_a_1654_, 0);
if (lean_obj_tag(v_fst_1658_) == 0)
{
lean_object* v_snd_1659_; lean_object* v___x_1660_; lean_object* v___x_1662_; 
v_snd_1659_ = lean_ctor_get(v_a_1654_, 1);
lean_inc(v_snd_1659_);
lean_dec(v_a_1654_);
v___x_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1660_, 0, v_snd_1659_);
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 0, v___x_1660_);
v___x_1662_ = v___x_1656_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1660_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
else
{
lean_object* v_val_1664_; lean_object* v___x_1666_; 
lean_inc_ref(v_fst_1658_);
lean_dec(v_a_1654_);
v_val_1664_ = lean_ctor_get(v_fst_1658_, 0);
lean_inc(v_val_1664_);
lean_dec_ref_known(v_fst_1658_, 1);
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 0, v_val_1664_);
v___x_1666_ = v___x_1656_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_val_1664_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
else
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
v_a_1669_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___x_1653_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1653_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1669_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(lean_object* v_init_1677_, uint8_t v___x_1678_, lean_object* v_as_1679_, size_t v_sz_1680_, size_t v_i_1681_, lean_object* v_b_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
uint8_t v___x_1686_; 
v___x_1686_ = lean_usize_dec_lt(v_i_1681_, v_sz_1680_);
if (v___x_1686_ == 0)
{
lean_object* v___x_1687_; 
v___x_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1687_, 0, v_b_1682_);
return v___x_1687_;
}
else
{
lean_object* v_snd_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1722_; 
v_snd_1688_ = lean_ctor_get(v_b_1682_, 1);
v_isSharedCheck_1722_ = !lean_is_exclusive(v_b_1682_);
if (v_isSharedCheck_1722_ == 0)
{
lean_object* v_unused_1723_; 
v_unused_1723_ = lean_ctor_get(v_b_1682_, 0);
lean_dec(v_unused_1723_);
v___x_1690_ = v_b_1682_;
v_isShared_1691_ = v_isSharedCheck_1722_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_snd_1688_);
lean_dec(v_b_1682_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1722_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v_a_1692_; lean_object* v___x_1693_; 
v_a_1692_ = lean_array_uget_borrowed(v_as_1679_, v_i_1681_);
lean_inc(v_snd_1688_);
v___x_1693_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1677_, v___x_1678_, v_a_1692_, v_snd_1688_, v___y_1683_, v___y_1684_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1713_; 
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1696_ = v___x_1693_;
v_isShared_1697_ = v_isSharedCheck_1713_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1693_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1713_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
if (lean_obj_tag(v_a_1694_) == 0)
{
lean_object* v___x_1698_; lean_object* v___x_1700_; 
v___x_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1698_, 0, v_a_1694_);
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 0, v___x_1698_);
v___x_1700_ = v___x_1690_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1698_);
lean_ctor_set(v_reuseFailAlloc_1704_, 1, v_snd_1688_);
v___x_1700_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
lean_object* v___x_1702_; 
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 0, v___x_1700_);
v___x_1702_ = v___x_1696_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1700_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
else
{
lean_object* v_a_1705_; lean_object* v___x_1706_; lean_object* v___x_1708_; 
lean_del_object(v___x_1696_);
lean_dec(v_snd_1688_);
v_a_1705_ = lean_ctor_get(v_a_1694_, 0);
lean_inc(v_a_1705_);
lean_dec_ref_known(v_a_1694_, 1);
v___x_1706_ = lean_box(0);
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 1, v_a_1705_);
lean_ctor_set(v___x_1690_, 0, v___x_1706_);
v___x_1708_ = v___x_1690_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1706_);
lean_ctor_set(v_reuseFailAlloc_1712_, 1, v_a_1705_);
v___x_1708_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
size_t v___x_1709_; size_t v___x_1710_; 
v___x_1709_ = ((size_t)1ULL);
v___x_1710_ = lean_usize_add(v_i_1681_, v___x_1709_);
v_i_1681_ = v___x_1710_;
v_b_1682_ = v___x_1708_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
lean_del_object(v___x_1690_);
lean_dec(v_snd_1688_);
v_a_1714_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1693_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1693_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39___boxed(lean_object* v_init_1724_, lean_object* v___x_1725_, lean_object* v_as_1726_, lean_object* v_sz_1727_, lean_object* v_i_1728_, lean_object* v_b_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
uint8_t v___x_36823__boxed_1733_; size_t v_sz_boxed_1734_; size_t v_i_boxed_1735_; lean_object* v_res_1736_; 
v___x_36823__boxed_1733_ = lean_unbox(v___x_1725_);
v_sz_boxed_1734_ = lean_unbox_usize(v_sz_1727_);
lean_dec(v_sz_1727_);
v_i_boxed_1735_ = lean_unbox_usize(v_i_1728_);
lean_dec(v_i_1728_);
v_res_1736_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(v_init_1724_, v___x_36823__boxed_1733_, v_as_1726_, v_sz_boxed_1734_, v_i_boxed_1735_, v_b_1729_, v___y_1730_, v___y_1731_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec_ref(v_as_1726_);
lean_dec_ref(v_init_1724_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27___boxed(lean_object* v_init_1737_, lean_object* v___x_1738_, lean_object* v_n_1739_, lean_object* v_b_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
uint8_t v___x_36843__boxed_1744_; lean_object* v_res_1745_; 
v___x_36843__boxed_1744_ = lean_unbox(v___x_1738_);
v_res_1745_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1737_, v___x_36843__boxed_1744_, v_n_1739_, v_b_1740_, v___y_1741_, v___y_1742_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec_ref(v_n_1739_);
lean_dec_ref(v_init_1737_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(uint8_t v___x_1746_, lean_object* v_as_1747_, size_t v_sz_1748_, size_t v_i_1749_, lean_object* v_b_1750_, lean_object* v___y_1751_){
_start:
{
uint8_t v___x_1753_; 
v___x_1753_ = lean_usize_dec_lt(v_i_1749_, v_sz_1748_);
if (v___x_1753_ == 0)
{
lean_object* v___x_1754_; 
v___x_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1754_, 0, v_b_1750_);
return v___x_1754_;
}
else
{
lean_object* v_snd_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1792_; 
v_snd_1755_ = lean_ctor_get(v_b_1750_, 1);
v_isSharedCheck_1792_ = !lean_is_exclusive(v_b_1750_);
if (v_isSharedCheck_1792_ == 0)
{
lean_object* v_unused_1793_; 
v_unused_1793_ = lean_ctor_get(v_b_1750_, 0);
lean_dec(v_unused_1793_);
v___x_1757_ = v_b_1750_;
v_isShared_1758_ = v_isSharedCheck_1792_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_snd_1755_);
lean_dec(v_b_1750_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1792_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v_ref_1759_; lean_object* v_a_1760_; lean_object* v_ref_1761_; lean_object* v_msg_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1791_; 
v_ref_1759_ = lean_ctor_get(v___y_1751_, 5);
v_a_1760_ = lean_array_uget(v_as_1747_, v_i_1749_);
v_ref_1761_ = lean_ctor_get(v_a_1760_, 0);
v_msg_1762_ = lean_ctor_get(v_a_1760_, 1);
v_isSharedCheck_1791_ = !lean_is_exclusive(v_a_1760_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1764_ = v_a_1760_;
v_isShared_1765_ = v_isSharedCheck_1791_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_msg_1762_);
lean_inc(v_ref_1761_);
lean_dec(v_a_1760_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1791_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1766_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v_ref_1783_; lean_object* v___y_1785_; lean_object* v___x_1788_; 
v___x_1766_ = lean_box(0);
v_ref_1783_ = l_Lean_replaceRef(v_ref_1761_, v_ref_1759_);
lean_dec(v_ref_1761_);
v___x_1788_ = l_Lean_Syntax_getPos_x3f(v_ref_1783_, v___x_1746_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v___x_1789_; 
v___x_1789_ = lean_unsigned_to_nat(0u);
v___y_1785_ = v___x_1789_;
goto v___jp_1784_;
}
else
{
lean_object* v_val_1790_; 
v_val_1790_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_val_1790_);
lean_dec_ref_known(v___x_1788_, 1);
v___y_1785_ = v_val_1790_;
goto v___jp_1784_;
}
v___jp_1767_:
{
lean_object* v___x_1771_; 
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 1, v___y_1769_);
lean_ctor_set(v___x_1757_, 0, v___y_1768_);
v___x_1771_ = v___x_1757_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___y_1768_);
lean_ctor_set(v_reuseFailAlloc_1782_, 1, v___y_1769_);
v___x_1771_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v_pos2traces_1775_; lean_object* v___x_1777_; 
v___x_1772_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1773_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1755_, v___x_1771_, v___x_1772_);
v___x_1774_ = lean_array_push(v___x_1773_, v_msg_1762_);
v_pos2traces_1775_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1755_, v___x_1771_, v___x_1774_);
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 1, v_pos2traces_1775_);
lean_ctor_set(v___x_1764_, 0, v___x_1766_);
v___x_1777_ = v___x_1764_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1766_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v_pos2traces_1775_);
v___x_1777_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
size_t v___x_1778_; size_t v___x_1779_; 
v___x_1778_ = ((size_t)1ULL);
v___x_1779_ = lean_usize_add(v_i_1749_, v___x_1778_);
v_i_1749_ = v___x_1779_;
v_b_1750_ = v___x_1777_;
goto _start;
}
}
}
v___jp_1784_:
{
lean_object* v___x_1786_; 
v___x_1786_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1783_, v___x_1746_);
lean_dec(v_ref_1783_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_inc(v___y_1785_);
v___y_1768_ = v___y_1785_;
v___y_1769_ = v___y_1785_;
goto v___jp_1767_;
}
else
{
lean_object* v_val_1787_; 
v_val_1787_ = lean_ctor_get(v___x_1786_, 0);
lean_inc(v_val_1787_);
lean_dec_ref_known(v___x_1786_, 1);
v___y_1768_ = v___y_1785_;
v___y_1769_ = v_val_1787_;
goto v___jp_1767_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg___boxed(lean_object* v___x_1794_, lean_object* v_as_1795_, lean_object* v_sz_1796_, lean_object* v_i_1797_, lean_object* v_b_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
uint8_t v___x_37026__boxed_1801_; size_t v_sz_boxed_1802_; size_t v_i_boxed_1803_; lean_object* v_res_1804_; 
v___x_37026__boxed_1801_ = lean_unbox(v___x_1794_);
v_sz_boxed_1802_ = lean_unbox_usize(v_sz_1796_);
lean_dec(v_sz_1796_);
v_i_boxed_1803_ = lean_unbox_usize(v_i_1797_);
lean_dec(v_i_1797_);
v_res_1804_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_37026__boxed_1801_, v_as_1795_, v_sz_boxed_1802_, v_i_boxed_1803_, v_b_1798_, v___y_1799_);
lean_dec_ref(v___y_1799_);
lean_dec_ref(v_as_1795_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(uint8_t v___x_1805_, lean_object* v_as_1806_, size_t v_sz_1807_, size_t v_i_1808_, lean_object* v_b_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
uint8_t v___x_1813_; 
v___x_1813_ = lean_usize_dec_lt(v_i_1808_, v_sz_1807_);
if (v___x_1813_ == 0)
{
lean_object* v___x_1814_; 
v___x_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1814_, 0, v_b_1809_);
return v___x_1814_;
}
else
{
lean_object* v_snd_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1852_; 
v_snd_1815_ = lean_ctor_get(v_b_1809_, 1);
v_isSharedCheck_1852_ = !lean_is_exclusive(v_b_1809_);
if (v_isSharedCheck_1852_ == 0)
{
lean_object* v_unused_1853_; 
v_unused_1853_ = lean_ctor_get(v_b_1809_, 0);
lean_dec(v_unused_1853_);
v___x_1817_ = v_b_1809_;
v_isShared_1818_ = v_isSharedCheck_1852_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_snd_1815_);
lean_dec(v_b_1809_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1852_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v_ref_1819_; lean_object* v_a_1820_; lean_object* v_ref_1821_; lean_object* v_msg_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1851_; 
v_ref_1819_ = lean_ctor_get(v___y_1810_, 5);
v_a_1820_ = lean_array_uget(v_as_1806_, v_i_1808_);
v_ref_1821_ = lean_ctor_get(v_a_1820_, 0);
v_msg_1822_ = lean_ctor_get(v_a_1820_, 1);
v_isSharedCheck_1851_ = !lean_is_exclusive(v_a_1820_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1824_ = v_a_1820_;
v_isShared_1825_ = v_isSharedCheck_1851_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_msg_1822_);
lean_inc(v_ref_1821_);
lean_dec(v_a_1820_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1851_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1826_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v_ref_1843_; lean_object* v___y_1845_; lean_object* v___x_1848_; 
v___x_1826_ = lean_box(0);
v_ref_1843_ = l_Lean_replaceRef(v_ref_1821_, v_ref_1819_);
lean_dec(v_ref_1821_);
v___x_1848_ = l_Lean_Syntax_getPos_x3f(v_ref_1843_, v___x_1805_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v___x_1849_; 
v___x_1849_ = lean_unsigned_to_nat(0u);
v___y_1845_ = v___x_1849_;
goto v___jp_1844_;
}
else
{
lean_object* v_val_1850_; 
v_val_1850_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_val_1850_);
lean_dec_ref_known(v___x_1848_, 1);
v___y_1845_ = v_val_1850_;
goto v___jp_1844_;
}
v___jp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 1, v___y_1829_);
lean_ctor_set(v___x_1817_, 0, v___y_1828_);
v___x_1831_ = v___x_1817_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___y_1828_);
lean_ctor_set(v_reuseFailAlloc_1842_, 1, v___y_1829_);
v___x_1831_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v_pos2traces_1835_; lean_object* v___x_1837_; 
v___x_1832_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1833_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1815_, v___x_1831_, v___x_1832_);
v___x_1834_ = lean_array_push(v___x_1833_, v_msg_1822_);
v_pos2traces_1835_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1815_, v___x_1831_, v___x_1834_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 1, v_pos2traces_1835_);
lean_ctor_set(v___x_1824_, 0, v___x_1826_);
v___x_1837_ = v___x_1824_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1826_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v_pos2traces_1835_);
v___x_1837_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
size_t v___x_1838_; size_t v___x_1839_; lean_object* v___x_1840_; 
v___x_1838_ = ((size_t)1ULL);
v___x_1839_ = lean_usize_add(v_i_1808_, v___x_1838_);
v___x_1840_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_1805_, v_as_1806_, v_sz_1807_, v___x_1839_, v___x_1837_, v___y_1810_);
return v___x_1840_;
}
}
}
v___jp_1844_:
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1843_, v___x_1805_);
lean_dec(v_ref_1843_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_inc(v___y_1845_);
v___y_1828_ = v___y_1845_;
v___y_1829_ = v___y_1845_;
goto v___jp_1827_;
}
else
{
lean_object* v_val_1847_; 
v_val_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_val_1847_);
lean_dec_ref_known(v___x_1846_, 1);
v___y_1828_ = v___y_1845_;
v___y_1829_ = v_val_1847_;
goto v___jp_1827_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28___boxed(lean_object* v___x_1854_, lean_object* v_as_1855_, lean_object* v_sz_1856_, lean_object* v_i_1857_, lean_object* v_b_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
uint8_t v___x_37106__boxed_1862_; size_t v_sz_boxed_1863_; size_t v_i_boxed_1864_; lean_object* v_res_1865_; 
v___x_37106__boxed_1862_ = lean_unbox(v___x_1854_);
v_sz_boxed_1863_ = lean_unbox_usize(v_sz_1856_);
lean_dec(v_sz_1856_);
v_i_boxed_1864_ = lean_unbox_usize(v_i_1857_);
lean_dec(v_i_1857_);
v_res_1865_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(v___x_37106__boxed_1862_, v_as_1855_, v_sz_boxed_1863_, v_i_boxed_1864_, v_b_1858_, v___y_1859_, v___y_1860_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec_ref(v_as_1855_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(uint8_t v___x_1866_, lean_object* v_t_1867_, lean_object* v_init_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v_root_1872_; lean_object* v_tail_1873_; lean_object* v___x_1874_; 
v_root_1872_ = lean_ctor_get(v_t_1867_, 0);
v_tail_1873_ = lean_ctor_get(v_t_1867_, 1);
lean_inc_ref(v_init_1868_);
v___x_1874_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1868_, v___x_1866_, v_root_1872_, v_init_1868_, v___y_1869_, v___y_1870_);
lean_dec_ref(v_init_1868_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1911_; 
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1877_ = v___x_1874_;
v_isShared_1878_ = v_isSharedCheck_1911_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1874_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1911_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
if (lean_obj_tag(v_a_1875_) == 0)
{
lean_object* v_a_1879_; lean_object* v___x_1881_; 
v_a_1879_ = lean_ctor_get(v_a_1875_, 0);
lean_inc(v_a_1879_);
lean_dec_ref_known(v_a_1875_, 1);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v_a_1879_);
v___x_1881_ = v___x_1877_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_a_1879_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
else
{
lean_object* v_a_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; size_t v_sz_1886_; size_t v___x_1887_; lean_object* v___x_1888_; 
lean_del_object(v___x_1877_);
v_a_1883_ = lean_ctor_get(v_a_1875_, 0);
lean_inc(v_a_1883_);
lean_dec_ref_known(v_a_1875_, 1);
v___x_1884_ = lean_box(0);
v___x_1885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1884_);
lean_ctor_set(v___x_1885_, 1, v_a_1883_);
v_sz_1886_ = lean_array_size(v_tail_1873_);
v___x_1887_ = ((size_t)0ULL);
v___x_1888_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(v___x_1866_, v_tail_1873_, v_sz_1886_, v___x_1887_, v___x_1885_, v___y_1869_, v___y_1870_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1902_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1891_ = v___x_1888_;
v_isShared_1892_ = v_isSharedCheck_1902_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1888_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1902_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v_fst_1893_; 
v_fst_1893_ = lean_ctor_get(v_a_1889_, 0);
if (lean_obj_tag(v_fst_1893_) == 0)
{
lean_object* v_snd_1894_; lean_object* v___x_1896_; 
v_snd_1894_ = lean_ctor_get(v_a_1889_, 1);
lean_inc(v_snd_1894_);
lean_dec(v_a_1889_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 0, v_snd_1894_);
v___x_1896_ = v___x_1891_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_snd_1894_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
else
{
lean_object* v_val_1898_; lean_object* v___x_1900_; 
lean_inc_ref(v_fst_1893_);
lean_dec(v_a_1889_);
v_val_1898_ = lean_ctor_get(v_fst_1893_, 0);
lean_inc(v_val_1898_);
lean_dec_ref_known(v_fst_1893_, 1);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 0, v_val_1898_);
v___x_1900_ = v___x_1891_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_val_1898_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
else
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1910_; 
v_a_1903_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1905_ = v___x_1888_;
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1888_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1906_ == 0)
{
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
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
}
}
else
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1919_; 
v_a_1912_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1914_ = v___x_1874_;
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1874_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
if (v_isShared_1915_ == 0)
{
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19___boxed(lean_object* v___x_1920_, lean_object* v_t_1921_, lean_object* v_init_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
uint8_t v___x_37187__boxed_1926_; lean_object* v_res_1927_; 
v___x_37187__boxed_1926_ = lean_unbox(v___x_1920_);
v_res_1927_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(v___x_37187__boxed_1926_, v_t_1921_, v_init_1922_, v___y_1923_, v___y_1924_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
lean_dec_ref(v_t_1921_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(lean_object* v_x_1928_, lean_object* v_x_1929_){
_start:
{
if (lean_obj_tag(v_x_1929_) == 0)
{
return v_x_1928_;
}
else
{
lean_object* v_key_1930_; lean_object* v_value_1931_; lean_object* v_tail_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v_key_1930_ = lean_ctor_get(v_x_1929_, 0);
v_value_1931_ = lean_ctor_get(v_x_1929_, 1);
v_tail_1932_ = lean_ctor_get(v_x_1929_, 2);
lean_inc(v_value_1931_);
lean_inc(v_key_1930_);
v___x_1933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1933_, 0, v_key_1930_);
lean_ctor_set(v___x_1933_, 1, v_value_1931_);
v___x_1934_ = lean_array_push(v_x_1928_, v___x_1933_);
v_x_1928_ = v___x_1934_;
v_x_1929_ = v_tail_1932_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22___boxed(lean_object* v_x_1936_, lean_object* v_x_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(v_x_1936_, v_x_1937_);
lean_dec(v_x_1937_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(lean_object* v_as_1939_, size_t v_i_1940_, size_t v_stop_1941_, lean_object* v_b_1942_){
_start:
{
uint8_t v___x_1943_; 
v___x_1943_ = lean_usize_dec_eq(v_i_1940_, v_stop_1941_);
if (v___x_1943_ == 0)
{
lean_object* v___x_1944_; lean_object* v___x_1945_; size_t v___x_1946_; size_t v___x_1947_; 
v___x_1944_ = lean_array_uget_borrowed(v_as_1939_, v_i_1940_);
v___x_1945_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(v_b_1942_, v___x_1944_);
v___x_1946_ = ((size_t)1ULL);
v___x_1947_ = lean_usize_add(v_i_1940_, v___x_1946_);
v_i_1940_ = v___x_1947_;
v_b_1942_ = v___x_1945_;
goto _start;
}
else
{
return v_b_1942_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23___boxed(lean_object* v_as_1949_, lean_object* v_i_1950_, lean_object* v_stop_1951_, lean_object* v_b_1952_){
_start:
{
size_t v_i_boxed_1953_; size_t v_stop_boxed_1954_; lean_object* v_res_1955_; 
v_i_boxed_1953_ = lean_unbox_usize(v_i_1950_);
lean_dec(v_i_1950_);
v_stop_boxed_1954_ = lean_unbox_usize(v_stop_1951_);
lean_dec(v_stop_1951_);
v_res_1955_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_as_1949_, v_i_boxed_1953_, v_stop_boxed_1954_, v_b_1952_);
lean_dec_ref(v_as_1949_);
return v_res_1955_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0(void){
_start:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1956_ = lean_unsigned_to_nat(32u);
v___x_1957_ = lean_mk_empty_array_with_capacity(v___x_1956_);
v___x_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1957_);
return v___x_1958_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1(void){
_start:
{
size_t v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1959_ = ((size_t)5ULL);
v___x_1960_ = lean_unsigned_to_nat(0u);
v___x_1961_ = lean_unsigned_to_nat(32u);
v___x_1962_ = lean_mk_empty_array_with_capacity(v___x_1961_);
v___x_1963_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0);
v___x_1964_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1964_, 0, v___x_1963_);
lean_ctor_set(v___x_1964_, 1, v___x_1962_);
lean_ctor_set(v___x_1964_, 2, v___x_1960_);
lean_ctor_set(v___x_1964_, 3, v___x_1960_);
lean_ctor_set_usize(v___x_1964_, 4, v___x_1959_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(lean_object* v___y_1965_){
_start:
{
lean_object* v___x_1967_; lean_object* v_traceState_1968_; lean_object* v_traces_1969_; lean_object* v___x_1970_; lean_object* v_traceState_1971_; lean_object* v_env_1972_; lean_object* v_nextMacroScope_1973_; lean_object* v_ngen_1974_; lean_object* v_auxDeclNGen_1975_; lean_object* v_cache_1976_; lean_object* v_messages_1977_; lean_object* v_infoState_1978_; lean_object* v_snapshotTasks_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1998_; 
v___x_1967_ = lean_st_ref_get(v___y_1965_);
v_traceState_1968_ = lean_ctor_get(v___x_1967_, 4);
lean_inc_ref(v_traceState_1968_);
lean_dec(v___x_1967_);
v_traces_1969_ = lean_ctor_get(v_traceState_1968_, 0);
lean_inc_ref(v_traces_1969_);
lean_dec_ref(v_traceState_1968_);
v___x_1970_ = lean_st_ref_take(v___y_1965_);
v_traceState_1971_ = lean_ctor_get(v___x_1970_, 4);
v_env_1972_ = lean_ctor_get(v___x_1970_, 0);
v_nextMacroScope_1973_ = lean_ctor_get(v___x_1970_, 1);
v_ngen_1974_ = lean_ctor_get(v___x_1970_, 2);
v_auxDeclNGen_1975_ = lean_ctor_get(v___x_1970_, 3);
v_cache_1976_ = lean_ctor_get(v___x_1970_, 5);
v_messages_1977_ = lean_ctor_get(v___x_1970_, 6);
v_infoState_1978_ = lean_ctor_get(v___x_1970_, 7);
v_snapshotTasks_1979_ = lean_ctor_get(v___x_1970_, 8);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1981_ = v___x_1970_;
v_isShared_1982_ = v_isSharedCheck_1998_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_snapshotTasks_1979_);
lean_inc(v_infoState_1978_);
lean_inc(v_messages_1977_);
lean_inc(v_cache_1976_);
lean_inc(v_traceState_1971_);
lean_inc(v_auxDeclNGen_1975_);
lean_inc(v_ngen_1974_);
lean_inc(v_nextMacroScope_1973_);
lean_inc(v_env_1972_);
lean_dec(v___x_1970_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1998_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
uint64_t v_tid_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1996_; 
v_tid_1983_ = lean_ctor_get_uint64(v_traceState_1971_, sizeof(void*)*1);
v_isSharedCheck_1996_ = !lean_is_exclusive(v_traceState_1971_);
if (v_isSharedCheck_1996_ == 0)
{
lean_object* v_unused_1997_; 
v_unused_1997_ = lean_ctor_get(v_traceState_1971_, 0);
lean_dec(v_unused_1997_);
v___x_1985_ = v_traceState_1971_;
v_isShared_1986_ = v_isSharedCheck_1996_;
goto v_resetjp_1984_;
}
else
{
lean_dec(v_traceState_1971_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1996_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1987_; lean_object* v___x_1989_; 
v___x_1987_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 0, v___x_1987_);
v___x_1989_ = v___x_1985_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v___x_1987_);
lean_ctor_set_uint64(v_reuseFailAlloc_1995_, sizeof(void*)*1, v_tid_1983_);
v___x_1989_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
lean_object* v___x_1991_; 
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 4, v___x_1989_);
v___x_1991_ = v___x_1981_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_env_1972_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_nextMacroScope_1973_);
lean_ctor_set(v_reuseFailAlloc_1994_, 2, v_ngen_1974_);
lean_ctor_set(v_reuseFailAlloc_1994_, 3, v_auxDeclNGen_1975_);
lean_ctor_set(v_reuseFailAlloc_1994_, 4, v___x_1989_);
lean_ctor_set(v_reuseFailAlloc_1994_, 5, v_cache_1976_);
lean_ctor_set(v_reuseFailAlloc_1994_, 6, v_messages_1977_);
lean_ctor_set(v_reuseFailAlloc_1994_, 7, v_infoState_1978_);
lean_ctor_set(v_reuseFailAlloc_1994_, 8, v_snapshotTasks_1979_);
v___x_1991_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1992_ = lean_st_ref_put(v___y_1965_, v___x_1991_);
v___x_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1993_, 0, v_traces_1969_);
return v___x_1993_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___boxed(lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_1999_);
lean_dec(v___y_1999_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(lean_object* v_hi_2002_, lean_object* v_pivot_2003_, lean_object* v_as_2004_, lean_object* v_i_2005_, lean_object* v_k_2006_){
_start:
{
uint8_t v___x_2007_; 
v___x_2007_ = lean_nat_dec_lt(v_k_2006_, v_hi_2002_);
if (v___x_2007_ == 0)
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
lean_dec(v_k_2006_);
v___x_2008_ = lean_array_fswap(v_as_2004_, v_i_2005_, v_hi_2002_);
v___x_2009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2009_, 0, v_i_2005_);
lean_ctor_set(v___x_2009_, 1, v___x_2008_);
return v___x_2009_;
}
else
{
lean_object* v___x_2010_; lean_object* v_fst_2011_; lean_object* v_fst_2012_; lean_object* v_fst_2013_; lean_object* v_fst_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; uint8_t v___x_2017_; 
v___x_2010_ = lean_array_fget_borrowed(v_as_2004_, v_k_2006_);
v_fst_2011_ = lean_ctor_get(v___x_2010_, 0);
v_fst_2012_ = lean_ctor_get(v_pivot_2003_, 0);
v_fst_2013_ = lean_ctor_get(v_fst_2011_, 0);
v_fst_2014_ = lean_ctor_get(v_fst_2012_, 0);
v___x_2015_ = lean_unsigned_to_nat(1u);
v___x_2016_ = lean_nat_add(v_fst_2013_, v___x_2015_);
v___x_2017_ = lean_nat_dec_le(v___x_2016_, v_fst_2014_);
lean_dec(v___x_2016_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; 
v___x_2018_ = lean_nat_add(v_k_2006_, v___x_2015_);
lean_dec(v_k_2006_);
v_k_2006_ = v___x_2018_;
goto _start;
}
else
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2020_ = lean_array_fswap(v_as_2004_, v_i_2005_, v_k_2006_);
v___x_2021_ = lean_nat_add(v_i_2005_, v___x_2015_);
lean_dec(v_i_2005_);
v___x_2022_ = lean_nat_add(v_k_2006_, v___x_2015_);
lean_dec(v_k_2006_);
v_as_2004_ = v___x_2020_;
v_i_2005_ = v___x_2021_;
v_k_2006_ = v___x_2022_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg___boxed(lean_object* v_hi_2024_, lean_object* v_pivot_2025_, lean_object* v_as_2026_, lean_object* v_i_2027_, lean_object* v_k_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_2024_, v_pivot_2025_, v_as_2026_, v_i_2027_, v_k_2028_);
lean_dec_ref(v_pivot_2025_);
lean_dec(v_hi_2024_);
return v_res_2029_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(lean_object* v_x_2030_, lean_object* v_x_2031_){
_start:
{
lean_object* v_fst_2032_; lean_object* v_fst_2033_; lean_object* v_fst_2034_; lean_object* v_fst_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; uint8_t v___x_2038_; 
v_fst_2032_ = lean_ctor_get(v_x_2030_, 0);
v_fst_2033_ = lean_ctor_get(v_x_2031_, 0);
v_fst_2034_ = lean_ctor_get(v_fst_2032_, 0);
v_fst_2035_ = lean_ctor_get(v_fst_2033_, 0);
v___x_2036_ = lean_unsigned_to_nat(1u);
v___x_2037_ = lean_nat_add(v_fst_2034_, v___x_2036_);
v___x_2038_ = lean_nat_dec_le(v___x_2037_, v_fst_2035_);
lean_dec(v___x_2037_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0___boxed(lean_object* v_x_2039_, lean_object* v_x_2040_){
_start:
{
uint8_t v_res_2041_; lean_object* v_r_2042_; 
v_res_2041_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v_x_2039_, v_x_2040_);
lean_dec_ref(v_x_2040_);
lean_dec_ref(v_x_2039_);
v_r_2042_ = lean_box(v_res_2041_);
return v_r_2042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(lean_object* v_n_2043_, lean_object* v_as_2044_, lean_object* v_lo_2045_, lean_object* v_hi_2046_){
_start:
{
lean_object* v___y_2048_; uint8_t v___x_2058_; 
v___x_2058_ = lean_nat_dec_lt(v_lo_2045_, v_hi_2046_);
if (v___x_2058_ == 0)
{
lean_dec(v_lo_2045_);
return v_as_2044_;
}
else
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v_mid_2061_; lean_object* v___y_2063_; lean_object* v___y_2069_; lean_object* v___x_2074_; lean_object* v___x_2075_; uint8_t v___x_2076_; 
v___x_2059_ = lean_nat_add(v_lo_2045_, v_hi_2046_);
v___x_2060_ = lean_unsigned_to_nat(1u);
v_mid_2061_ = lean_nat_shiftr(v___x_2059_, v___x_2060_);
lean_dec(v___x_2059_);
v___x_2074_ = lean_array_fget_borrowed(v_as_2044_, v_mid_2061_);
v___x_2075_ = lean_array_fget_borrowed(v_as_2044_, v_lo_2045_);
v___x_2076_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2074_, v___x_2075_);
if (v___x_2076_ == 0)
{
v___y_2069_ = v_as_2044_;
goto v___jp_2068_;
}
else
{
lean_object* v___x_2077_; 
v___x_2077_ = lean_array_fswap(v_as_2044_, v_lo_2045_, v_mid_2061_);
v___y_2069_ = v___x_2077_;
goto v___jp_2068_;
}
v___jp_2062_:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; uint8_t v___x_2066_; 
v___x_2064_ = lean_array_fget_borrowed(v___y_2063_, v_mid_2061_);
v___x_2065_ = lean_array_fget_borrowed(v___y_2063_, v_hi_2046_);
v___x_2066_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2064_, v___x_2065_);
if (v___x_2066_ == 0)
{
lean_dec(v_mid_2061_);
v___y_2048_ = v___y_2063_;
goto v___jp_2047_;
}
else
{
lean_object* v___x_2067_; 
v___x_2067_ = lean_array_fswap(v___y_2063_, v_mid_2061_, v_hi_2046_);
lean_dec(v_mid_2061_);
v___y_2048_ = v___x_2067_;
goto v___jp_2047_;
}
}
v___jp_2068_:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; 
v___x_2070_ = lean_array_fget_borrowed(v___y_2069_, v_hi_2046_);
v___x_2071_ = lean_array_fget_borrowed(v___y_2069_, v_lo_2045_);
v___x_2072_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2070_, v___x_2071_);
if (v___x_2072_ == 0)
{
v___y_2063_ = v___y_2069_;
goto v___jp_2062_;
}
else
{
lean_object* v___x_2073_; 
v___x_2073_ = lean_array_fswap(v___y_2069_, v_lo_2045_, v_hi_2046_);
v___y_2063_ = v___x_2073_;
goto v___jp_2062_;
}
}
}
v___jp_2047_:
{
lean_object* v_pivot_2049_; lean_object* v___x_2050_; lean_object* v_fst_2051_; lean_object* v_snd_2052_; uint8_t v___x_2053_; 
v_pivot_2049_ = lean_array_fget(v___y_2048_, v_hi_2046_);
lean_inc_n(v_lo_2045_, 2);
v___x_2050_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_2046_, v_pivot_2049_, v___y_2048_, v_lo_2045_, v_lo_2045_);
lean_dec(v_pivot_2049_);
v_fst_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_fst_2051_);
v_snd_2052_ = lean_ctor_get(v___x_2050_, 1);
lean_inc(v_snd_2052_);
lean_dec_ref(v___x_2050_);
v___x_2053_ = lean_nat_dec_le(v_hi_2046_, v_fst_2051_);
if (v___x_2053_ == 0)
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2054_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_2043_, v_snd_2052_, v_lo_2045_, v_fst_2051_);
v___x_2055_ = lean_unsigned_to_nat(1u);
v___x_2056_ = lean_nat_add(v_fst_2051_, v___x_2055_);
lean_dec(v_fst_2051_);
v_as_2044_ = v___x_2054_;
v_lo_2045_ = v___x_2056_;
goto _start;
}
else
{
lean_dec(v_fst_2051_);
lean_dec(v_lo_2045_);
return v_snd_2052_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___boxed(lean_object* v_n_2078_, lean_object* v_as_2079_, lean_object* v_lo_2080_, lean_object* v_hi_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_2078_, v_as_2079_, v_lo_2080_, v_hi_2081_);
lean_dec(v_hi_2081_);
lean_dec(v_n_2078_);
return v_res_2082_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0(void){
_start:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2083_ = lean_box(0);
v___x_2084_ = lean_unsigned_to_nat(16u);
v___x_2085_ = lean_mk_array(v___x_2084_, v___x_2083_);
return v___x_2085_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1(void){
_start:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v_pos2traces_2088_; 
v___x_2086_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0, &l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0);
v___x_2087_ = lean_unsigned_to_nat(0u);
v_pos2traces_2088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos2traces_2088_, 0, v___x_2087_);
lean_ctor_set(v_pos2traces_2088_, 1, v___x_2086_);
return v_pos2traces_2088_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10(lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
lean_object* v_options_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v_options_2095_ = lean_ctor_get(v___y_2089_, 2);
v___x_2096_ = l_Lean_trace_profiler_output;
v___x_2097_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(v_options_2095_, v___x_2096_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v___x_2098_; uint8_t v___x_2099_; 
v___x_2098_ = l_Lean_trace_profiler_serve;
v___x_2099_ = l_Lean_Option_get___at___00main_spec__8(v_options_2095_, v___x_2098_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2100_; lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2163_; 
v___x_2100_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_2090_);
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2103_ = v___x_2100_;
v_isShared_2104_ = v_isSharedCheck_2163_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v___x_2100_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2163_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
uint8_t v___x_2105_; 
v___x_2105_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_2101_);
if (v___x_2105_ == 0)
{
lean_object* v___x_2106_; lean_object* v_pos2traces_2107_; lean_object* v___x_2108_; 
lean_del_object(v___x_2103_);
v___x_2106_ = lean_unsigned_to_nat(0u);
v_pos2traces_2107_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1, &l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1);
v___x_2108_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(v___x_2105_, v_a_2101_, v_pos2traces_2107_, v___y_2089_, v___y_2090_);
lean_dec(v_a_2101_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; lean_object* v___y_2111_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v___y_2127_; lean_object* v___y_2128_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2137_; lean_object* v_size_2143_; lean_object* v_buckets_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; uint8_t v___x_2147_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2109_);
lean_dec_ref_known(v___x_2108_, 1);
v_size_2143_ = lean_ctor_get(v_a_2109_, 0);
lean_inc(v_size_2143_);
v_buckets_2144_ = lean_ctor_get(v_a_2109_, 1);
lean_inc_ref(v_buckets_2144_);
lean_dec(v_a_2109_);
v___x_2145_ = lean_mk_empty_array_with_capacity(v_size_2143_);
lean_dec(v_size_2143_);
v___x_2146_ = lean_array_get_size(v_buckets_2144_);
v___x_2147_ = lean_nat_dec_lt(v___x_2106_, v___x_2146_);
if (v___x_2147_ == 0)
{
lean_dec_ref(v_buckets_2144_);
v___y_2137_ = v___x_2145_;
goto v___jp_2136_;
}
else
{
size_t v___x_2148_; size_t v___x_2149_; lean_object* v___x_2150_; 
v___x_2148_ = ((size_t)0ULL);
v___x_2149_ = lean_usize_of_nat(v___x_2146_);
v___x_2150_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_buckets_2144_, v___x_2148_, v___x_2149_, v___x_2145_);
lean_dec_ref(v_buckets_2144_);
v___y_2137_ = v___x_2150_;
goto v___jp_2136_;
}
v___jp_2110_:
{
lean_object* v___x_2112_; size_t v_sz_2113_; size_t v___x_2114_; lean_object* v___x_2115_; 
v___x_2112_ = lean_box(0);
v_sz_2113_ = lean_array_size(v___y_2111_);
v___x_2114_ = ((size_t)0ULL);
v___x_2115_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(v___x_2099_, v___y_2111_, v_sz_2113_, v___x_2114_, v___x_2112_, v___y_2089_, v___y_2090_);
lean_dec_ref(v___y_2111_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2122_; 
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2122_ == 0)
{
lean_object* v_unused_2123_; 
v_unused_2123_ = lean_ctor_get(v___x_2115_, 0);
lean_dec(v_unused_2123_);
v___x_2117_ = v___x_2115_;
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
else
{
lean_dec(v___x_2115_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2120_; 
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 0, v___x_2112_);
v___x_2120_ = v___x_2117_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v___x_2112_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
else
{
return v___x_2115_;
}
}
v___jp_2124_:
{
lean_object* v___x_2129_; 
v___x_2129_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v___y_2125_, v___y_2127_, v___y_2126_, v___y_2128_);
lean_dec(v___y_2128_);
lean_dec(v___y_2125_);
v___y_2111_ = v___x_2129_;
goto v___jp_2110_;
}
v___jp_2130_:
{
uint8_t v___x_2135_; 
v___x_2135_ = lean_nat_dec_le(v___y_2134_, v___y_2131_);
if (v___x_2135_ == 0)
{
lean_dec(v___y_2131_);
lean_inc(v___y_2134_);
v___y_2125_ = v___y_2132_;
v___y_2126_ = v___y_2134_;
v___y_2127_ = v___y_2133_;
v___y_2128_ = v___y_2134_;
goto v___jp_2124_;
}
else
{
v___y_2125_ = v___y_2132_;
v___y_2126_ = v___y_2134_;
v___y_2127_ = v___y_2133_;
v___y_2128_ = v___y_2131_;
goto v___jp_2124_;
}
}
v___jp_2136_:
{
lean_object* v___x_2138_; uint8_t v___x_2139_; 
v___x_2138_ = lean_array_get_size(v___y_2137_);
v___x_2139_ = lean_nat_dec_eq(v___x_2138_, v___x_2106_);
if (v___x_2139_ == 0)
{
lean_object* v___x_2140_; lean_object* v___x_2141_; uint8_t v___x_2142_; 
v___x_2140_ = lean_unsigned_to_nat(1u);
v___x_2141_ = lean_nat_sub(v___x_2138_, v___x_2140_);
v___x_2142_ = lean_nat_dec_le(v___x_2106_, v___x_2141_);
if (v___x_2142_ == 0)
{
lean_inc(v___x_2141_);
v___y_2131_ = v___x_2141_;
v___y_2132_ = v___x_2138_;
v___y_2133_ = v___y_2137_;
v___y_2134_ = v___x_2141_;
goto v___jp_2130_;
}
else
{
v___y_2131_ = v___x_2141_;
v___y_2132_ = v___x_2138_;
v___y_2133_ = v___y_2137_;
v___y_2134_ = v___x_2106_;
goto v___jp_2130_;
}
}
else
{
v___y_2111_ = v___y_2137_;
goto v___jp_2110_;
}
}
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
v_a_2151_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2108_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2108_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
else
{
lean_object* v___x_2159_; lean_object* v___x_2161_; 
lean_dec(v_a_2101_);
v___x_2159_ = lean_box(0);
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 0, v___x_2159_);
v___x_2161_ = v___x_2103_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2159_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
else
{
goto v___jp_2092_;
}
}
else
{
lean_dec_ref_known(v___x_2097_, 1);
goto v___jp_2092_;
}
v___jp_2092_:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2093_ = lean_box(0);
v___x_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2093_);
return v___x_2094_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10___boxed(lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2164_, v___y_2165_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(lean_object* v_as_2168_, size_t v_sz_2169_, size_t v_i_2170_, lean_object* v_b_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
uint8_t v___x_2175_; 
v___x_2175_ = lean_usize_dec_lt(v_i_2170_, v_sz_2169_);
if (v___x_2175_ == 0)
{
lean_object* v___x_2176_; 
v___x_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2176_, 0, v_b_2171_);
return v___x_2176_;
}
else
{
lean_object* v_options_2177_; lean_object* v_a_2178_; lean_object* v___x_2179_; 
v_options_2177_ = lean_ctor_get(v___y_2172_, 2);
v_a_2178_ = lean_array_uget_borrowed(v_as_2168_, v_i_2170_);
lean_inc_ref(v_options_2177_);
lean_inc(v_a_2178_);
v___x_2179_ = l_Lean_Compiler_LCNF_resumeCompilation(v_a_2178_, v_options_2177_, v___y_2172_, v___y_2173_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v___x_2180_; 
lean_dec_ref_known(v___x_2179_, 1);
v___x_2180_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2172_, v___y_2173_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v___x_2181_; size_t v___x_2182_; size_t v___x_2183_; 
lean_dec_ref_known(v___x_2180_, 1);
v___x_2181_ = lean_box(0);
v___x_2182_ = ((size_t)1ULL);
v___x_2183_ = lean_usize_add(v_i_2170_, v___x_2182_);
v_i_2170_ = v___x_2183_;
v_b_2171_ = v___x_2181_;
goto _start;
}
else
{
return v___x_2180_;
}
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2186_; 
v_a_2185_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_a_2185_);
lean_dec_ref_known(v___x_2179_, 1);
v___x_2186_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2172_, v___y_2173_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2193_ == 0)
{
lean_object* v_unused_2194_; 
v_unused_2194_ = lean_ctor_get(v___x_2186_, 0);
lean_dec(v_unused_2194_);
v___x_2188_ = v___x_2186_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_dec(v___x_2186_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
lean_ctor_set_tag(v___x_2188_, 1);
lean_ctor_set(v___x_2188_, 0, v_a_2185_);
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2185_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
else
{
lean_dec(v_a_2185_);
return v___x_2186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11___boxed(lean_object* v_as_2195_, lean_object* v_sz_2196_, lean_object* v_i_2197_, lean_object* v_b_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
size_t v_sz_boxed_2202_; size_t v_i_boxed_2203_; lean_object* v_res_2204_; 
v_sz_boxed_2202_ = lean_unbox_usize(v_sz_2196_);
lean_dec(v_sz_2196_);
v_i_boxed_2203_ = lean_unbox_usize(v_i_2197_);
lean_dec(v_i_2197_);
v_res_2204_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(v_as_2195_, v_sz_boxed_2202_, v_i_boxed_2203_, v_b_2198_, v___y_2199_, v___y_2200_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
lean_dec_ref(v_as_2195_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(lean_object* v_as_2205_, size_t v_sz_2206_, size_t v_i_2207_, lean_object* v_b_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
uint8_t v___x_2212_; 
v___x_2212_ = lean_usize_dec_lt(v_i_2207_, v_sz_2206_);
if (v___x_2212_ == 0)
{
lean_object* v___x_2213_; 
v___x_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2213_, 0, v_b_2208_);
return v___x_2213_;
}
else
{
lean_object* v_a_2214_; lean_object* v_declNames_2215_; lean_object* v___x_2216_; size_t v_sz_2217_; size_t v___x_2218_; lean_object* v___x_2219_; 
v_a_2214_ = lean_array_uget_borrowed(v_as_2205_, v_i_2207_);
v_declNames_2215_ = lean_ctor_get(v_a_2214_, 0);
v___x_2216_ = lean_box(0);
v_sz_2217_ = lean_array_size(v_declNames_2215_);
v___x_2218_ = ((size_t)0ULL);
v___x_2219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(v_declNames_2215_, v_sz_2217_, v___x_2218_, v___x_2216_, v___y_2209_, v___y_2210_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v___x_2220_; 
lean_dec_ref_known(v___x_2219_, 1);
v___x_2220_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v___y_2210_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; lean_object* v_unreported_2222_; lean_object* v___x_2223_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc(v_a_2221_);
lean_dec_ref_known(v___x_2220_, 1);
v_unreported_2222_ = lean_ctor_get(v_a_2221_, 1);
lean_inc_ref(v_unreported_2222_);
lean_dec(v_a_2221_);
v___x_2223_ = l_Lean_PersistentArray_forIn___at___00main_spec__12(v_unreported_2222_, v___x_2216_, v___y_2209_, v___y_2210_);
lean_dec_ref(v_unreported_2222_);
if (lean_obj_tag(v___x_2223_) == 0)
{
size_t v___x_2224_; size_t v___x_2225_; 
lean_dec_ref_known(v___x_2223_, 1);
v___x_2224_ = ((size_t)1ULL);
v___x_2225_ = lean_usize_add(v_i_2207_, v___x_2224_);
v_i_2207_ = v___x_2225_;
v_b_2208_ = v___x_2216_;
goto _start;
}
else
{
return v___x_2223_;
}
}
else
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
v_a_2227_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v___x_2220_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2220_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2230_ == 0)
{
v___x_2232_ = v___x_2229_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_a_2227_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
else
{
return v___x_2219_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13___boxed(lean_object* v_as_2235_, lean_object* v_sz_2236_, lean_object* v_i_2237_, lean_object* v_b_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
size_t v_sz_boxed_2242_; size_t v_i_boxed_2243_; lean_object* v_res_2244_; 
v_sz_boxed_2242_ = lean_unbox_usize(v_sz_2236_);
lean_dec(v_sz_2236_);
v_i_boxed_2243_ = lean_unbox_usize(v_i_2237_);
lean_dec(v_i_2237_);
v_res_2244_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(v_as_2235_, v_sz_boxed_2242_, v_i_boxed_2243_, v_b_2238_, v___y_2239_, v___y_2240_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec_ref(v_as_2235_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(lean_object* v_as_2245_, size_t v_i_2246_, size_t v_stop_2247_, lean_object* v_b_2248_){
_start:
{
uint8_t v___x_2249_; 
v___x_2249_ = lean_usize_dec_eq(v_i_2246_, v_stop_2247_);
if (v___x_2249_ == 0)
{
lean_object* v___x_2250_; lean_object* v_name_2251_; lean_object* v___x_2252_; size_t v___x_2253_; size_t v___x_2254_; 
v___x_2250_ = lean_array_uget_borrowed(v_as_2245_, v_i_2246_);
v_name_2251_ = lean_ctor_get(v___x_2250_, 0);
lean_inc(v_name_2251_);
v___x_2252_ = l_Lean_Compiler_LCNF_setDeclPublic(v_b_2248_, v_name_2251_);
v___x_2253_ = ((size_t)1ULL);
v___x_2254_ = lean_usize_add(v_i_2246_, v___x_2253_);
v_i_2246_ = v___x_2254_;
v_b_2248_ = v___x_2252_;
goto _start;
}
else
{
return v_b_2248_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___boxed(lean_object* v_as_2256_, lean_object* v_i_2257_, lean_object* v_stop_2258_, lean_object* v_b_2259_){
_start:
{
size_t v_i_boxed_2260_; size_t v_stop_boxed_2261_; lean_object* v_res_2262_; 
v_i_boxed_2260_ = lean_unbox_usize(v_i_2257_);
lean_dec(v_i_2257_);
v_stop_boxed_2261_ = lean_unbox_usize(v_stop_2258_);
lean_dec(v_stop_2258_);
v_res_2262_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v_as_2256_, v_i_boxed_2260_, v_stop_boxed_2261_, v_b_2259_);
lean_dec_ref(v_as_2256_);
return v_res_2262_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0(uint8_t v_suppressElabErrors_2263_, uint8_t v___y_2264_, lean_object* v_x_2265_){
_start:
{
if (lean_obj_tag(v_x_2265_) == 1)
{
lean_object* v_pre_2266_; 
v_pre_2266_ = lean_ctor_get(v_x_2265_, 0);
switch(lean_obj_tag(v_pre_2266_))
{
case 1:
{
lean_object* v_pre_2267_; 
v_pre_2267_ = lean_ctor_get(v_pre_2266_, 0);
switch(lean_obj_tag(v_pre_2267_))
{
case 0:
{
lean_object* v_str_2268_; lean_object* v_str_2269_; lean_object* v___x_2270_; uint8_t v___x_2271_; 
v_str_2268_ = lean_ctor_get(v_x_2265_, 1);
v_str_2269_ = lean_ctor_get(v_pre_2266_, 1);
v___x_2270_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0));
v___x_2271_ = lean_string_dec_eq(v_str_2269_, v___x_2270_);
if (v___x_2271_ == 0)
{
lean_object* v___x_2272_; uint8_t v___x_2273_; 
v___x_2272_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1));
v___x_2273_ = lean_string_dec_eq(v_str_2269_, v___x_2272_);
if (v___x_2273_ == 0)
{
return v___x_2273_;
}
else
{
lean_object* v___x_2274_; uint8_t v___x_2275_; 
v___x_2274_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2));
v___x_2275_ = lean_string_dec_eq(v_str_2268_, v___x_2274_);
if (v___x_2275_ == 0)
{
return v___x_2275_;
}
else
{
return v_suppressElabErrors_2263_;
}
}
}
else
{
lean_object* v___x_2276_; uint8_t v___x_2277_; 
v___x_2276_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3));
v___x_2277_ = lean_string_dec_eq(v_str_2268_, v___x_2276_);
if (v___x_2277_ == 0)
{
return v___x_2277_;
}
else
{
return v_suppressElabErrors_2263_;
}
}
}
case 1:
{
lean_object* v_pre_2278_; 
v_pre_2278_ = lean_ctor_get(v_pre_2267_, 0);
if (lean_obj_tag(v_pre_2278_) == 0)
{
lean_object* v_str_2279_; lean_object* v_str_2280_; lean_object* v_str_2281_; lean_object* v___x_2282_; uint8_t v___x_2283_; 
v_str_2279_ = lean_ctor_get(v_x_2265_, 1);
v_str_2280_ = lean_ctor_get(v_pre_2266_, 1);
v_str_2281_ = lean_ctor_get(v_pre_2267_, 1);
v___x_2282_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4));
v___x_2283_ = lean_string_dec_eq(v_str_2281_, v___x_2282_);
if (v___x_2283_ == 0)
{
return v___x_2283_;
}
else
{
lean_object* v___x_2284_; uint8_t v___x_2285_; 
v___x_2284_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5));
v___x_2285_ = lean_string_dec_eq(v_str_2280_, v___x_2284_);
if (v___x_2285_ == 0)
{
return v___x_2285_;
}
else
{
lean_object* v___x_2286_; uint8_t v___x_2287_; 
v___x_2286_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6));
v___x_2287_ = lean_string_dec_eq(v_str_2279_, v___x_2286_);
if (v___x_2287_ == 0)
{
return v___x_2287_;
}
else
{
return v_suppressElabErrors_2263_;
}
}
}
}
else
{
return v___y_2264_;
}
}
default: 
{
return v___y_2264_;
}
}
}
case 0:
{
lean_object* v_str_2288_; lean_object* v___x_2289_; uint8_t v___x_2290_; 
v_str_2288_ = lean_ctor_get(v_x_2265_, 1);
v___x_2289_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_2290_ = lean_string_dec_eq(v_str_2288_, v___x_2289_);
if (v___x_2290_ == 0)
{
return v___x_2290_;
}
else
{
return v_suppressElabErrors_2263_;
}
}
default: 
{
return v___y_2264_;
}
}
}
else
{
return v___y_2264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0___boxed(lean_object* v_suppressElabErrors_2291_, lean_object* v___y_2292_, lean_object* v_x_2293_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2294_; uint8_t v___y_37787__boxed_2295_; uint8_t v_res_2296_; lean_object* v_r_2297_; 
v_suppressElabErrors_boxed_2294_ = lean_unbox(v_suppressElabErrors_2291_);
v___y_37787__boxed_2295_ = lean_unbox(v___y_2292_);
v_res_2296_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0(v_suppressElabErrors_boxed_2294_, v___y_37787__boxed_2295_, v_x_2293_);
lean_dec(v_x_2293_);
v_r_2297_ = lean_box(v_res_2296_);
return v_r_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(lean_object* v_ref_2298_, lean_object* v_msgData_2299_, uint8_t v_severity_2300_, uint8_t v_isSilent_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
uint8_t v___y_2306_; lean_object* v___y_2307_; lean_object* v___y_2308_; lean_object* v___y_2309_; lean_object* v___y_2310_; uint8_t v___y_2311_; lean_object* v___y_2312_; lean_object* v___y_2313_; lean_object* v___y_2314_; lean_object* v___y_2342_; uint8_t v___y_2343_; lean_object* v___y_2344_; uint8_t v___y_2345_; lean_object* v___y_2346_; uint8_t v___y_2347_; lean_object* v___y_2348_; lean_object* v___y_2349_; lean_object* v___y_2367_; uint8_t v___y_2368_; lean_object* v___y_2369_; uint8_t v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; uint8_t v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2378_; uint8_t v___y_2379_; lean_object* v___y_2380_; uint8_t v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; uint8_t v___y_2384_; uint8_t v___x_2389_; lean_object* v___y_2391_; uint8_t v___y_2392_; lean_object* v___y_2393_; lean_object* v___y_2394_; lean_object* v___y_2395_; uint8_t v___y_2396_; uint8_t v___y_2397_; uint8_t v___y_2399_; uint8_t v___x_2414_; 
v___x_2389_ = 2;
v___x_2414_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2300_, v___x_2389_);
if (v___x_2414_ == 0)
{
v___y_2399_ = v___x_2414_;
goto v___jp_2398_;
}
else
{
uint8_t v___x_2415_; 
lean_inc_ref(v_msgData_2299_);
v___x_2415_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2299_);
v___y_2399_ = v___x_2415_;
goto v___jp_2398_;
}
v___jp_2305_:
{
lean_object* v___x_2315_; lean_object* v_currNamespace_2316_; lean_object* v_openDecls_2317_; lean_object* v_env_2318_; lean_object* v_nextMacroScope_2319_; lean_object* v_ngen_2320_; lean_object* v_auxDeclNGen_2321_; lean_object* v_traceState_2322_; lean_object* v_cache_2323_; lean_object* v_messages_2324_; lean_object* v_infoState_2325_; lean_object* v_snapshotTasks_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2340_; 
v___x_2315_ = lean_st_ref_take(v___y_2314_);
v_currNamespace_2316_ = lean_ctor_get(v___y_2313_, 6);
v_openDecls_2317_ = lean_ctor_get(v___y_2313_, 7);
v_env_2318_ = lean_ctor_get(v___x_2315_, 0);
v_nextMacroScope_2319_ = lean_ctor_get(v___x_2315_, 1);
v_ngen_2320_ = lean_ctor_get(v___x_2315_, 2);
v_auxDeclNGen_2321_ = lean_ctor_get(v___x_2315_, 3);
v_traceState_2322_ = lean_ctor_get(v___x_2315_, 4);
v_cache_2323_ = lean_ctor_get(v___x_2315_, 5);
v_messages_2324_ = lean_ctor_get(v___x_2315_, 6);
v_infoState_2325_ = lean_ctor_get(v___x_2315_, 7);
v_snapshotTasks_2326_ = lean_ctor_get(v___x_2315_, 8);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2328_ = v___x_2315_;
v_isShared_2329_ = v_isSharedCheck_2340_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_snapshotTasks_2326_);
lean_inc(v_infoState_2325_);
lean_inc(v_messages_2324_);
lean_inc(v_cache_2323_);
lean_inc(v_traceState_2322_);
lean_inc(v_auxDeclNGen_2321_);
lean_inc(v_ngen_2320_);
lean_inc(v_nextMacroScope_2319_);
lean_inc(v_env_2318_);
lean_dec(v___x_2315_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2340_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2335_; 
lean_inc(v_openDecls_2317_);
lean_inc(v_currNamespace_2316_);
v___x_2330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2330_, 0, v_currNamespace_2316_);
lean_ctor_set(v___x_2330_, 1, v_openDecls_2317_);
v___x_2331_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2330_);
lean_ctor_set(v___x_2331_, 1, v___y_2308_);
lean_inc_ref(v___y_2310_);
lean_inc_ref(v___y_2307_);
v___x_2332_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2332_, 0, v___y_2307_);
lean_ctor_set(v___x_2332_, 1, v___y_2309_);
lean_ctor_set(v___x_2332_, 2, v___y_2312_);
lean_ctor_set(v___x_2332_, 3, v___y_2310_);
lean_ctor_set(v___x_2332_, 4, v___x_2331_);
lean_ctor_set_uint8(v___x_2332_, sizeof(void*)*5, v___y_2306_);
lean_ctor_set_uint8(v___x_2332_, sizeof(void*)*5 + 1, v___y_2311_);
lean_ctor_set_uint8(v___x_2332_, sizeof(void*)*5 + 2, v_isSilent_2301_);
v___x_2333_ = l_Lean_MessageLog_add(v___x_2332_, v_messages_2324_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 6, v___x_2333_);
v___x_2335_ = v___x_2328_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_env_2318_);
lean_ctor_set(v_reuseFailAlloc_2339_, 1, v_nextMacroScope_2319_);
lean_ctor_set(v_reuseFailAlloc_2339_, 2, v_ngen_2320_);
lean_ctor_set(v_reuseFailAlloc_2339_, 3, v_auxDeclNGen_2321_);
lean_ctor_set(v_reuseFailAlloc_2339_, 4, v_traceState_2322_);
lean_ctor_set(v_reuseFailAlloc_2339_, 5, v_cache_2323_);
lean_ctor_set(v_reuseFailAlloc_2339_, 6, v___x_2333_);
lean_ctor_set(v_reuseFailAlloc_2339_, 7, v_infoState_2325_);
lean_ctor_set(v_reuseFailAlloc_2339_, 8, v_snapshotTasks_2326_);
v___x_2335_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2336_ = lean_st_ref_put(v___y_2314_, v___x_2335_);
v___x_2337_ = lean_box(0);
v___x_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2337_);
return v___x_2338_;
}
}
}
v___jp_2341_:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2365_; 
v___x_2350_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2299_);
v___x_2351_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(v___x_2350_, v___y_2302_, v___y_2303_);
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2354_ = v___x_2351_;
v_isShared_2355_ = v_isSharedCheck_2365_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2351_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2365_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
lean_inc_ref_n(v___y_2346_, 2);
v___x_2356_ = l_Lean_FileMap_toPosition(v___y_2346_, v___y_2348_);
lean_dec(v___y_2348_);
v___x_2357_ = l_Lean_FileMap_toPosition(v___y_2346_, v___y_2349_);
lean_dec(v___y_2349_);
v___x_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2357_);
v___x_2359_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1));
if (v___y_2345_ == 0)
{
lean_del_object(v___x_2354_);
lean_dec_ref(v___y_2342_);
v___y_2306_ = v___y_2343_;
v___y_2307_ = v___y_2344_;
v___y_2308_ = v_a_2352_;
v___y_2309_ = v___x_2356_;
v___y_2310_ = v___x_2359_;
v___y_2311_ = v___y_2347_;
v___y_2312_ = v___x_2358_;
v___y_2313_ = v___y_2302_;
v___y_2314_ = v___y_2303_;
goto v___jp_2305_;
}
else
{
uint8_t v___x_2360_; 
lean_inc(v_a_2352_);
v___x_2360_ = l_Lean_MessageData_hasTag(v___y_2342_, v_a_2352_);
if (v___x_2360_ == 0)
{
lean_object* v___x_2361_; lean_object* v___x_2363_; 
lean_dec_ref_known(v___x_2358_, 1);
lean_dec_ref(v___x_2356_);
lean_dec(v_a_2352_);
v___x_2361_ = lean_box(0);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 0, v___x_2361_);
v___x_2363_ = v___x_2354_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2361_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
else
{
lean_del_object(v___x_2354_);
v___y_2306_ = v___y_2343_;
v___y_2307_ = v___y_2344_;
v___y_2308_ = v_a_2352_;
v___y_2309_ = v___x_2356_;
v___y_2310_ = v___x_2359_;
v___y_2311_ = v___y_2347_;
v___y_2312_ = v___x_2358_;
v___y_2313_ = v___y_2302_;
v___y_2314_ = v___y_2303_;
goto v___jp_2305_;
}
}
}
}
v___jp_2366_:
{
lean_object* v___x_2375_; 
v___x_2375_ = l_Lean_Syntax_getTailPos_x3f(v___y_2372_, v___y_2368_);
lean_dec(v___y_2372_);
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_inc(v___y_2374_);
v___y_2342_ = v___y_2367_;
v___y_2343_ = v___y_2368_;
v___y_2344_ = v___y_2369_;
v___y_2345_ = v___y_2370_;
v___y_2346_ = v___y_2371_;
v___y_2347_ = v___y_2373_;
v___y_2348_ = v___y_2374_;
v___y_2349_ = v___y_2374_;
goto v___jp_2341_;
}
else
{
lean_object* v_val_2376_; 
v_val_2376_ = lean_ctor_get(v___x_2375_, 0);
lean_inc(v_val_2376_);
lean_dec_ref_known(v___x_2375_, 1);
v___y_2342_ = v___y_2367_;
v___y_2343_ = v___y_2368_;
v___y_2344_ = v___y_2369_;
v___y_2345_ = v___y_2370_;
v___y_2346_ = v___y_2371_;
v___y_2347_ = v___y_2373_;
v___y_2348_ = v___y_2374_;
v___y_2349_ = v_val_2376_;
goto v___jp_2341_;
}
}
v___jp_2377_:
{
lean_object* v_ref_2385_; lean_object* v___x_2386_; 
v_ref_2385_ = l_Lean_replaceRef(v_ref_2298_, v___y_2383_);
v___x_2386_ = l_Lean_Syntax_getPos_x3f(v_ref_2385_, v___y_2379_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v___x_2387_; 
v___x_2387_ = lean_unsigned_to_nat(0u);
v___y_2367_ = v___y_2378_;
v___y_2368_ = v___y_2379_;
v___y_2369_ = v___y_2380_;
v___y_2370_ = v___y_2381_;
v___y_2371_ = v___y_2382_;
v___y_2372_ = v_ref_2385_;
v___y_2373_ = v___y_2384_;
v___y_2374_ = v___x_2387_;
goto v___jp_2366_;
}
else
{
lean_object* v_val_2388_; 
v_val_2388_ = lean_ctor_get(v___x_2386_, 0);
lean_inc(v_val_2388_);
lean_dec_ref_known(v___x_2386_, 1);
v___y_2367_ = v___y_2378_;
v___y_2368_ = v___y_2379_;
v___y_2369_ = v___y_2380_;
v___y_2370_ = v___y_2381_;
v___y_2371_ = v___y_2382_;
v___y_2372_ = v_ref_2385_;
v___y_2373_ = v___y_2384_;
v___y_2374_ = v_val_2388_;
goto v___jp_2366_;
}
}
v___jp_2390_:
{
if (v___y_2397_ == 0)
{
v___y_2378_ = v___y_2395_;
v___y_2379_ = v___y_2396_;
v___y_2380_ = v___y_2391_;
v___y_2381_ = v___y_2392_;
v___y_2382_ = v___y_2394_;
v___y_2383_ = v___y_2393_;
v___y_2384_ = v_severity_2300_;
goto v___jp_2377_;
}
else
{
v___y_2378_ = v___y_2395_;
v___y_2379_ = v___y_2396_;
v___y_2380_ = v___y_2391_;
v___y_2381_ = v___y_2392_;
v___y_2382_ = v___y_2394_;
v___y_2383_ = v___y_2393_;
v___y_2384_ = v___x_2389_;
goto v___jp_2377_;
}
}
v___jp_2398_:
{
if (v___y_2399_ == 0)
{
lean_object* v_fileName_2400_; lean_object* v_fileMap_2401_; lean_object* v_options_2402_; lean_object* v_ref_2403_; uint8_t v_suppressElabErrors_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___f_2407_; uint8_t v___x_2408_; uint8_t v___x_2409_; 
v_fileName_2400_ = lean_ctor_get(v___y_2302_, 0);
v_fileMap_2401_ = lean_ctor_get(v___y_2302_, 1);
v_options_2402_ = lean_ctor_get(v___y_2302_, 2);
v_ref_2403_ = lean_ctor_get(v___y_2302_, 5);
v_suppressElabErrors_2404_ = lean_ctor_get_uint8(v___y_2302_, sizeof(void*)*14 + 1);
v___x_2405_ = lean_box(v_suppressElabErrors_2404_);
v___x_2406_ = lean_box(v___y_2399_);
v___f_2407_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2407_, 0, v___x_2405_);
lean_closure_set(v___f_2407_, 1, v___x_2406_);
v___x_2408_ = 1;
v___x_2409_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2300_, v___x_2408_);
if (v___x_2409_ == 0)
{
v___y_2391_ = v_fileName_2400_;
v___y_2392_ = v_suppressElabErrors_2404_;
v___y_2393_ = v_ref_2403_;
v___y_2394_ = v_fileMap_2401_;
v___y_2395_ = v___f_2407_;
v___y_2396_ = v___y_2399_;
v___y_2397_ = v___x_2409_;
goto v___jp_2390_;
}
else
{
lean_object* v___x_2410_; uint8_t v___x_2411_; 
v___x_2410_ = l_Lean_warningAsError;
v___x_2411_ = l_Lean_Option_get___at___00main_spec__8(v_options_2402_, v___x_2410_);
v___y_2391_ = v_fileName_2400_;
v___y_2392_ = v_suppressElabErrors_2404_;
v___y_2393_ = v_ref_2403_;
v___y_2394_ = v_fileMap_2401_;
v___y_2395_ = v___f_2407_;
v___y_2396_ = v___y_2399_;
v___y_2397_ = v___x_2411_;
goto v___jp_2390_;
}
}
else
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
lean_dec_ref(v_msgData_2299_);
v___x_2412_ = lean_box(0);
v___x_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2412_);
return v___x_2413_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___boxed(lean_object* v_ref_2416_, lean_object* v_msgData_2417_, lean_object* v_severity_2418_, lean_object* v_isSilent_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
uint8_t v_severity_boxed_2423_; uint8_t v_isSilent_boxed_2424_; lean_object* v_res_2425_; 
v_severity_boxed_2423_ = lean_unbox(v_severity_2418_);
v_isSilent_boxed_2424_ = lean_unbox(v_isSilent_2419_);
v_res_2425_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(v_ref_2416_, v_msgData_2417_, v_severity_boxed_2423_, v_isSilent_boxed_2424_, v___y_2420_, v___y_2421_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v_ref_2416_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(lean_object* v_msgData_2426_, uint8_t v_severity_2427_, uint8_t v_isSilent_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
lean_object* v_ref_2432_; lean_object* v___x_2433_; 
v_ref_2432_ = lean_ctor_get(v___y_2429_, 5);
v___x_2433_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(v_ref_2432_, v_msgData_2426_, v_severity_2427_, v_isSilent_2428_, v___y_2429_, v___y_2430_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30___boxed(lean_object* v_msgData_2434_, lean_object* v_severity_2435_, lean_object* v_isSilent_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
uint8_t v_severity_boxed_2440_; uint8_t v_isSilent_boxed_2441_; lean_object* v_res_2442_; 
v_severity_boxed_2440_ = lean_unbox(v_severity_2435_);
v_isSilent_boxed_2441_ = lean_unbox(v_isSilent_2436_);
v_res_2442_ = l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(v_msgData_2434_, v_severity_boxed_2440_, v_isSilent_boxed_2441_, v___y_2437_, v___y_2438_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__14(lean_object* v_msgData_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
uint8_t v___x_2447_; uint8_t v___x_2448_; lean_object* v___x_2449_; 
v___x_2447_ = 2;
v___x_2448_ = 0;
v___x_2449_ = l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(v_msgData_2443_, v___x_2447_, v___x_2448_, v___y_2444_, v___y_2445_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__14___boxed(lean_object* v_msgData_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_Lean_logError___at___00main_spec__14(v_msgData_2450_, v___y_2451_, v___y_2452_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(lean_object* v_x2_2455_, lean_object* v_as_2456_, size_t v_i_2457_, size_t v_stop_2458_, lean_object* v_b_2459_){
_start:
{
uint8_t v___x_2460_; 
v___x_2460_ = lean_usize_dec_eq(v_i_2457_, v_stop_2458_);
if (v___x_2460_ == 0)
{
lean_object* v___x_2461_; lean_object* v___x_2462_; size_t v___x_2463_; size_t v___x_2464_; 
v___x_2461_ = lean_array_uget_borrowed(v_as_2456_, v_i_2457_);
lean_inc_ref(v_x2_2455_);
lean_inc(v___x_2461_);
v___x_2462_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2461_, v_x2_2455_, v_b_2459_);
v___x_2463_ = ((size_t)1ULL);
v___x_2464_ = lean_usize_add(v_i_2457_, v___x_2463_);
v_i_2457_ = v___x_2464_;
v_b_2459_ = v___x_2462_;
goto _start;
}
else
{
lean_dec_ref(v_x2_2455_);
return v_b_2459_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2___boxed(lean_object* v_x2_2466_, lean_object* v_as_2467_, lean_object* v_i_2468_, lean_object* v_stop_2469_, lean_object* v_b_2470_){
_start:
{
size_t v_i_boxed_2471_; size_t v_stop_boxed_2472_; lean_object* v_res_2473_; 
v_i_boxed_2471_ = lean_unbox_usize(v_i_2468_);
lean_dec(v_i_2468_);
v_stop_boxed_2472_ = lean_unbox_usize(v_stop_2469_);
lean_dec(v_stop_2469_);
v_res_2473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v_x2_2466_, v_as_2467_, v_i_boxed_2471_, v_stop_boxed_2472_, v_b_2470_);
lean_dec_ref(v_as_2467_);
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(lean_object* v_as_2474_, size_t v_i_2475_, size_t v_stop_2476_, lean_object* v_b_2477_){
_start:
{
lean_object* v___y_2479_; uint8_t v___x_2483_; 
v___x_2483_ = lean_usize_dec_eq(v_i_2475_, v_stop_2476_);
if (v___x_2483_ == 0)
{
lean_object* v___x_2484_; lean_object* v_declNames_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; uint8_t v___x_2488_; 
v___x_2484_ = lean_array_uget_borrowed(v_as_2474_, v_i_2475_);
v_declNames_2485_ = lean_ctor_get(v___x_2484_, 0);
v___x_2486_ = lean_unsigned_to_nat(0u);
v___x_2487_ = lean_array_get_size(v_declNames_2485_);
v___x_2488_ = lean_nat_dec_lt(v___x_2486_, v___x_2487_);
if (v___x_2488_ == 0)
{
v___y_2479_ = v_b_2477_;
goto v___jp_2478_;
}
else
{
uint8_t v___x_2489_; 
v___x_2489_ = lean_nat_dec_le(v___x_2487_, v___x_2487_);
if (v___x_2489_ == 0)
{
if (v___x_2488_ == 0)
{
v___y_2479_ = v_b_2477_;
goto v___jp_2478_;
}
else
{
size_t v___x_2490_; size_t v___x_2491_; lean_object* v___x_2492_; 
v___x_2490_ = ((size_t)0ULL);
v___x_2491_ = lean_usize_of_nat(v___x_2487_);
lean_inc(v___x_2484_);
v___x_2492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_2484_, v_declNames_2485_, v___x_2490_, v___x_2491_, v_b_2477_);
v___y_2479_ = v___x_2492_;
goto v___jp_2478_;
}
}
else
{
size_t v___x_2493_; size_t v___x_2494_; lean_object* v___x_2495_; 
v___x_2493_ = ((size_t)0ULL);
v___x_2494_ = lean_usize_of_nat(v___x_2487_);
lean_inc(v___x_2484_);
v___x_2495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_2484_, v_declNames_2485_, v___x_2493_, v___x_2494_, v_b_2477_);
v___y_2479_ = v___x_2495_;
goto v___jp_2478_;
}
}
}
else
{
return v_b_2477_;
}
v___jp_2478_:
{
size_t v___x_2480_; size_t v___x_2481_; 
v___x_2480_ = ((size_t)1ULL);
v___x_2481_ = lean_usize_add(v_i_2475_, v___x_2480_);
v_i_2475_ = v___x_2481_;
v_b_2477_ = v___y_2479_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___boxed(lean_object* v_as_2496_, lean_object* v_i_2497_, lean_object* v_stop_2498_, lean_object* v_b_2499_){
_start:
{
size_t v_i_boxed_2500_; size_t v_stop_boxed_2501_; lean_object* v_res_2502_; 
v_i_boxed_2500_ = lean_unbox_usize(v_i_2497_);
lean_dec(v_i_2497_);
v_stop_boxed_2501_ = lean_unbox_usize(v_stop_2498_);
lean_dec(v_stop_2498_);
v_res_2502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v_as_2496_, v_i_boxed_2500_, v_stop_boxed_2501_, v_b_2499_);
lean_dec_ref(v_as_2496_);
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(lean_object* v_a_2503_, lean_object* v_as_2504_, size_t v_i_2505_, size_t v_stop_2506_, lean_object* v_b_2507_){
_start:
{
lean_object* v___y_2509_; uint8_t v___x_2513_; 
v___x_2513_ = lean_usize_dec_eq(v_i_2505_, v_stop_2506_);
if (v___x_2513_ == 0)
{
lean_object* v___x_2514_; lean_object* v_name_2515_; uint8_t v___x_2516_; 
v___x_2514_ = lean_array_uget_borrowed(v_as_2504_, v_i_2505_);
v_name_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_name_2515_);
lean_inc_ref(v_a_2503_);
v___x_2516_ = l_Lean_isExtern(v_a_2503_, v_name_2515_);
if (v___x_2516_ == 0)
{
v___y_2509_ = v_b_2507_;
goto v___jp_2508_;
}
else
{
lean_object* v___x_2517_; 
lean_inc(v___x_2514_);
v___x_2517_ = lean_array_push(v_b_2507_, v___x_2514_);
v___y_2509_ = v___x_2517_;
goto v___jp_2508_;
}
}
else
{
lean_dec_ref(v_a_2503_);
return v_b_2507_;
}
v___jp_2508_:
{
size_t v___x_2510_; size_t v___x_2511_; 
v___x_2510_ = ((size_t)1ULL);
v___x_2511_ = lean_usize_add(v_i_2505_, v___x_2510_);
v_i_2505_ = v___x_2511_;
v_b_2507_ = v___y_2509_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19___boxed(lean_object* v_a_2518_, lean_object* v_as_2519_, lean_object* v_i_2520_, lean_object* v_stop_2521_, lean_object* v_b_2522_){
_start:
{
size_t v_i_boxed_2523_; size_t v_stop_boxed_2524_; lean_object* v_res_2525_; 
v_i_boxed_2523_ = lean_unbox_usize(v_i_2520_);
lean_dec(v_i_2520_);
v_stop_boxed_2524_ = lean_unbox_usize(v_stop_2521_);
lean_dec(v_stop_2521_);
v_res_2525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_2518_, v_as_2519_, v_i_boxed_2523_, v_stop_boxed_2524_, v_b_2522_);
lean_dec_ref(v_as_2519_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(lean_object* v_as_2526_, size_t v_sz_2527_, size_t v_i_2528_, lean_object* v_b_2529_){
_start:
{
uint8_t v___x_2531_; 
v___x_2531_ = lean_usize_dec_lt(v_i_2528_, v_sz_2527_);
if (v___x_2531_ == 0)
{
lean_object* v___x_2532_; 
v___x_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2532_, 0, v_b_2529_);
return v___x_2532_;
}
else
{
uint8_t v___x_2533_; lean_object* v_a_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
lean_dec_ref(v_b_2529_);
v___x_2533_ = 0;
v_a_2534_ = lean_array_uget_borrowed(v_as_2526_, v_i_2528_);
lean_inc(v_a_2534_);
v___x_2535_ = l_Lean_Message_toString(v_a_2534_, v___x_2533_);
v___x_2536_ = l_IO_eprintln___at___00main_spec__6(v___x_2535_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v___x_2537_; size_t v___x_2538_; size_t v___x_2539_; 
lean_dec_ref_known(v___x_2536_, 1);
v___x_2537_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_2538_ = ((size_t)1ULL);
v___x_2539_ = lean_usize_add(v_i_2528_, v___x_2538_);
v_i_2528_ = v___x_2539_;
v_b_2529_ = v___x_2537_;
goto _start;
}
else
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
v_a_2541_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v___x_2536_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___x_2536_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2544_ == 0)
{
v___x_2546_ = v___x_2543_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2541_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27___boxed(lean_object* v_as_2549_, lean_object* v_sz_2550_, lean_object* v_i_2551_, lean_object* v_b_2552_, lean_object* v___y_2553_){
_start:
{
size_t v_sz_boxed_2554_; size_t v_i_boxed_2555_; lean_object* v_res_2556_; 
v_sz_boxed_2554_ = lean_unbox_usize(v_sz_2550_);
lean_dec(v_sz_2550_);
v_i_boxed_2555_ = lean_unbox_usize(v_i_2551_);
lean_dec(v_i_2551_);
v_res_2556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(v_as_2549_, v_sz_boxed_2554_, v_i_boxed_2555_, v_b_2552_);
lean_dec_ref(v_as_2549_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(lean_object* v_as_2557_, size_t v_sz_2558_, size_t v_i_2559_, lean_object* v_b_2560_){
_start:
{
uint8_t v___x_2562_; 
v___x_2562_ = lean_usize_dec_lt(v_i_2559_, v_sz_2558_);
if (v___x_2562_ == 0)
{
lean_object* v___x_2563_; 
v___x_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2563_, 0, v_b_2560_);
return v___x_2563_;
}
else
{
uint8_t v___x_2564_; lean_object* v_a_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
lean_dec_ref(v_b_2560_);
v___x_2564_ = 0;
v_a_2565_ = lean_array_uget_borrowed(v_as_2557_, v_i_2559_);
lean_inc(v_a_2565_);
v___x_2566_ = l_Lean_Message_toString(v_a_2565_, v___x_2564_);
v___x_2567_ = l_IO_eprintln___at___00main_spec__6(v___x_2566_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v___x_2568_; size_t v___x_2569_; size_t v___x_2570_; lean_object* v___x_2571_; 
lean_dec_ref_known(v___x_2567_, 1);
v___x_2568_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_2569_ = ((size_t)1ULL);
v___x_2570_ = lean_usize_add(v_i_2559_, v___x_2569_);
v___x_2571_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(v_as_2557_, v_sz_2558_, v___x_2570_, v___x_2568_);
return v___x_2571_;
}
else
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2579_; 
v_a_2572_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2574_ = v___x_2567_;
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2567_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2577_; 
if (v_isShared_2575_ == 0)
{
v___x_2577_ = v___x_2574_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2572_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14___boxed(lean_object* v_as_2580_, lean_object* v_sz_2581_, lean_object* v_i_2582_, lean_object* v_b_2583_, lean_object* v___y_2584_){
_start:
{
size_t v_sz_boxed_2585_; size_t v_i_boxed_2586_; lean_object* v_res_2587_; 
v_sz_boxed_2585_ = lean_unbox_usize(v_sz_2581_);
lean_dec(v_sz_2581_);
v_i_boxed_2586_ = lean_unbox_usize(v_i_2582_);
lean_dec(v_i_2582_);
v_res_2587_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(v_as_2580_, v_sz_boxed_2585_, v_i_boxed_2586_, v_b_2583_);
lean_dec_ref(v_as_2580_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(lean_object* v_init_2588_, lean_object* v_n_2589_, lean_object* v_b_2590_){
_start:
{
if (lean_obj_tag(v_n_2589_) == 0)
{
lean_object* v_cs_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; size_t v_sz_2595_; size_t v___x_2596_; lean_object* v___x_2597_; 
v_cs_2592_ = lean_ctor_get(v_n_2589_, 0);
v___x_2593_ = lean_box(0);
v___x_2594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
lean_ctor_set(v___x_2594_, 1, v_b_2590_);
v_sz_2595_ = lean_array_size(v_cs_2592_);
v___x_2596_ = ((size_t)0ULL);
v___x_2597_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_init_2588_, v_cs_2592_, v_sz_2595_, v___x_2596_, v___x_2594_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2612_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2600_ = v___x_2597_;
v_isShared_2601_ = v_isSharedCheck_2612_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2597_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2612_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v_fst_2602_; 
v_fst_2602_ = lean_ctor_get(v_a_2598_, 0);
if (lean_obj_tag(v_fst_2602_) == 0)
{
lean_object* v_snd_2603_; lean_object* v___x_2604_; lean_object* v___x_2606_; 
v_snd_2603_ = lean_ctor_get(v_a_2598_, 1);
lean_inc(v_snd_2603_);
lean_dec(v_a_2598_);
v___x_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2604_, 0, v_snd_2603_);
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 0, v___x_2604_);
v___x_2606_ = v___x_2600_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v___x_2604_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
else
{
lean_object* v_val_2608_; lean_object* v___x_2610_; 
lean_inc_ref(v_fst_2602_);
lean_dec(v_a_2598_);
v_val_2608_ = lean_ctor_get(v_fst_2602_, 0);
lean_inc(v_val_2608_);
lean_dec_ref_known(v_fst_2602_, 1);
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 0, v_val_2608_);
v___x_2610_ = v___x_2600_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_val_2608_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
v_a_2613_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2597_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2597_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
else
{
lean_object* v_vs_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; size_t v_sz_2624_; size_t v___x_2625_; lean_object* v___x_2626_; 
v_vs_2621_ = lean_ctor_get(v_n_2589_, 0);
v___x_2622_ = lean_box(0);
v___x_2623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2622_);
lean_ctor_set(v___x_2623_, 1, v_b_2590_);
v_sz_2624_ = lean_array_size(v_vs_2621_);
v___x_2625_ = ((size_t)0ULL);
v___x_2626_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(v_vs_2621_, v_sz_2624_, v___x_2625_, v___x_2623_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2641_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2629_ = v___x_2626_;
v_isShared_2630_ = v_isSharedCheck_2641_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2626_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2641_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v_fst_2631_; 
v_fst_2631_ = lean_ctor_get(v_a_2627_, 0);
if (lean_obj_tag(v_fst_2631_) == 0)
{
lean_object* v_snd_2632_; lean_object* v___x_2633_; lean_object* v___x_2635_; 
v_snd_2632_ = lean_ctor_get(v_a_2627_, 1);
lean_inc(v_snd_2632_);
lean_dec(v_a_2627_);
v___x_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2633_, 0, v_snd_2632_);
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 0, v___x_2633_);
v___x_2635_ = v___x_2629_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2633_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
else
{
lean_object* v_val_2637_; lean_object* v___x_2639_; 
lean_inc_ref(v_fst_2631_);
lean_dec(v_a_2627_);
v_val_2637_ = lean_ctor_get(v_fst_2631_, 0);
lean_inc(v_val_2637_);
lean_dec_ref_known(v_fst_2631_, 1);
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 0, v_val_2637_);
v___x_2639_ = v___x_2629_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_val_2637_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
}
}
else
{
lean_object* v_a_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2649_; 
v_a_2642_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2644_ = v___x_2626_;
v_isShared_2645_ = v_isSharedCheck_2649_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_a_2642_);
lean_dec(v___x_2626_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2649_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v___x_2647_; 
if (v_isShared_2645_ == 0)
{
v___x_2647_ = v___x_2644_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_a_2642_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(lean_object* v_init_2650_, lean_object* v_as_2651_, size_t v_sz_2652_, size_t v_i_2653_, lean_object* v_b_2654_){
_start:
{
uint8_t v___x_2656_; 
v___x_2656_ = lean_usize_dec_lt(v_i_2653_, v_sz_2652_);
if (v___x_2656_ == 0)
{
lean_object* v___x_2657_; 
v___x_2657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2657_, 0, v_b_2654_);
return v___x_2657_;
}
else
{
lean_object* v_snd_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2692_; 
v_snd_2658_ = lean_ctor_get(v_b_2654_, 1);
v_isSharedCheck_2692_ = !lean_is_exclusive(v_b_2654_);
if (v_isSharedCheck_2692_ == 0)
{
lean_object* v_unused_2693_; 
v_unused_2693_ = lean_ctor_get(v_b_2654_, 0);
lean_dec(v_unused_2693_);
v___x_2660_ = v_b_2654_;
v_isShared_2661_ = v_isSharedCheck_2692_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_snd_2658_);
lean_dec(v_b_2654_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2692_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v_a_2662_; lean_object* v___x_2663_; 
v_a_2662_ = lean_array_uget_borrowed(v_as_2651_, v_i_2653_);
lean_inc(v_snd_2658_);
v___x_2663_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2650_, v_a_2662_, v_snd_2658_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v_a_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2683_; 
v_a_2664_ = lean_ctor_get(v___x_2663_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2666_ = v___x_2663_;
v_isShared_2667_ = v_isSharedCheck_2683_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_a_2664_);
lean_dec(v___x_2663_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2683_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
if (lean_obj_tag(v_a_2664_) == 0)
{
lean_object* v___x_2668_; lean_object* v___x_2670_; 
v___x_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2668_, 0, v_a_2664_);
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 0, v___x_2668_);
v___x_2670_ = v___x_2660_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2668_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v_snd_2658_);
v___x_2670_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
lean_object* v___x_2672_; 
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 0, v___x_2670_);
v___x_2672_ = v___x_2666_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___x_2670_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2676_; lean_object* v___x_2678_; 
lean_del_object(v___x_2666_);
lean_dec(v_snd_2658_);
v_a_2675_ = lean_ctor_get(v_a_2664_, 0);
lean_inc(v_a_2675_);
lean_dec_ref_known(v_a_2664_, 1);
v___x_2676_ = lean_box(0);
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 1, v_a_2675_);
lean_ctor_set(v___x_2660_, 0, v___x_2676_);
v___x_2678_ = v___x_2660_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v___x_2676_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v_a_2675_);
v___x_2678_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
size_t v___x_2679_; size_t v___x_2680_; 
v___x_2679_ = ((size_t)1ULL);
v___x_2680_ = lean_usize_add(v_i_2653_, v___x_2679_);
v_i_2653_ = v___x_2680_;
v_b_2654_ = v___x_2678_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
lean_del_object(v___x_2660_);
lean_dec(v_snd_2658_);
v_a_2684_ = lean_ctor_get(v___x_2663_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2663_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2663_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13___boxed(lean_object* v_init_2694_, lean_object* v_as_2695_, lean_object* v_sz_2696_, lean_object* v_i_2697_, lean_object* v_b_2698_, lean_object* v___y_2699_){
_start:
{
size_t v_sz_boxed_2700_; size_t v_i_boxed_2701_; lean_object* v_res_2702_; 
v_sz_boxed_2700_ = lean_unbox_usize(v_sz_2696_);
lean_dec(v_sz_2696_);
v_i_boxed_2701_ = lean_unbox_usize(v_i_2697_);
lean_dec(v_i_2697_);
v_res_2702_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_init_2694_, v_as_2695_, v_sz_boxed_2700_, v_i_boxed_2701_, v_b_2698_);
lean_dec_ref(v_as_2695_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10___boxed(lean_object* v_init_2703_, lean_object* v_n_2704_, lean_object* v_b_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2703_, v_n_2704_, v_b_2705_);
lean_dec_ref(v_n_2704_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(lean_object* v_as_2708_, size_t v_sz_2709_, size_t v_i_2710_, lean_object* v_b_2711_){
_start:
{
uint8_t v___x_2713_; 
v___x_2713_ = lean_usize_dec_lt(v_i_2710_, v_sz_2709_);
if (v___x_2713_ == 0)
{
lean_object* v___x_2714_; 
v___x_2714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2714_, 0, v_b_2711_);
return v___x_2714_;
}
else
{
uint8_t v___x_2715_; lean_object* v_a_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
lean_dec_ref(v_b_2711_);
v___x_2715_ = 0;
v_a_2716_ = lean_array_uget_borrowed(v_as_2708_, v_i_2710_);
lean_inc(v_a_2716_);
v___x_2717_ = l_Lean_Message_toString(v_a_2716_, v___x_2715_);
v___x_2718_ = l_IO_eprintln___at___00main_spec__6(v___x_2717_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_object* v___x_2719_; size_t v___x_2720_; size_t v___x_2721_; 
lean_dec_ref_known(v___x_2718_, 1);
v___x_2719_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_2720_ = ((size_t)1ULL);
v___x_2721_ = lean_usize_add(v_i_2710_, v___x_2720_);
v_i_2710_ = v___x_2721_;
v_b_2711_ = v___x_2719_;
goto _start;
}
else
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2730_; 
v_a_2723_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2725_ = v___x_2718_;
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2718_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2728_; 
if (v_isShared_2726_ == 0)
{
v___x_2728_ = v___x_2725_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_a_2723_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16___boxed(lean_object* v_as_2731_, lean_object* v_sz_2732_, lean_object* v_i_2733_, lean_object* v_b_2734_, lean_object* v___y_2735_){
_start:
{
size_t v_sz_boxed_2736_; size_t v_i_boxed_2737_; lean_object* v_res_2738_; 
v_sz_boxed_2736_ = lean_unbox_usize(v_sz_2732_);
lean_dec(v_sz_2732_);
v_i_boxed_2737_ = lean_unbox_usize(v_i_2733_);
lean_dec(v_i_2733_);
v_res_2738_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(v_as_2731_, v_sz_boxed_2736_, v_i_boxed_2737_, v_b_2734_);
lean_dec_ref(v_as_2731_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(lean_object* v_as_2739_, size_t v_sz_2740_, size_t v_i_2741_, lean_object* v_b_2742_){
_start:
{
uint8_t v___x_2744_; 
v___x_2744_ = lean_usize_dec_lt(v_i_2741_, v_sz_2740_);
if (v___x_2744_ == 0)
{
lean_object* v___x_2745_; 
v___x_2745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2745_, 0, v_b_2742_);
return v___x_2745_;
}
else
{
uint8_t v___x_2746_; lean_object* v_a_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
lean_dec_ref(v_b_2742_);
v___x_2746_ = 0;
v_a_2747_ = lean_array_uget_borrowed(v_as_2739_, v_i_2741_);
lean_inc(v_a_2747_);
v___x_2748_ = l_Lean_Message_toString(v_a_2747_, v___x_2746_);
v___x_2749_ = l_IO_eprintln___at___00main_spec__6(v___x_2748_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v___x_2750_; size_t v___x_2751_; size_t v___x_2752_; lean_object* v___x_2753_; 
lean_dec_ref_known(v___x_2749_, 1);
v___x_2750_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_2751_ = ((size_t)1ULL);
v___x_2752_ = lean_usize_add(v_i_2741_, v___x_2751_);
v___x_2753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(v_as_2739_, v_sz_2740_, v___x_2752_, v___x_2750_);
return v___x_2753_;
}
else
{
lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2761_; 
v_a_2754_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2756_ = v___x_2749_;
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_a_2754_);
lean_dec(v___x_2749_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2759_; 
if (v_isShared_2757_ == 0)
{
v___x_2759_ = v___x_2756_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_a_2754_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11___boxed(lean_object* v_as_2762_, lean_object* v_sz_2763_, lean_object* v_i_2764_, lean_object* v_b_2765_, lean_object* v___y_2766_){
_start:
{
size_t v_sz_boxed_2767_; size_t v_i_boxed_2768_; lean_object* v_res_2769_; 
v_sz_boxed_2767_ = lean_unbox_usize(v_sz_2763_);
lean_dec(v_sz_2763_);
v_i_boxed_2768_ = lean_unbox_usize(v_i_2764_);
lean_dec(v_i_2764_);
v_res_2769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_as_2762_, v_sz_boxed_2767_, v_i_boxed_2768_, v_b_2765_);
lean_dec_ref(v_as_2762_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7(lean_object* v_t_2770_, lean_object* v_init_2771_){
_start:
{
lean_object* v_root_2773_; lean_object* v_tail_2774_; lean_object* v___x_2775_; 
v_root_2773_ = lean_ctor_get(v_t_2770_, 0);
v_tail_2774_ = lean_ctor_get(v_t_2770_, 1);
v___x_2775_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2771_, v_root_2773_, v_init_2771_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2812_; 
v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2778_ = v___x_2775_;
v_isShared_2779_ = v_isSharedCheck_2812_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2775_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2812_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
if (lean_obj_tag(v_a_2776_) == 0)
{
lean_object* v_a_2780_; lean_object* v___x_2782_; 
v_a_2780_ = lean_ctor_get(v_a_2776_, 0);
lean_inc(v_a_2780_);
lean_dec_ref_known(v_a_2776_, 1);
if (v_isShared_2779_ == 0)
{
lean_ctor_set(v___x_2778_, 0, v_a_2780_);
v___x_2782_ = v___x_2778_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2780_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
else
{
lean_object* v_a_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; size_t v_sz_2787_; size_t v___x_2788_; lean_object* v___x_2789_; 
lean_del_object(v___x_2778_);
v_a_2784_ = lean_ctor_get(v_a_2776_, 0);
lean_inc(v_a_2784_);
lean_dec_ref_known(v_a_2776_, 1);
v___x_2785_ = lean_box(0);
v___x_2786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2785_);
lean_ctor_set(v___x_2786_, 1, v_a_2784_);
v_sz_2787_ = lean_array_size(v_tail_2774_);
v___x_2788_ = ((size_t)0ULL);
v___x_2789_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_tail_2774_, v_sz_2787_, v___x_2788_, v___x_2786_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2803_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2792_ = v___x_2789_;
v_isShared_2793_ = v_isSharedCheck_2803_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_a_2790_);
lean_dec(v___x_2789_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2803_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v_fst_2794_; 
v_fst_2794_ = lean_ctor_get(v_a_2790_, 0);
if (lean_obj_tag(v_fst_2794_) == 0)
{
lean_object* v_snd_2795_; lean_object* v___x_2797_; 
v_snd_2795_ = lean_ctor_get(v_a_2790_, 1);
lean_inc(v_snd_2795_);
lean_dec(v_a_2790_);
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 0, v_snd_2795_);
v___x_2797_ = v___x_2792_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_snd_2795_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
else
{
lean_object* v_val_2799_; lean_object* v___x_2801_; 
lean_inc_ref(v_fst_2794_);
lean_dec(v_a_2790_);
v_val_2799_ = lean_ctor_get(v_fst_2794_, 0);
lean_inc(v_val_2799_);
lean_dec_ref_known(v_fst_2794_, 1);
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 0, v_val_2799_);
v___x_2801_ = v___x_2792_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_val_2799_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
}
else
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2811_; 
v_a_2804_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2806_ = v___x_2789_;
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2789_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
if (v_isShared_2807_ == 0)
{
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_a_2804_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
}
}
}
else
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
v_a_2813_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2815_ = v___x_2775_;
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2775_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7___boxed(lean_object* v_t_2821_, lean_object* v_init_2822_, lean_object* v___y_2823_){
_start:
{
lean_object* v_res_2824_; 
v_res_2824_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_t_2821_, v_init_2822_);
lean_dec_ref(v_t_2821_);
return v_res_2824_;
}
}
static lean_object* _init_l_main___closed__3(void){
_start:
{
lean_object* v___x_2828_; 
v___x_2828_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(lean_box(0), lean_box(0), lean_box(0));
return v___x_2828_;
}
}
static lean_object* _init_l_main___closed__4(void){
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
static lean_object* _init_l_main___closed__5(void){
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
static lean_object* _init_l_main___closed__6(void){
_start:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2835_ = ((lean_object*)(l_main___closed__2));
v___x_2836_ = ((lean_object*)(l_main___closed__1));
v___x_2837_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_2836_, v___x_2835_);
return v___x_2837_;
}
}
static lean_object* _init_l_main___closed__7(void){
_start:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2838_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_2839_ = lean_box(0);
v___x_2840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2839_);
lean_ctor_set(v___x_2840_, 1, v___x_2838_);
return v___x_2840_;
}
}
static lean_object* _init_l_main___closed__8(void){
_start:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___x_2841_ = lean_obj_once(&l_main___closed__7, &l_main___closed__7_once, _init_l_main___closed__7);
v___x_2842_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2841_);
return v___x_2842_;
}
}
static lean_object* _init_l_main___closed__9(void){
_start:
{
lean_object* v___x_2843_; 
v___x_2843_ = l_Array_instInhabited(lean_box(0));
return v___x_2843_;
}
}
static lean_object* _init_l_main___closed__15(void){
_start:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2852_ = l_Lean_Options_empty;
v___x_2853_ = l_Lean_Core_getMaxHeartbeats(v___x_2852_);
return v___x_2853_;
}
}
static lean_object* _init_l_main___closed__20(void){
_start:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; 
v___x_2858_ = ((lean_object*)(l_main___closed__19));
v___x_2859_ = lean_unsigned_to_nat(27u);
v___x_2860_ = lean_unsigned_to_nat(149u);
v___x_2861_ = ((lean_object*)(l_main___closed__18));
v___x_2862_ = ((lean_object*)(l_main___closed__17));
v___x_2863_ = l_mkPanicMessageWithDecl(v___x_2862_, v___x_2861_, v___x_2860_, v___x_2859_, v___x_2858_);
return v___x_2863_;
}
}
static lean_object* _init_l_main___closed__22(void){
_start:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2865_ = ((lean_object*)(l_main___closed__19));
v___x_2866_ = lean_unsigned_to_nat(51u);
v___x_2867_ = lean_unsigned_to_nat(122u);
v___x_2868_ = ((lean_object*)(l_main___closed__18));
v___x_2869_ = ((lean_object*)(l_main___closed__17));
v___x_2870_ = l_mkPanicMessageWithDecl(v___x_2869_, v___x_2868_, v___x_2867_, v___x_2866_, v___x_2865_);
return v___x_2870_;
}
}
static lean_object* _init_l_main___closed__23(void){
_start:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2871_ = lean_unsigned_to_nat(1u);
v___x_2872_ = l_Lean_firstFrontendMacroScope;
v___x_2873_ = lean_nat_add(v___x_2872_, v___x_2871_);
return v___x_2873_;
}
}
static lean_object* _init_l_main___closed__27(void){
_start:
{
lean_object* v___x_2880_; uint64_t v___x_2881_; lean_object* v___x_2882_; 
v___x_2880_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2881_ = 0ULL;
v___x_2882_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2882_, 0, v___x_2880_);
lean_ctor_set_uint64(v___x_2882_, sizeof(void*)*1, v___x_2881_);
return v___x_2882_;
}
}
static lean_object* _init_l_main___closed__28(void){
_start:
{
lean_object* v___x_2883_; 
v___x_2883_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2883_;
}
}
static lean_object* _init_l_main___closed__29(void){
_start:
{
lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2884_ = lean_obj_once(&l_main___closed__28, &l_main___closed__28_once, _init_l_main___closed__28);
v___x_2885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2884_);
return v___x_2885_;
}
}
static lean_object* _init_l_main___closed__30(void){
_start:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2886_ = lean_obj_once(&l_main___closed__29, &l_main___closed__29_once, _init_l_main___closed__29);
v___x_2887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2886_);
lean_ctor_set(v___x_2887_, 1, v___x_2886_);
return v___x_2887_;
}
}
static lean_object* _init_l_main___closed__31(void){
_start:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2888_ = l_Lean_NameSet_empty;
v___x_2889_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2890_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2889_);
lean_ctor_set(v___x_2890_, 1, v___x_2889_);
lean_ctor_set(v___x_2890_, 2, v___x_2888_);
return v___x_2890_;
}
}
static lean_object* _init_l_main___closed__32(void){
_start:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; uint8_t v___x_2893_; lean_object* v___x_2894_; 
v___x_2891_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2892_ = lean_obj_once(&l_main___closed__29, &l_main___closed__29_once, _init_l_main___closed__29);
v___x_2893_ = 1;
v___x_2894_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2894_, 0, v___x_2892_);
lean_ctor_set(v___x_2894_, 1, v___x_2892_);
lean_ctor_set(v___x_2894_, 2, v___x_2891_);
lean_ctor_set_uint8(v___x_2894_, sizeof(void*)*3, v___x_2893_);
return v___x_2894_;
}
}
static uint8_t _init_l_main___closed__37(void){
_start:
{
uint8_t v___x_2901_; uint8_t v___x_2902_; uint8_t v___x_2903_; 
v___x_2901_ = 2;
v___x_2902_ = 0;
v___x_2903_ = l_Lean_instOrdOLeanLevel_ord(v___x_2902_, v___x_2901_);
return v___x_2903_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_2904_; lean_object* v___x_2905_; 
v___x_2904_ = 1;
v___x_2905_ = lean_box_uint32(v___x_2904_);
return v___x_2905_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_2906_; lean_object* v___x_2907_; 
v___x_2906_ = 0;
v___x_2907_ = lean_box_uint32(v___x_2906_);
return v___x_2907_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_2908_){
_start:
{
if (lean_obj_tag(v_args_2908_) == 1)
{
lean_object* v_tail_2933_; 
v_tail_2933_ = lean_ctor_get(v_args_2908_, 1);
lean_inc(v_tail_2933_);
if (lean_obj_tag(v_tail_2933_) == 1)
{
lean_object* v_tail_2934_; 
v_tail_2934_ = lean_ctor_get(v_tail_2933_, 1);
lean_inc(v_tail_2934_);
if (lean_obj_tag(v_tail_2934_) == 1)
{
lean_object* v_head_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_3580_; 
v_head_2935_ = lean_ctor_get(v_args_2908_, 0);
v_isSharedCheck_3580_ = !lean_is_exclusive(v_args_2908_);
if (v_isSharedCheck_3580_ == 0)
{
lean_object* v_unused_3581_; 
v_unused_3581_ = lean_ctor_get(v_args_2908_, 1);
lean_dec(v_unused_3581_);
v___x_2937_ = v_args_2908_;
v_isShared_2938_ = v_isSharedCheck_3580_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_head_2935_);
lean_dec(v_args_2908_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_3580_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v_head_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_3578_; 
v_head_2939_ = lean_ctor_get(v_tail_2933_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v_tail_2933_);
if (v_isSharedCheck_3578_ == 0)
{
lean_object* v_unused_3579_; 
v_unused_3579_ = lean_ctor_get(v_tail_2933_, 1);
lean_dec(v_unused_3579_);
v___x_2941_ = v_tail_2933_;
v_isShared_2942_ = v_isSharedCheck_3578_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_head_2939_);
lean_dec(v_tail_2933_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_3578_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v_head_2943_; lean_object* v_tail_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_3577_; 
v_head_2943_ = lean_ctor_get(v_tail_2934_, 0);
v_tail_2944_ = lean_ctor_get(v_tail_2934_, 1);
v_isSharedCheck_3577_ = !lean_is_exclusive(v_tail_2934_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_2946_ = v_tail_2934_;
v_isShared_2947_ = v_isSharedCheck_3577_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_tail_2944_);
lean_inc(v_head_2943_);
lean_dec(v_tail_2934_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_3577_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2948_; 
v___x_2948_ = l_Lean_ModuleSetup_load(v_head_2935_);
lean_dec(v_head_2935_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v_a_2949_; lean_object* v_name_2950_; lean_object* v_importArts_2951_; lean_object* v_options_2952_; uint8_t v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2957_; 
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
lean_inc(v_a_2949_);
lean_dec_ref_known(v___x_2948_, 1);
v_name_2950_ = lean_ctor_get(v_a_2949_, 0);
lean_inc(v_name_2950_);
v_importArts_2951_ = lean_ctor_get(v_a_2949_, 3);
lean_inc(v_importArts_2951_);
v_options_2952_ = lean_ctor_get(v_a_2949_, 6);
lean_inc(v_options_2952_);
lean_dec(v_a_2949_);
v___x_2953_ = 0;
v___x_2954_ = l_Lean_LeanOptions_toOptions(v_options_2952_);
v___x_2955_ = lean_box(v___x_2953_);
if (v_isShared_2947_ == 0)
{
lean_ctor_set_tag(v___x_2946_, 0);
lean_ctor_set(v___x_2946_, 1, v___x_2954_);
lean_ctor_set(v___x_2946_, 0, v___x_2955_);
v___x_2957_ = v___x_2946_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v___x_2955_);
lean_ctor_set(v_reuseFailAlloc_3568_, 1, v___x_2954_);
v___x_2957_ = v_reuseFailAlloc_3568_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
lean_object* v___x_2958_; 
v___x_2958_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_tail_2944_, v___x_2957_);
lean_dec(v_tail_2944_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; lean_object* v___x_2960_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
lean_inc(v_a_2959_);
lean_dec_ref_known(v___x_2958_, 1);
v___x_2960_ = lean_init_search_path();
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_fst_2961_; lean_object* v_snd_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_3551_; 
lean_dec_ref_known(v___x_2960_, 1);
v_fst_2961_ = lean_ctor_get(v_a_2959_, 0);
v_snd_2962_ = lean_ctor_get(v_a_2959_, 1);
v_isSharedCheck_3551_ = !lean_is_exclusive(v_a_2959_);
if (v_isSharedCheck_3551_ == 0)
{
v___x_2964_ = v_a_2959_;
v_isShared_2965_ = v_isSharedCheck_3551_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_snd_2962_);
lean_inc(v_fst_2961_);
lean_dec(v_a_2959_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_3551_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; uint8_t v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; uint8_t v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3135_; uint8_t v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v_nextMacroScope_3153_; lean_object* v_ngen_3154_; lean_object* v_auxDeclNGen_3155_; lean_object* v_traceState_3156_; lean_object* v_messages_3157_; lean_object* v_infoState_3158_; lean_object* v_snapshotTasks_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; uint8_t v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; uint8_t v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3249_; uint8_t v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; uint8_t v___y_3271_; uint8_t v___y_3272_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; uint8_t v___x_3297_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3425_; lean_object* v___y_3426_; lean_object* v___y_3427_; lean_object* v___y_3428_; lean_object* v___y_3429_; lean_object* v___y_3430_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; uint8_t v___x_3454_; uint8_t v___y_3456_; uint8_t v___x_3550_; 
v___x_2966_ = lean_obj_once(&l_main___closed__3, &l_main___closed__3_once, _init_l_main___closed__3);
v___x_2967_ = lean_box(0);
v___x_2968_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_2969_ = lean_obj_once(&l_main___closed__5, &l_main___closed__5_once, _init_l_main___closed__5);
v___x_2970_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_2971_ = lean_obj_once(&l_main___closed__8, &l_main___closed__8_once, _init_l_main___closed__8);
v___x_2972_ = lean_obj_once(&l_main___closed__9, &l_main___closed__9_once, _init_l_main___closed__9);
v___x_2973_ = lean_box(1);
v___x_2974_ = ((lean_object*)(l_main___closed__10));
v___x_2975_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_2976_ = 1;
v___x_2977_ = l_Lean_Option_set___at___00Lean_Environment_realizeConst_spec__0(v_snd_2962_, v___x_2975_, v___x_2976_);
v___x_2978_ = l_Lean_maxHeartbeats;
v___x_2979_ = lean_unsigned_to_nat(0u);
v___x_2980_ = l_Lean_Option_set___at___00main_spec__3(v___x_2977_, v___x_2978_, v___x_2979_);
v___x_3292_ = ((lean_object*)(l_main___closed__21));
lean_inc(v_name_2950_);
v___x_3293_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_3293_, 0, v_name_2950_);
lean_ctor_set_uint8(v___x_3293_, sizeof(void*)*1, v___x_2976_);
lean_ctor_set_uint8(v___x_3293_, sizeof(void*)*1 + 1, v___x_2976_);
lean_ctor_set_uint8(v___x_3293_, sizeof(void*)*1 + 2, v___x_2953_);
v___x_3294_ = lean_unsigned_to_nat(1u);
v___x_3295_ = lean_mk_empty_array_with_capacity(v___x_3294_);
v___x_3296_ = lean_array_push(v___x_3295_, v___x_3293_);
v___x_3297_ = 0;
v___x_3454_ = 2;
v___x_3550_ = lean_uint8_once(&l_main___closed__37, &l_main___closed__37_once, _init_l_main___closed__37);
if (v___x_3550_ == 0)
{
v___y_3456_ = v___x_2976_;
goto v___jp_3455_;
}
else
{
v___y_3456_ = v___x_2953_;
goto v___jp_3455_;
}
v___jp_2981_:
{
lean_object* v___x_3001_; lean_object* v_messages_3002_; lean_object* v_env_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3126_; 
v___x_3001_ = lean_st_ref_get(v___y_2994_);
lean_dec(v___y_2994_);
v_messages_3002_ = lean_ctor_get(v___x_3001_, 6);
v_env_3003_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3126_ == 0)
{
lean_object* v_unused_3127_; lean_object* v_unused_3128_; lean_object* v_unused_3129_; lean_object* v_unused_3130_; lean_object* v_unused_3131_; lean_object* v_unused_3132_; lean_object* v_unused_3133_; 
v_unused_3127_ = lean_ctor_get(v___x_3001_, 8);
lean_dec(v_unused_3127_);
v_unused_3128_ = lean_ctor_get(v___x_3001_, 7);
lean_dec(v_unused_3128_);
v_unused_3129_ = lean_ctor_get(v___x_3001_, 5);
lean_dec(v_unused_3129_);
v_unused_3130_ = lean_ctor_get(v___x_3001_, 4);
lean_dec(v_unused_3130_);
v_unused_3131_ = lean_ctor_get(v___x_3001_, 3);
lean_dec(v_unused_3131_);
v_unused_3132_ = lean_ctor_get(v___x_3001_, 2);
lean_dec(v_unused_3132_);
v_unused_3133_ = lean_ctor_get(v___x_3001_, 1);
lean_dec(v_unused_3133_);
v___x_3005_ = v___x_3001_;
v_isShared_3006_ = v_isSharedCheck_3126_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_messages_3002_);
lean_inc(v_env_3003_);
lean_dec(v___x_3001_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3126_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v_unreported_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v_unreported_3007_ = lean_ctor_get(v_messages_3002_, 1);
v___x_3008_ = lean_box(0);
v___x_3009_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_unreported_3007_, v___x_3008_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3116_; 
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3116_ == 0)
{
lean_object* v_unused_3117_; 
v_unused_3117_ = lean_ctor_get(v___x_3009_, 0);
lean_dec(v_unused_3117_);
v___x_3011_ = v___x_3009_;
v_isShared_3012_ = v_isSharedCheck_3116_;
goto v_resetjp_3010_;
}
else
{
lean_dec(v___x_3009_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3116_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
uint8_t v___x_3013_; 
v___x_3013_ = l_Lean_MessageLog_hasErrors(v_messages_3002_);
lean_dec_ref(v_messages_3002_);
if (v___x_3013_ == 0)
{
lean_object* v___x_3014_; 
lean_del_object(v___x_3011_);
lean_inc_ref(v_env_3003_);
v___x_3014_ = l___private_LeanIR_0__mkIRSigData(v_env_3003_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v_a_3015_; lean_object* v___x_3016_; 
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc(v_a_3015_);
lean_dec_ref_known(v___x_3014_, 1);
lean_inc_ref(v_env_3003_);
v___x_3016_ = l___private_LeanIR_0__mkIRData(v_env_3003_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_a_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3024_; 
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_a_3017_);
lean_dec_ref_known(v___x_3016_, 1);
v___x_3018_ = ((lean_object*)(l_main___closed__11));
lean_inc(v_head_2939_);
v___x_3019_ = l_System_FilePath_addExtension(v_head_2939_, v___x_3018_);
v___x_3020_ = l_Lean_Environment_mainModule(v_env_3003_);
v___x_3021_ = ((lean_object*)(l_main___closed__13));
v___x_3022_ = l_Lean_Name_append(v___x_3020_, v___x_3021_);
if (v_isShared_2965_ == 0)
{
lean_ctor_set(v___x_2964_, 1, v_a_3015_);
lean_ctor_set(v___x_2964_, 0, v___x_3019_);
v___x_3024_ = v___x_2964_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v___x_3019_);
lean_ctor_set(v_reuseFailAlloc_3095_, 1, v_a_3015_);
v___x_3024_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
lean_object* v___x_3026_; 
lean_inc(v_head_2939_);
if (v_isShared_2942_ == 0)
{
lean_ctor_set_tag(v___x_2941_, 0);
lean_ctor_set(v___x_2941_, 1, v_a_3017_);
v___x_3026_ = v___x_2941_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_head_2939_);
lean_ctor_set(v_reuseFailAlloc_3094_, 1, v_a_3017_);
v___x_3026_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3027_ = lean_unsigned_to_nat(2u);
v___x_3028_ = lean_mk_empty_array_with_capacity(v___x_3027_);
v___x_3029_ = lean_array_push(v___x_3028_, v___x_3024_);
v___x_3030_ = lean_array_push(v___x_3029_, v___x_3026_);
v___x_3031_ = l_Lean_saveModuleDataParts(v___x_3022_, v___x_3030_);
lean_dec_ref(v___x_3030_);
lean_dec(v___x_3022_);
if (lean_obj_tag(v___x_3031_) == 0)
{
uint8_t v___x_3032_; lean_object* v___x_3033_; 
lean_dec_ref_known(v___x_3031_, 1);
v___x_3032_ = 1;
v___x_3033_ = lean_io_prim_handle_mk(v_head_2943_, v___x_3032_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_object* v_a_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3039_; 
lean_dec(v_head_2943_);
v_a_3034_ = lean_ctor_get(v___x_3033_, 0);
lean_inc(v_a_3034_);
lean_dec_ref_known(v___x_3033_, 1);
v___x_3035_ = ((lean_object*)(l_main___closed__14));
v___x_3036_ = l_Lean_Options_empty;
v___x_3037_ = lean_obj_once(&l_main___closed__15, &l_main___closed__15_once, _init_l_main___closed__15);
lean_inc_ref(v___y_2991_);
lean_inc_ref(v___y_2995_);
lean_inc_ref(v___y_2992_);
lean_inc_ref(v___y_2997_);
lean_inc_ref(v___y_2998_);
lean_inc_ref(v___y_3000_);
lean_inc(v___y_2993_);
lean_inc_ref(v_env_3003_);
if (v_isShared_3006_ == 0)
{
lean_ctor_set(v___x_3005_, 8, v___y_2991_);
lean_ctor_set(v___x_3005_, 7, v___y_2995_);
lean_ctor_set(v___x_3005_, 6, v___y_2992_);
lean_ctor_set(v___x_3005_, 5, v___y_2997_);
lean_ctor_set(v___x_3005_, 4, v___y_2998_);
lean_ctor_set(v___x_3005_, 3, v___y_2999_);
lean_ctor_set(v___x_3005_, 2, v___y_3000_);
lean_ctor_set(v___x_3005_, 1, v___y_2993_);
v___x_3039_ = v___x_3005_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_env_3003_);
lean_ctor_set(v_reuseFailAlloc_3063_, 1, v___y_2993_);
lean_ctor_set(v_reuseFailAlloc_3063_, 2, v___y_3000_);
lean_ctor_set(v_reuseFailAlloc_3063_, 3, v___y_2999_);
lean_ctor_set(v_reuseFailAlloc_3063_, 4, v___y_2998_);
lean_ctor_set(v_reuseFailAlloc_3063_, 5, v___y_2997_);
lean_ctor_set(v_reuseFailAlloc_3063_, 6, v___y_2992_);
lean_ctor_set(v_reuseFailAlloc_3063_, 7, v___y_2995_);
lean_ctor_set(v_reuseFailAlloc_3063_, 8, v___y_2991_);
v___x_3039_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___f_3042_; lean_object* v___x_3043_; 
v___x_3040_ = lean_box(v___y_2982_);
v___x_3041_ = lean_box(v___x_2953_);
lean_inc(v___y_2986_);
lean_inc(v___y_2988_);
lean_inc(v___y_2984_);
lean_inc(v___y_2989_);
lean_inc_ref(v___y_2985_);
lean_inc_ref(v___y_2990_);
lean_inc(v___y_2983_);
v___f_3042_ = lean_alloc_closure((void*)(l_main___lam__1___boxed), 18, 17);
lean_closure_set(v___f_3042_, 0, v___x_3039_);
lean_closure_set(v___f_3042_, 1, v___y_2983_);
lean_closure_set(v___f_3042_, 2, v___x_3036_);
lean_closure_set(v___f_3042_, 3, v_name_2950_);
lean_closure_set(v___f_3042_, 4, v_a_3034_);
lean_closure_set(v___f_3042_, 5, v___x_3040_);
lean_closure_set(v___f_3042_, 6, v___y_2990_);
lean_closure_set(v___f_3042_, 7, v_head_2939_);
lean_closure_set(v___f_3042_, 8, v___y_2985_);
lean_closure_set(v___f_3042_, 9, v___x_2979_);
lean_closure_set(v___f_3042_, 10, v___y_2989_);
lean_closure_set(v___f_3042_, 11, v___y_2987_);
lean_closure_set(v___f_3042_, 12, v___y_2984_);
lean_closure_set(v___f_3042_, 13, v___x_3037_);
lean_closure_set(v___f_3042_, 14, v___y_2988_);
lean_closure_set(v___f_3042_, 15, v___y_2986_);
lean_closure_set(v___f_3042_, 16, v___x_3041_);
v___x_3043_ = l_Lean_profileitIOUnsafe___redArg(v___x_3035_, v___x_2980_, v___f_3042_, v___y_2996_);
lean_dec_ref(v___x_2980_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_object* v___x_3044_; uint8_t v___x_3045_; 
lean_dec_ref_known(v___x_3043_, 1);
v___x_3044_ = lean_display_cumulative_profiling_times();
v___x_3045_ = lean_unbox(v_fst_2961_);
lean_dec(v_fst_2961_);
if (v___x_3045_ == 0)
{
lean_dec_ref(v_env_3003_);
goto v___jp_2930_;
}
else
{
lean_object* v___x_3046_; 
v___x_3046_ = l_Lean_Environment_displayStats(v_env_3003_);
if (lean_obj_tag(v___x_3046_) == 0)
{
lean_dec_ref_known(v___x_3046_, 1);
goto v___jp_2930_;
}
else
{
lean_object* v_a_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3054_; 
v_a_3047_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3049_ = v___x_3046_;
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_a_3047_);
lean_dec(v___x_3046_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3052_; 
if (v_isShared_3050_ == 0)
{
v___x_3052_ = v___x_3049_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_a_3047_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
}
}
else
{
lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
lean_dec_ref(v_env_3003_);
lean_dec(v_fst_2961_);
v_a_3055_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3057_ = v___x_3043_;
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___x_3043_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3060_; 
if (v_isShared_3058_ == 0)
{
v___x_3060_ = v___x_3057_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3055_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
}
}
else
{
lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
lean_dec_ref_known(v___x_3033_, 1);
lean_del_object(v___x_3005_);
lean_dec_ref(v_env_3003_);
lean_dec_ref(v___y_2999_);
lean_dec(v___y_2996_);
lean_dec(v___y_2987_);
lean_dec_ref(v___x_2980_);
lean_dec(v_fst_2961_);
lean_dec(v_name_2950_);
lean_dec(v_head_2939_);
v___x_3064_ = ((lean_object*)(l_main___closed__16));
v___x_3065_ = lean_string_append(v___x_3064_, v_head_2943_);
lean_dec(v_head_2943_);
v___x_3066_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__1));
v___x_3067_ = lean_string_append(v___x_3065_, v___x_3066_);
v___x_3068_ = l_IO_eprintln___at___00main_spec__6(v___x_3067_);
if (lean_obj_tag(v___x_3068_) == 0)
{
lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3076_; 
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3076_ == 0)
{
lean_object* v_unused_3077_; 
v_unused_3077_ = lean_ctor_get(v___x_3068_, 0);
lean_dec(v_unused_3077_);
v___x_3070_ = v___x_3068_;
v_isShared_3071_ = v_isSharedCheck_3076_;
goto v_resetjp_3069_;
}
else
{
lean_dec(v___x_3068_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3076_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3072_; lean_object* v___x_3074_; 
v___x_3072_ = l_main___boxed__const__1;
if (v_isShared_3071_ == 0)
{
lean_ctor_set(v___x_3070_, 0, v___x_3072_);
v___x_3074_ = v___x_3070_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v___x_3072_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
else
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3085_; 
v_a_3078_ = lean_ctor_get(v___x_3068_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_3068_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_3068_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3083_; 
if (v_isShared_3081_ == 0)
{
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3078_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
}
}
else
{
lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3093_; 
lean_del_object(v___x_3005_);
lean_dec_ref(v_env_3003_);
lean_dec_ref(v___y_2999_);
lean_dec(v___y_2996_);
lean_dec(v___y_2987_);
lean_dec_ref(v___x_2980_);
lean_dec(v_fst_2961_);
lean_dec(v_name_2950_);
lean_dec(v_head_2943_);
lean_dec(v_head_2939_);
v_a_3086_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3088_ = v___x_3031_;
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v___x_3031_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3091_; 
if (v_isShared_3089_ == 0)
{
v___x_3091_ = v___x_3088_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_a_3086_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
}
}
}
else
{
lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3103_; 
lean_dec(v_a_3015_);
lean_del_object(v___x_3005_);
lean_dec_ref(v_env_3003_);
lean_dec_ref(v___y_2999_);
lean_dec(v___y_2996_);
lean_dec(v___y_2987_);
lean_dec_ref(v___x_2980_);
lean_del_object(v___x_2964_);
lean_dec(v_fst_2961_);
lean_dec(v_name_2950_);
lean_dec(v_head_2943_);
lean_del_object(v___x_2941_);
lean_dec(v_head_2939_);
v_a_3096_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3098_ = v___x_3016_;
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_3016_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v___x_3101_; 
if (v_isShared_3099_ == 0)
{
v___x_3101_ = v___x_3098_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_a_3096_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
}
else
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
lean_del_object(v___x_3005_);
lean_dec_ref(v_env_3003_);
lean_dec_ref(v___y_2999_);
lean_dec(v___y_2996_);
lean_dec(v___y_2987_);
lean_dec_ref(v___x_2980_);
lean_del_object(v___x_2964_);
lean_dec(v_fst_2961_);
lean_dec(v_name_2950_);
lean_dec(v_head_2943_);
lean_del_object(v___x_2941_);
lean_dec(v_head_2939_);
v_a_3104_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_3014_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3014_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3109_; 
if (v_isShared_3107_ == 0)
{
v___x_3109_ = v___x_3106_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3104_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
}
else
{
lean_object* v___x_3112_; lean_object* v___x_3114_; 
lean_del_object(v___x_3005_);
lean_dec_ref(v_env_3003_);
lean_dec_ref(v___y_2999_);
lean_dec(v___y_2996_);
lean_dec(v___y_2987_);
lean_dec_ref(v___x_2980_);
lean_del_object(v___x_2964_);
lean_dec(v_fst_2961_);
lean_dec(v_name_2950_);
lean_dec(v_head_2943_);
lean_del_object(v___x_2941_);
lean_dec(v_head_2939_);
v___x_3112_ = l_main___boxed__const__1;
if (v_isShared_3012_ == 0)
{
lean_ctor_set(v___x_3011_, 0, v___x_3112_);
v___x_3114_ = v___x_3011_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3112_);
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
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3125_; 
lean_del_object(v___x_3005_);
lean_dec_ref(v_env_3003_);
lean_dec_ref(v_messages_3002_);
lean_dec_ref(v___y_2999_);
lean_dec(v___y_2996_);
lean_dec(v___y_2987_);
lean_dec_ref(v___x_2980_);
lean_del_object(v___x_2964_);
lean_dec(v_fst_2961_);
lean_dec(v_name_2950_);
lean_dec(v_head_2943_);
lean_del_object(v___x_2941_);
lean_dec(v_head_2939_);
v_a_3118_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3120_ = v___x_3009_;
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_3009_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3123_; 
if (v_isShared_3121_ == 0)
{
v___x_3123_ = v___x_3120_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_a_3118_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
}
}
v___jp_3134_:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; size_t v_sz_3168_; size_t v___x_3169_; lean_object* v___x_3170_; 
lean_inc_ref(v___y_3147_);
v___x_3165_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3165_, 0, v___y_3164_);
lean_ctor_set(v___x_3165_, 1, v_nextMacroScope_3153_);
lean_ctor_set(v___x_3165_, 2, v_ngen_3154_);
lean_ctor_set(v___x_3165_, 3, v_auxDeclNGen_3155_);
lean_ctor_set(v___x_3165_, 4, v_traceState_3156_);
lean_ctor_set(v___x_3165_, 5, v___y_3147_);
lean_ctor_set(v___x_3165_, 6, v_messages_3157_);
lean_ctor_set(v___x_3165_, 7, v_infoState_3158_);
lean_ctor_set(v___x_3165_, 8, v_snapshotTasks_3159_);
v___x_3166_ = lean_st_ref_put(v___y_3146_, v___x_3165_);
v___x_3167_ = lean_box(0);
v_sz_3168_ = lean_array_size(v___y_3160_);
v___x_3169_ = ((size_t)0ULL);
v___x_3170_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(v___y_3160_, v_sz_3168_, v___x_3169_, v___x_3167_, v___y_3152_, v___y_3146_);
lean_dec_ref(v___y_3160_);
if (lean_obj_tag(v___x_3170_) == 0)
{
lean_dec_ref_known(v___x_3170_, 1);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3146_);
v___y_2982_ = v___y_3136_;
v___y_2983_ = v___y_3135_;
v___y_2984_ = v___y_3138_;
v___y_2985_ = v___y_3137_;
v___y_2986_ = v___y_3139_;
v___y_2987_ = v___y_3140_;
v___y_2988_ = v___y_3141_;
v___y_2989_ = v___y_3143_;
v___y_2990_ = v___y_3142_;
v___y_2991_ = v___y_3144_;
v___y_2992_ = v___y_3148_;
v___y_2993_ = v___y_3145_;
v___y_2994_ = v___y_3149_;
v___y_2995_ = v___y_3150_;
v___y_2996_ = v___y_3151_;
v___y_2997_ = v___y_3147_;
v___y_2998_ = v___y_3161_;
v___y_2999_ = v___y_3163_;
v___y_3000_ = v___y_3162_;
goto v___jp_2981_;
}
else
{
if (lean_obj_tag(v___x_3170_) == 0)
{
lean_dec_ref_known(v___x_3170_, 1);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3146_);
v___y_2982_ = v___y_3136_;
v___y_2983_ = v___y_3135_;
v___y_2984_ = v___y_3138_;
v___y_2985_ = v___y_3137_;
v___y_2986_ = v___y_3139_;
v___y_2987_ = v___y_3140_;
v___y_2988_ = v___y_3141_;
v___y_2989_ = v___y_3143_;
v___y_2990_ = v___y_3142_;
v___y_2991_ = v___y_3144_;
v___y_2992_ = v___y_3148_;
v___y_2993_ = v___y_3145_;
v___y_2994_ = v___y_3149_;
v___y_2995_ = v___y_3150_;
v___y_2996_ = v___y_3151_;
v___y_2997_ = v___y_3147_;
v___y_2998_ = v___y_3161_;
v___y_2999_ = v___y_3163_;
v___y_3000_ = v___y_3162_;
goto v___jp_2981_;
}
else
{
lean_object* v_a_3171_; uint8_t v___x_3172_; 
v_a_3171_ = lean_ctor_get(v___x_3170_, 0);
lean_inc(v_a_3171_);
lean_dec_ref_known(v___x_3170_, 1);
v___x_3172_ = l_Lean_Exception_isInterrupt(v_a_3171_);
if (v___x_3172_ == 0)
{
lean_object* v___x_3173_; lean_object* v___x_3174_; 
v___x_3173_ = l_Lean_Exception_toMessageData(v_a_3171_);
v___x_3174_ = l_Lean_logError___at___00main_spec__14(v___x_3173_, v___y_3152_, v___y_3146_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3152_);
if (lean_obj_tag(v___x_3174_) == 0)
{
lean_dec_ref_known(v___x_3174_, 1);
v___y_2982_ = v___y_3136_;
v___y_2983_ = v___y_3135_;
v___y_2984_ = v___y_3138_;
v___y_2985_ = v___y_3137_;
v___y_2986_ = v___y_3139_;
v___y_2987_ = v___y_3140_;
v___y_2988_ = v___y_3141_;
v___y_2989_ = v___y_3143_;
v___y_2990_ = v___y_3142_;
v___y_2991_ = v___y_3144_;
v___y_2992_ = v___y_3148_;
v___y_2993_ = v___y_3145_;
v___y_2994_ = v___y_3149_;
v___y_2995_ = v___y_3150_;
v___y_2996_ = v___y_3151_;
v___y_2997_ = v___y_3147_;
v___y_2998_ = v___y_3161_;
v___y_2999_ = v___y_3163_;
v___y_3000_ = v___y_3162_;
goto v___jp_2981_;
}
else
{
lean_object* v___x_3175_; lean_object* v___x_3176_; 
lean_dec_ref_known(v___x_3174_, 1);
lean_dec_ref(v___y_3163_);
lean_dec(v___y_3151_);
lean_dec(v___y_3149_);
lean_dec(v___y_3140_);
lean_dec_ref(v___x_2980_);
lean_del_object(v___x_2964_);
lean_dec(v_fst_2961_);
lean_dec(v_name_2950_);
lean_dec(v_head_2943_);
lean_del_object(v___x_2941_);
lean_dec(v_head_2939_);
v___x_3175_ = lean_obj_once(&l_main___closed__20, &l_main___closed__20_once, _init_l_main___closed__20);
v___x_3176_ = l_panic___at___00main_spec__5(v___x_3175_);
return v___x_3176_;
}
}
else
{
lean_dec(v_a_3171_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3146_);
v___y_2982_ = v___y_3136_;
v___y_2983_ = v___y_3135_;
v___y_2984_ = v___y_3138_;
v___y_2985_ = v___y_3137_;
v___y_2986_ = v___y_3139_;
v___y_2987_ = v___y_3140_;
v___y_2988_ = v___y_3141_;
v___y_2989_ = v___y_3143_;
v___y_2990_ = v___y_3142_;
v___y_2991_ = v___y_3144_;
v___y_2992_ = v___y_3148_;
v___y_2993_ = v___y_3145_;
v___y_2994_ = v___y_3149_;
v___y_2995_ = v___y_3150_;
v___y_2996_ = v___y_3151_;
v___y_2997_ = v___y_3147_;
v___y_2998_ = v___y_3161_;
v___y_2999_ = v___y_3163_;
v___y_3000_ = v___y_3162_;
goto v___jp_2981_;
}
}
}
}
v___jp_3177_:
{
lean_object* v___x_3202_; lean_object* v_fileName_3203_; lean_object* v_fileMap_3204_; lean_object* v_currRecDepth_3205_; lean_object* v_ref_3206_; lean_object* v_currNamespace_3207_; lean_object* v_openDecls_3208_; lean_object* v_initHeartbeats_3209_; lean_object* v_maxHeartbeats_3210_; lean_object* v_quotContext_3211_; lean_object* v_currMacroScope_3212_; lean_object* v_cancelTk_x3f_3213_; uint8_t v_suppressElabErrors_3214_; lean_object* v_inheritedTraceOptions_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3245_; 
v___x_3202_ = lean_st_ref_take(v___y_3201_);
v_fileName_3203_ = lean_ctor_get(v___y_3200_, 0);
v_fileMap_3204_ = lean_ctor_get(v___y_3200_, 1);
v_currRecDepth_3205_ = lean_ctor_get(v___y_3200_, 3);
v_ref_3206_ = lean_ctor_get(v___y_3200_, 5);
v_currNamespace_3207_ = lean_ctor_get(v___y_3200_, 6);
v_openDecls_3208_ = lean_ctor_get(v___y_3200_, 7);
v_initHeartbeats_3209_ = lean_ctor_get(v___y_3200_, 8);
v_maxHeartbeats_3210_ = lean_ctor_get(v___y_3200_, 9);
v_quotContext_3211_ = lean_ctor_get(v___y_3200_, 10);
v_currMacroScope_3212_ = lean_ctor_get(v___y_3200_, 11);
v_cancelTk_x3f_3213_ = lean_ctor_get(v___y_3200_, 12);
v_suppressElabErrors_3214_ = lean_ctor_get_uint8(v___y_3200_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3215_ = lean_ctor_get(v___y_3200_, 13);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___y_3200_);
if (v_isSharedCheck_3245_ == 0)
{
lean_object* v_unused_3246_; lean_object* v_unused_3247_; 
v_unused_3246_ = lean_ctor_get(v___y_3200_, 4);
lean_dec(v_unused_3246_);
v_unused_3247_ = lean_ctor_get(v___y_3200_, 2);
lean_dec(v_unused_3247_);
v___x_3217_ = v___y_3200_;
v_isShared_3218_ = v_isSharedCheck_3245_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_inheritedTraceOptions_3215_);
lean_inc(v_cancelTk_x3f_3213_);
lean_inc(v_currMacroScope_3212_);
lean_inc(v_quotContext_3211_);
lean_inc(v_maxHeartbeats_3210_);
lean_inc(v_initHeartbeats_3209_);
lean_inc(v_openDecls_3208_);
lean_inc(v_currNamespace_3207_);
lean_inc(v_ref_3206_);
lean_inc(v_currRecDepth_3205_);
lean_inc(v_fileMap_3204_);
lean_inc(v_fileName_3203_);
lean_dec(v___y_3200_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3245_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v_env_3219_; lean_object* v_nextMacroScope_3220_; lean_object* v_ngen_3221_; lean_object* v_auxDeclNGen_3222_; lean_object* v_traceState_3223_; lean_object* v_messages_3224_; lean_object* v_infoState_3225_; lean_object* v_snapshotTasks_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3230_; 
v_env_3219_ = lean_ctor_get(v___x_3202_, 0);
lean_inc_ref(v_env_3219_);
v_nextMacroScope_3220_ = lean_ctor_get(v___x_3202_, 1);
lean_inc(v_nextMacroScope_3220_);
v_ngen_3221_ = lean_ctor_get(v___x_3202_, 2);
lean_inc_ref(v_ngen_3221_);
v_auxDeclNGen_3222_ = lean_ctor_get(v___x_3202_, 3);
lean_inc_ref(v_auxDeclNGen_3222_);
v_traceState_3223_ = lean_ctor_get(v___x_3202_, 4);
lean_inc_ref(v_traceState_3223_);
v_messages_3224_ = lean_ctor_get(v___x_3202_, 6);
lean_inc_ref(v_messages_3224_);
v_infoState_3225_ = lean_ctor_get(v___x_3202_, 7);
lean_inc_ref(v_infoState_3225_);
v_snapshotTasks_3226_ = lean_ctor_get(v___x_3202_, 8);
lean_inc_ref(v_snapshotTasks_3226_);
lean_dec(v___x_3202_);
v___x_3227_ = l_Lean_maxRecDepth;
v___x_3228_ = l_Lean_Option_get___at___00main_spec__9(v___x_2980_, v___x_3227_);
lean_inc_ref(v___x_2980_);
if (v_isShared_3218_ == 0)
{
lean_ctor_set(v___x_3217_, 4, v___x_3228_);
lean_ctor_set(v___x_3217_, 2, v___x_2980_);
v___x_3230_ = v___x_3217_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v_fileName_3203_);
lean_ctor_set(v_reuseFailAlloc_3244_, 1, v_fileMap_3204_);
lean_ctor_set(v_reuseFailAlloc_3244_, 2, v___x_2980_);
lean_ctor_set(v_reuseFailAlloc_3244_, 3, v_currRecDepth_3205_);
lean_ctor_set(v_reuseFailAlloc_3244_, 4, v___x_3228_);
lean_ctor_set(v_reuseFailAlloc_3244_, 5, v_ref_3206_);
lean_ctor_set(v_reuseFailAlloc_3244_, 6, v_currNamespace_3207_);
lean_ctor_set(v_reuseFailAlloc_3244_, 7, v_openDecls_3208_);
lean_ctor_set(v_reuseFailAlloc_3244_, 8, v_initHeartbeats_3209_);
lean_ctor_set(v_reuseFailAlloc_3244_, 9, v_maxHeartbeats_3210_);
lean_ctor_set(v_reuseFailAlloc_3244_, 10, v_quotContext_3211_);
lean_ctor_set(v_reuseFailAlloc_3244_, 11, v_currMacroScope_3212_);
lean_ctor_set(v_reuseFailAlloc_3244_, 12, v_cancelTk_x3f_3213_);
lean_ctor_set(v_reuseFailAlloc_3244_, 13, v_inheritedTraceOptions_3215_);
lean_ctor_set_uint8(v_reuseFailAlloc_3244_, sizeof(void*)*14 + 1, v_suppressElabErrors_3214_);
v___x_3230_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
lean_object* v___x_3231_; uint8_t v___x_3232_; 
lean_ctor_set_uint8(v___x_3230_, sizeof(void*)*14, v___y_3197_);
v___x_3231_ = lean_array_get_size(v___y_3195_);
v___x_3232_ = lean_nat_dec_lt(v___x_2979_, v___x_3231_);
if (v___x_3232_ == 0)
{
lean_object* v___x_3233_; 
lean_inc_ref(v___y_3189_);
v___x_3233_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3189_, v_env_3219_, v___x_2973_);
v___y_3135_ = v___y_3179_;
v___y_3136_ = v___y_3178_;
v___y_3137_ = v___y_3181_;
v___y_3138_ = v___y_3180_;
v___y_3139_ = v___y_3182_;
v___y_3140_ = v___y_3183_;
v___y_3141_ = v___y_3184_;
v___y_3142_ = v___y_3186_;
v___y_3143_ = v___y_3185_;
v___y_3144_ = v___y_3187_;
v___y_3145_ = v___y_3188_;
v___y_3146_ = v___y_3201_;
v___y_3147_ = v___y_3190_;
v___y_3148_ = v___y_3191_;
v___y_3149_ = v___y_3192_;
v___y_3150_ = v___y_3193_;
v___y_3151_ = v___y_3194_;
v___y_3152_ = v___x_3230_;
v_nextMacroScope_3153_ = v_nextMacroScope_3220_;
v_ngen_3154_ = v_ngen_3221_;
v_auxDeclNGen_3155_ = v_auxDeclNGen_3222_;
v_traceState_3156_ = v_traceState_3223_;
v_messages_3157_ = v_messages_3224_;
v_infoState_3158_ = v_infoState_3225_;
v_snapshotTasks_3159_ = v_snapshotTasks_3226_;
v___y_3160_ = v___y_3195_;
v___y_3161_ = v___y_3196_;
v___y_3162_ = v___y_3198_;
v___y_3163_ = v___y_3199_;
v___y_3164_ = v___x_3233_;
goto v___jp_3134_;
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
lean_inc_ref(v___y_3189_);
v___x_3235_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3189_, v_env_3219_, v___x_2973_);
v___y_3135_ = v___y_3179_;
v___y_3136_ = v___y_3178_;
v___y_3137_ = v___y_3181_;
v___y_3138_ = v___y_3180_;
v___y_3139_ = v___y_3182_;
v___y_3140_ = v___y_3183_;
v___y_3141_ = v___y_3184_;
v___y_3142_ = v___y_3186_;
v___y_3143_ = v___y_3185_;
v___y_3144_ = v___y_3187_;
v___y_3145_ = v___y_3188_;
v___y_3146_ = v___y_3201_;
v___y_3147_ = v___y_3190_;
v___y_3148_ = v___y_3191_;
v___y_3149_ = v___y_3192_;
v___y_3150_ = v___y_3193_;
v___y_3151_ = v___y_3194_;
v___y_3152_ = v___x_3230_;
v_nextMacroScope_3153_ = v_nextMacroScope_3220_;
v_ngen_3154_ = v_ngen_3221_;
v_auxDeclNGen_3155_ = v_auxDeclNGen_3222_;
v_traceState_3156_ = v_traceState_3223_;
v_messages_3157_ = v_messages_3224_;
v_infoState_3158_ = v_infoState_3225_;
v_snapshotTasks_3159_ = v_snapshotTasks_3226_;
v___y_3160_ = v___y_3195_;
v___y_3161_ = v___y_3196_;
v___y_3162_ = v___y_3198_;
v___y_3163_ = v___y_3199_;
v___y_3164_ = v___x_3235_;
goto v___jp_3134_;
}
else
{
size_t v___x_3236_; size_t v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3236_ = ((size_t)0ULL);
v___x_3237_ = lean_usize_of_nat(v___x_3231_);
v___x_3238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3195_, v___x_3236_, v___x_3237_, v___x_2973_);
lean_inc_ref(v___y_3189_);
v___x_3239_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3189_, v_env_3219_, v___x_3238_);
v___y_3135_ = v___y_3179_;
v___y_3136_ = v___y_3178_;
v___y_3137_ = v___y_3181_;
v___y_3138_ = v___y_3180_;
v___y_3139_ = v___y_3182_;
v___y_3140_ = v___y_3183_;
v___y_3141_ = v___y_3184_;
v___y_3142_ = v___y_3186_;
v___y_3143_ = v___y_3185_;
v___y_3144_ = v___y_3187_;
v___y_3145_ = v___y_3188_;
v___y_3146_ = v___y_3201_;
v___y_3147_ = v___y_3190_;
v___y_3148_ = v___y_3191_;
v___y_3149_ = v___y_3192_;
v___y_3150_ = v___y_3193_;
v___y_3151_ = v___y_3194_;
v___y_3152_ = v___x_3230_;
v_nextMacroScope_3153_ = v_nextMacroScope_3220_;
v_ngen_3154_ = v_ngen_3221_;
v_auxDeclNGen_3155_ = v_auxDeclNGen_3222_;
v_traceState_3156_ = v_traceState_3223_;
v_messages_3157_ = v_messages_3224_;
v_infoState_3158_ = v_infoState_3225_;
v_snapshotTasks_3159_ = v_snapshotTasks_3226_;
v___y_3160_ = v___y_3195_;
v___y_3161_ = v___y_3196_;
v___y_3162_ = v___y_3198_;
v___y_3163_ = v___y_3199_;
v___y_3164_ = v___x_3239_;
goto v___jp_3134_;
}
}
else
{
size_t v___x_3240_; size_t v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; 
v___x_3240_ = ((size_t)0ULL);
v___x_3241_ = lean_usize_of_nat(v___x_3231_);
v___x_3242_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3195_, v___x_3240_, v___x_3241_, v___x_2973_);
lean_inc_ref(v___y_3189_);
v___x_3243_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3189_, v_env_3219_, v___x_3242_);
v___y_3135_ = v___y_3179_;
v___y_3136_ = v___y_3178_;
v___y_3137_ = v___y_3181_;
v___y_3138_ = v___y_3180_;
v___y_3139_ = v___y_3182_;
v___y_3140_ = v___y_3183_;
v___y_3141_ = v___y_3184_;
v___y_3142_ = v___y_3186_;
v___y_3143_ = v___y_3185_;
v___y_3144_ = v___y_3187_;
v___y_3145_ = v___y_3188_;
v___y_3146_ = v___y_3201_;
v___y_3147_ = v___y_3190_;
v___y_3148_ = v___y_3191_;
v___y_3149_ = v___y_3192_;
v___y_3150_ = v___y_3193_;
v___y_3151_ = v___y_3194_;
v___y_3152_ = v___x_3230_;
v_nextMacroScope_3153_ = v_nextMacroScope_3220_;
v_ngen_3154_ = v_ngen_3221_;
v_auxDeclNGen_3155_ = v_auxDeclNGen_3222_;
v_traceState_3156_ = v_traceState_3223_;
v_messages_3157_ = v_messages_3224_;
v_infoState_3158_ = v_infoState_3225_;
v_snapshotTasks_3159_ = v_snapshotTasks_3226_;
v___y_3160_ = v___y_3195_;
v___y_3161_ = v___y_3196_;
v___y_3162_ = v___y_3198_;
v___y_3163_ = v___y_3199_;
v___y_3164_ = v___x_3243_;
goto v___jp_3134_;
}
}
}
}
}
v___jp_3248_:
{
if (v___y_3272_ == 0)
{
lean_object* v___x_3273_; lean_object* v_env_3274_; lean_object* v_nextMacroScope_3275_; lean_object* v_ngen_3276_; lean_object* v_auxDeclNGen_3277_; lean_object* v_traceState_3278_; lean_object* v_messages_3279_; lean_object* v_infoState_3280_; lean_object* v_snapshotTasks_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3290_; 
v___x_3273_ = lean_st_ref_take(v___y_3262_);
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
v___x_3285_ = l_Lean_Kernel_enableDiag(v_env_3274_, v___y_3271_);
lean_inc_ref(v___y_3261_);
if (v_isShared_3284_ == 0)
{
lean_ctor_set(v___x_3283_, 5, v___y_3261_);
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
lean_ctor_set(v_reuseFailAlloc_3289_, 5, v___y_3261_);
lean_ctor_set(v_reuseFailAlloc_3289_, 6, v_messages_3279_);
lean_ctor_set(v_reuseFailAlloc_3289_, 7, v_infoState_3280_);
lean_ctor_set(v_reuseFailAlloc_3289_, 8, v_snapshotTasks_3281_);
v___x_3287_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
lean_object* v___x_3288_; 
v___x_3288_ = lean_st_ref_put(v___y_3262_, v___x_3287_);
lean_inc(v___y_3262_);
v___y_3178_ = v___y_3250_;
v___y_3179_ = v___y_3249_;
v___y_3180_ = v___y_3252_;
v___y_3181_ = v___y_3251_;
v___y_3182_ = v___y_3253_;
v___y_3183_ = v___y_3254_;
v___y_3184_ = v___y_3255_;
v___y_3185_ = v___y_3257_;
v___y_3186_ = v___y_3256_;
v___y_3187_ = v___y_3258_;
v___y_3188_ = v___y_3259_;
v___y_3189_ = v___y_3260_;
v___y_3190_ = v___y_3261_;
v___y_3191_ = v___y_3263_;
v___y_3192_ = v___y_3262_;
v___y_3193_ = v___y_3264_;
v___y_3194_ = v___y_3265_;
v___y_3195_ = v___y_3267_;
v___y_3196_ = v___y_3268_;
v___y_3197_ = v___y_3271_;
v___y_3198_ = v___y_3270_;
v___y_3199_ = v___y_3269_;
v___y_3200_ = v___y_3266_;
v___y_3201_ = v___y_3262_;
goto v___jp_3177_;
}
}
}
else
{
lean_inc(v___y_3262_);
v___y_3178_ = v___y_3250_;
v___y_3179_ = v___y_3249_;
v___y_3180_ = v___y_3252_;
v___y_3181_ = v___y_3251_;
v___y_3182_ = v___y_3253_;
v___y_3183_ = v___y_3254_;
v___y_3184_ = v___y_3255_;
v___y_3185_ = v___y_3257_;
v___y_3186_ = v___y_3256_;
v___y_3187_ = v___y_3258_;
v___y_3188_ = v___y_3259_;
v___y_3189_ = v___y_3260_;
v___y_3190_ = v___y_3261_;
v___y_3191_ = v___y_3263_;
v___y_3192_ = v___y_3262_;
v___y_3193_ = v___y_3264_;
v___y_3194_ = v___y_3265_;
v___y_3195_ = v___y_3267_;
v___y_3196_ = v___y_3268_;
v___y_3197_ = v___y_3271_;
v___y_3198_ = v___y_3270_;
v___y_3199_ = v___y_3269_;
v___y_3200_ = v___y_3266_;
v___y_3201_ = v___y_3262_;
goto v___jp_3177_;
}
}
v___jp_3298_:
{
lean_object* v___x_3307_; 
if (v_isShared_2938_ == 0)
{
lean_ctor_set_tag(v___x_2937_, 0);
lean_ctor_set(v___x_2937_, 1, v___y_3305_);
lean_ctor_set(v___x_2937_, 0, v___y_3304_);
v___x_3307_ = v___x_2937_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v___y_3304_);
lean_ctor_set(v_reuseFailAlloc_3402_, 1, v___y_3305_);
v___x_3307_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v_moduleData_3311_; lean_object* v___x_3312_; uint8_t v___x_3313_; 
v___x_3308_ = lean_box(0);
lean_inc_ref(v___y_3303_);
v___x_3309_ = l_Lean_EnvExtension_setState___redArg(v___y_3303_, v___y_3301_, v___x_3307_, v___x_3308_);
v___x_3310_ = l_Lean_Environment_header(v___x_3309_);
v_moduleData_3311_ = lean_ctor_get(v___x_3310_, 6);
lean_inc_ref(v_moduleData_3311_);
lean_dec_ref(v___x_3310_);
v___x_3312_ = lean_array_get_size(v_moduleData_3311_);
v___x_3313_ = lean_nat_dec_lt(v___y_3300_, v___x_3312_);
if (v___x_3313_ == 0)
{
lean_object* v___x_3314_; lean_object* v___x_3315_; 
lean_dec_ref(v_moduleData_3311_);
lean_dec_ref(v___x_3309_);
lean_dec(v___y_3302_);
lean_dec(v___y_3300_);
lean_dec(v___y_3299_);
lean_dec_ref(v___x_2980_);
lean_del_object(v___x_2964_);
lean_dec(v_fst_2961_);
lean_dec(v_name_2950_);
lean_dec(v_head_2943_);
lean_del_object(v___x_2941_);
lean_dec(v_head_2939_);
v___x_3314_ = lean_obj_once(&l_main___closed__22, &l_main___closed__22_once, _init_l_main___closed__22);
v___x_3315_ = l_panic___at___00main_spec__5(v___x_3314_);
return v___x_3315_;
}
else
{
lean_object* v_base_3316_; lean_object* v_private_3317_; lean_object* v_header_3318_; lean_object* v_serverBaseExts_3319_; lean_object* v_checked_3320_; lean_object* v_asyncConstsMap_3321_; lean_object* v_asyncCtx_x3f_3322_; lean_object* v_importRealizationCtx_x3f_3323_; lean_object* v_localRealizationCtxMap_3324_; lean_object* v_allRealizations_3325_; uint8_t v_isExporting_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3400_; 
v_base_3316_ = lean_ctor_get(v___x_3309_, 0);
lean_inc_ref(v_base_3316_);
v_private_3317_ = lean_ctor_get(v_base_3316_, 0);
lean_inc(v_private_3317_);
v_header_3318_ = lean_ctor_get(v_private_3317_, 5);
lean_inc_ref(v_header_3318_);
v_serverBaseExts_3319_ = lean_ctor_get(v___x_3309_, 1);
v_checked_3320_ = lean_ctor_get(v___x_3309_, 2);
v_asyncConstsMap_3321_ = lean_ctor_get(v___x_3309_, 3);
v_asyncCtx_x3f_3322_ = lean_ctor_get(v___x_3309_, 4);
v_importRealizationCtx_x3f_3323_ = lean_ctor_get(v___x_3309_, 5);
v_localRealizationCtxMap_3324_ = lean_ctor_get(v___x_3309_, 6);
v_allRealizations_3325_ = lean_ctor_get(v___x_3309_, 7);
v_isExporting_3326_ = lean_ctor_get_uint8(v___x_3309_, sizeof(void*)*8);
v_isSharedCheck_3400_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3400_ == 0)
{
lean_object* v_unused_3401_; 
v_unused_3401_ = lean_ctor_get(v___x_3309_, 0);
lean_dec(v_unused_3401_);
v___x_3328_ = v___x_3309_;
v_isShared_3329_ = v_isSharedCheck_3400_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_allRealizations_3325_);
lean_inc(v_localRealizationCtxMap_3324_);
lean_inc(v_importRealizationCtx_x3f_3323_);
lean_inc(v_asyncCtx_x3f_3322_);
lean_inc(v_asyncConstsMap_3321_);
lean_inc(v_checked_3320_);
lean_inc(v_serverBaseExts_3319_);
lean_dec(v___x_3309_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3400_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v_public_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3398_; 
v_public_3330_ = lean_ctor_get(v_base_3316_, 1);
v_isSharedCheck_3398_ = !lean_is_exclusive(v_base_3316_);
if (v_isSharedCheck_3398_ == 0)
{
lean_object* v_unused_3399_; 
v_unused_3399_ = lean_ctor_get(v_base_3316_, 0);
lean_dec(v_unused_3399_);
v___x_3332_ = v_base_3316_;
v_isShared_3333_ = v_isSharedCheck_3398_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_public_3330_);
lean_dec(v_base_3316_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3398_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v_constants_3334_; uint8_t v_quotInit_3335_; lean_object* v_diagnostics_3336_; lean_object* v_const2ModIdx_3337_; lean_object* v_extensions_3338_; lean_object* v_irBaseExts_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3396_; 
v_constants_3334_ = lean_ctor_get(v_private_3317_, 0);
v_quotInit_3335_ = lean_ctor_get_uint8(v_private_3317_, sizeof(void*)*6);
v_diagnostics_3336_ = lean_ctor_get(v_private_3317_, 1);
v_const2ModIdx_3337_ = lean_ctor_get(v_private_3317_, 2);
v_extensions_3338_ = lean_ctor_get(v_private_3317_, 3);
v_irBaseExts_3339_ = lean_ctor_get(v_private_3317_, 4);
v_isSharedCheck_3396_ = !lean_is_exclusive(v_private_3317_);
if (v_isSharedCheck_3396_ == 0)
{
lean_object* v_unused_3397_; 
v_unused_3397_ = lean_ctor_get(v_private_3317_, 5);
lean_dec(v_unused_3397_);
v___x_3341_ = v_private_3317_;
v_isShared_3342_ = v_isSharedCheck_3396_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_irBaseExts_3339_);
lean_inc(v_extensions_3338_);
lean_inc(v_const2ModIdx_3337_);
lean_inc(v_diagnostics_3336_);
lean_inc(v_constants_3334_);
lean_dec(v_private_3317_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3396_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
uint32_t v_trustLevel_3343_; lean_object* v_mainModule_3344_; uint8_t v_isModule_3345_; lean_object* v_regions_3346_; lean_object* v_modules_3347_; lean_object* v_moduleName2Idx_3348_; lean_object* v_importAllModules_3349_; lean_object* v_moduleData_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3394_; 
v_trustLevel_3343_ = lean_ctor_get_uint32(v_header_3318_, sizeof(void*)*7);
v_mainModule_3344_ = lean_ctor_get(v_header_3318_, 0);
v_isModule_3345_ = lean_ctor_get_uint8(v_header_3318_, sizeof(void*)*7 + 4);
v_regions_3346_ = lean_ctor_get(v_header_3318_, 2);
v_modules_3347_ = lean_ctor_get(v_header_3318_, 3);
v_moduleName2Idx_3348_ = lean_ctor_get(v_header_3318_, 4);
v_importAllModules_3349_ = lean_ctor_get(v_header_3318_, 5);
v_moduleData_3350_ = lean_ctor_get(v_header_3318_, 6);
v_isSharedCheck_3394_ = !lean_is_exclusive(v_header_3318_);
if (v_isSharedCheck_3394_ == 0)
{
lean_object* v_unused_3395_; 
v_unused_3395_ = lean_ctor_get(v_header_3318_, 1);
lean_dec(v_unused_3395_);
v___x_3352_ = v_header_3318_;
v_isShared_3353_ = v_isSharedCheck_3394_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_moduleData_3350_);
lean_inc(v_importAllModules_3349_);
lean_inc(v_moduleName2Idx_3348_);
lean_inc(v_modules_3347_);
lean_inc(v_regions_3346_);
lean_inc(v_mainModule_3344_);
lean_dec(v_header_3318_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3394_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3354_; lean_object* v_imports_3355_; lean_object* v___x_3357_; 
v___x_3354_ = lean_array_fget(v_moduleData_3311_, v___y_3300_);
lean_dec_ref(v_moduleData_3311_);
v_imports_3355_ = lean_ctor_get(v___x_3354_, 0);
lean_inc_ref(v_imports_3355_);
lean_dec(v___x_3354_);
if (v_isShared_3353_ == 0)
{
lean_ctor_set(v___x_3352_, 1, v_imports_3355_);
v___x_3357_ = v___x_3352_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 7, 5);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_mainModule_3344_);
lean_ctor_set(v_reuseFailAlloc_3393_, 1, v_imports_3355_);
lean_ctor_set(v_reuseFailAlloc_3393_, 2, v_regions_3346_);
lean_ctor_set(v_reuseFailAlloc_3393_, 3, v_modules_3347_);
lean_ctor_set(v_reuseFailAlloc_3393_, 4, v_moduleName2Idx_3348_);
lean_ctor_set(v_reuseFailAlloc_3393_, 5, v_importAllModules_3349_);
lean_ctor_set(v_reuseFailAlloc_3393_, 6, v_moduleData_3350_);
lean_ctor_set_uint32(v_reuseFailAlloc_3393_, sizeof(void*)*7, v_trustLevel_3343_);
lean_ctor_set_uint8(v_reuseFailAlloc_3393_, sizeof(void*)*7 + 4, v_isModule_3345_);
v___x_3357_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
lean_object* v___x_3359_; 
if (v_isShared_3342_ == 0)
{
lean_ctor_set(v___x_3341_, 5, v___x_3357_);
v___x_3359_ = v___x_3341_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_constants_3334_);
lean_ctor_set(v_reuseFailAlloc_3392_, 1, v_diagnostics_3336_);
lean_ctor_set(v_reuseFailAlloc_3392_, 2, v_const2ModIdx_3337_);
lean_ctor_set(v_reuseFailAlloc_3392_, 3, v_extensions_3338_);
lean_ctor_set(v_reuseFailAlloc_3392_, 4, v_irBaseExts_3339_);
lean_ctor_set(v_reuseFailAlloc_3392_, 5, v___x_3357_);
lean_ctor_set_uint8(v_reuseFailAlloc_3392_, sizeof(void*)*6, v_quotInit_3335_);
v___x_3359_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
lean_object* v___x_3361_; 
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 0, v___x_3359_);
v___x_3361_ = v___x_3332_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v___x_3359_);
lean_ctor_set(v_reuseFailAlloc_3391_, 1, v_public_3330_);
v___x_3361_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
lean_object* v___x_3363_; 
if (v_isShared_3329_ == 0)
{
lean_ctor_set(v___x_3328_, 0, v___x_3361_);
v___x_3363_ = v___x_3328_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v___x_3361_);
lean_ctor_set(v_reuseFailAlloc_3390_, 1, v_serverBaseExts_3319_);
lean_ctor_set(v_reuseFailAlloc_3390_, 2, v_checked_3320_);
lean_ctor_set(v_reuseFailAlloc_3390_, 3, v_asyncConstsMap_3321_);
lean_ctor_set(v_reuseFailAlloc_3390_, 4, v_asyncCtx_x3f_3322_);
lean_ctor_set(v_reuseFailAlloc_3390_, 5, v_importRealizationCtx_x3f_3323_);
lean_ctor_set(v_reuseFailAlloc_3390_, 6, v_localRealizationCtxMap_3324_);
lean_ctor_set(v_reuseFailAlloc_3390_, 7, v_allRealizations_3325_);
lean_ctor_set_uint8(v_reuseFailAlloc_3390_, sizeof(void*)*8, v_isExporting_3326_);
v___x_3363_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v_env_3386_; lean_object* v___x_3387_; uint8_t v___x_3388_; uint8_t v___x_3389_; 
v___x_3364_ = l_Lean_Compiler_LCNF_postponedCompileDeclsExt;
v___x_3365_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2974_, v___x_3364_, v___x_3363_, v___y_3300_, v___x_3297_);
lean_dec(v___y_3300_);
v___x_3366_ = l_Lean_firstFrontendMacroScope;
v___x_3367_ = lean_obj_once(&l_main___closed__23, &l_main___closed__23_once, _init_l_main___closed__23);
v___x_3368_ = ((lean_object*)(l_main___closed__26));
lean_inc_n(v___y_3302_, 3);
v___x_3369_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3369_, 0, v___y_3302_);
lean_ctor_set(v___x_3369_, 1, v___x_3294_);
lean_ctor_set(v___x_3369_, 2, v___x_2967_);
v___x_3370_ = lean_obj_once(&l_main___closed__27, &l_main___closed__27_once, _init_l_main___closed__27);
v___x_3371_ = lean_obj_once(&l_main___closed__30, &l_main___closed__30_once, _init_l_main___closed__30);
v___x_3372_ = lean_obj_once(&l_main___closed__31, &l_main___closed__31_once, _init_l_main___closed__31);
v___x_3373_ = lean_obj_once(&l_main___closed__32, &l_main___closed__32_once, _init_l_main___closed__32);
v___x_3374_ = ((lean_object*)(l_main___closed__33));
lean_inc_ref(v___x_3369_);
v___x_3375_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3363_);
lean_ctor_set(v___x_3375_, 1, v___x_3367_);
lean_ctor_set(v___x_3375_, 2, v___x_3368_);
lean_ctor_set(v___x_3375_, 3, v___x_3369_);
lean_ctor_set(v___x_3375_, 4, v___x_3370_);
lean_ctor_set(v___x_3375_, 5, v___x_3371_);
lean_ctor_set(v___x_3375_, 6, v___x_3372_);
lean_ctor_set(v___x_3375_, 7, v___x_3373_);
lean_ctor_set(v___x_3375_, 8, v___x_3374_);
v___x_3376_ = lean_st_mk_ref(v___x_3375_);
v___x_3377_ = l_Lean_inheritedTraceOptions;
v___x_3378_ = lean_st_ref_get(v___x_3377_);
v___x_3379_ = lean_st_ref_get(v___x_3376_);
v___x_3380_ = l_Lean_instInhabitedFileMap_default;
v___x_3381_ = lean_unsigned_to_nat(1000u);
v___x_3382_ = lean_box(0);
v___x_3383_ = l_Lean_Core_getMaxHeartbeats(v___x_2980_);
v___x_3384_ = lean_box(0);
lean_inc_ref(v___x_2980_);
lean_inc(v_head_2939_);
v___x_3385_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3385_, 0, v_head_2939_);
lean_ctor_set(v___x_3385_, 1, v___x_3380_);
lean_ctor_set(v___x_3385_, 2, v___x_2980_);
lean_ctor_set(v___x_3385_, 3, v___x_2979_);
lean_ctor_set(v___x_3385_, 4, v___x_3381_);
lean_ctor_set(v___x_3385_, 5, v___x_3382_);
lean_ctor_set(v___x_3385_, 6, v___y_3302_);
lean_ctor_set(v___x_3385_, 7, v___x_2967_);
lean_ctor_set(v___x_3385_, 8, v___x_2979_);
lean_ctor_set(v___x_3385_, 9, v___x_3383_);
lean_ctor_set(v___x_3385_, 10, v___y_3302_);
lean_ctor_set(v___x_3385_, 11, v___x_3366_);
lean_ctor_set(v___x_3385_, 12, v___x_3384_);
lean_ctor_set(v___x_3385_, 13, v___x_3378_);
lean_ctor_set_uint8(v___x_3385_, sizeof(void*)*14, v___x_2953_);
lean_ctor_set_uint8(v___x_3385_, sizeof(void*)*14 + 1, v___x_2953_);
v_env_3386_ = lean_ctor_get(v___x_3379_, 0);
lean_inc_ref(v_env_3386_);
lean_dec(v___x_3379_);
v___x_3387_ = l_Lean_diagnostics;
v___x_3388_ = l_Lean_Option_get___at___00main_spec__8(v___x_2980_, v___x_3387_);
v___x_3389_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3386_);
lean_dec_ref(v_env_3386_);
if (v___x_3388_ == 0)
{
if (v___x_3389_ == 0)
{
v___y_3249_ = v___x_3377_;
v___y_3250_ = v___x_3313_;
v___y_3251_ = v___x_3380_;
v___y_3252_ = v___x_2967_;
v___y_3253_ = v___x_3384_;
v___y_3254_ = v___y_3299_;
v___y_3255_ = v___x_3366_;
v___y_3256_ = v___x_3371_;
v___y_3257_ = v___x_3382_;
v___y_3258_ = v___x_3374_;
v___y_3259_ = v___x_3367_;
v___y_3260_ = v___x_3364_;
v___y_3261_ = v___x_3371_;
v___y_3262_ = v___x_3376_;
v___y_3263_ = v___x_3372_;
v___y_3264_ = v___x_3373_;
v___y_3265_ = v___y_3302_;
v___y_3266_ = v___x_3385_;
v___y_3267_ = v___x_3365_;
v___y_3268_ = v___x_3370_;
v___y_3269_ = v___x_3369_;
v___y_3270_ = v___x_3368_;
v___y_3271_ = v___x_3388_;
v___y_3272_ = v___x_3313_;
goto v___jp_3248_;
}
else
{
v___y_3249_ = v___x_3377_;
v___y_3250_ = v___x_3313_;
v___y_3251_ = v___x_3380_;
v___y_3252_ = v___x_2967_;
v___y_3253_ = v___x_3384_;
v___y_3254_ = v___y_3299_;
v___y_3255_ = v___x_3366_;
v___y_3256_ = v___x_3371_;
v___y_3257_ = v___x_3382_;
v___y_3258_ = v___x_3374_;
v___y_3259_ = v___x_3367_;
v___y_3260_ = v___x_3364_;
v___y_3261_ = v___x_3371_;
v___y_3262_ = v___x_3376_;
v___y_3263_ = v___x_3372_;
v___y_3264_ = v___x_3373_;
v___y_3265_ = v___y_3302_;
v___y_3266_ = v___x_3385_;
v___y_3267_ = v___x_3365_;
v___y_3268_ = v___x_3370_;
v___y_3269_ = v___x_3369_;
v___y_3270_ = v___x_3368_;
v___y_3271_ = v___x_3388_;
v___y_3272_ = v___x_3388_;
goto v___jp_3248_;
}
}
else
{
v___y_3249_ = v___x_3377_;
v___y_3250_ = v___x_3313_;
v___y_3251_ = v___x_3380_;
v___y_3252_ = v___x_2967_;
v___y_3253_ = v___x_3384_;
v___y_3254_ = v___y_3299_;
v___y_3255_ = v___x_3366_;
v___y_3256_ = v___x_3371_;
v___y_3257_ = v___x_3382_;
v___y_3258_ = v___x_3374_;
v___y_3259_ = v___x_3367_;
v___y_3260_ = v___x_3364_;
v___y_3261_ = v___x_3371_;
v___y_3262_ = v___x_3376_;
v___y_3263_ = v___x_3372_;
v___y_3264_ = v___x_3373_;
v___y_3265_ = v___y_3302_;
v___y_3266_ = v___x_3385_;
v___y_3267_ = v___x_3365_;
v___y_3268_ = v___x_3370_;
v___y_3269_ = v___x_3369_;
v___y_3270_ = v___x_3368_;
v___y_3271_ = v___x_3388_;
v___y_3272_ = v___x_3389_;
goto v___jp_3248_;
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
v___jp_3403_:
{
lean_object* v___x_3408_; lean_object* v_toEnvExtension_3409_; lean_object* v_asyncMode_3410_; lean_object* v___x_3411_; lean_object* v_importedEntries_3412_; lean_object* v_state_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; uint8_t v___x_3416_; 
v___x_3408_ = l_Lean_IR_declMapExt;
v_toEnvExtension_3409_ = lean_ctor_get(v___x_3408_, 0);
v_asyncMode_3410_ = lean_ctor_get(v_toEnvExtension_3409_, 2);
lean_inc(v___y_3406_);
lean_inc_ref(v___y_3407_);
v___x_3411_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2971_, v_toEnvExtension_3409_, v___y_3407_, v_asyncMode_3410_, v___y_3406_);
v_importedEntries_3412_ = lean_ctor_get(v___x_3411_, 0);
lean_inc_ref(v_importedEntries_3412_);
v_state_3413_ = lean_ctor_get(v___x_3411_, 1);
lean_inc(v_state_3413_);
lean_dec(v___x_3411_);
v___x_3414_ = lean_array_get_borrowed(v___x_2972_, v_importedEntries_3412_, v___y_3405_);
v___x_3415_ = lean_array_get_size(v___x_3414_);
v___x_3416_ = lean_nat_dec_lt(v___x_2979_, v___x_3415_);
if (v___x_3416_ == 0)
{
v___y_3299_ = v___y_3404_;
v___y_3300_ = v___y_3405_;
v___y_3301_ = v___y_3407_;
v___y_3302_ = v___y_3406_;
v___y_3303_ = v_toEnvExtension_3409_;
v___y_3304_ = v_importedEntries_3412_;
v___y_3305_ = v_state_3413_;
goto v___jp_3298_;
}
else
{
uint8_t v___x_3417_; 
v___x_3417_ = lean_nat_dec_le(v___x_3415_, v___x_3415_);
if (v___x_3417_ == 0)
{
if (v___x_3416_ == 0)
{
v___y_3299_ = v___y_3404_;
v___y_3300_ = v___y_3405_;
v___y_3301_ = v___y_3407_;
v___y_3302_ = v___y_3406_;
v___y_3303_ = v_toEnvExtension_3409_;
v___y_3304_ = v_importedEntries_3412_;
v___y_3305_ = v_state_3413_;
goto v___jp_3298_;
}
else
{
size_t v___x_3418_; size_t v___x_3419_; lean_object* v___x_3420_; 
v___x_3418_ = ((size_t)0ULL);
v___x_3419_ = lean_usize_of_nat(v___x_3415_);
lean_inc_ref(v___y_3407_);
v___x_3420_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3407_, v___x_3414_, v___x_3418_, v___x_3419_, v_state_3413_);
v___y_3299_ = v___y_3404_;
v___y_3300_ = v___y_3405_;
v___y_3301_ = v___y_3407_;
v___y_3302_ = v___y_3406_;
v___y_3303_ = v_toEnvExtension_3409_;
v___y_3304_ = v_importedEntries_3412_;
v___y_3305_ = v___x_3420_;
goto v___jp_3298_;
}
}
else
{
size_t v___x_3421_; size_t v___x_3422_; lean_object* v___x_3423_; 
v___x_3421_ = ((size_t)0ULL);
v___x_3422_ = lean_usize_of_nat(v___x_3415_);
lean_inc_ref(v___y_3407_);
v___x_3423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3407_, v___x_3414_, v___x_3421_, v___x_3422_, v_state_3413_);
v___y_3299_ = v___y_3404_;
v___y_3300_ = v___y_3405_;
v___y_3301_ = v___y_3407_;
v___y_3302_ = v___y_3406_;
v___y_3303_ = v_toEnvExtension_3409_;
v___y_3304_ = v_importedEntries_3412_;
v___y_3305_ = v___x_3423_;
goto v___jp_3298_;
}
}
}
v___jp_3424_:
{
uint8_t v___x_3431_; 
v___x_3431_ = lean_nat_dec_lt(v___x_2979_, v___y_3429_);
if (v___x_3431_ == 0)
{
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
v___y_3404_ = v___y_3425_;
v___y_3405_ = v___y_3426_;
v___y_3406_ = v___y_3427_;
v___y_3407_ = v___y_3430_;
goto v___jp_3403_;
}
else
{
uint8_t v___x_3432_; 
v___x_3432_ = lean_nat_dec_le(v___y_3429_, v___y_3429_);
if (v___x_3432_ == 0)
{
if (v___x_3431_ == 0)
{
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
v___y_3404_ = v___y_3425_;
v___y_3405_ = v___y_3426_;
v___y_3406_ = v___y_3427_;
v___y_3407_ = v___y_3430_;
goto v___jp_3403_;
}
else
{
size_t v___x_3433_; size_t v___x_3434_; lean_object* v___x_3435_; 
v___x_3433_ = ((size_t)0ULL);
v___x_3434_ = lean_usize_of_nat(v___y_3429_);
lean_dec(v___y_3429_);
v___x_3435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3428_, v___x_3433_, v___x_3434_, v___y_3430_);
lean_dec_ref(v___y_3428_);
v___y_3404_ = v___y_3425_;
v___y_3405_ = v___y_3426_;
v___y_3406_ = v___y_3427_;
v___y_3407_ = v___x_3435_;
goto v___jp_3403_;
}
}
else
{
size_t v___x_3436_; size_t v___x_3437_; lean_object* v___x_3438_; 
v___x_3436_ = ((size_t)0ULL);
v___x_3437_ = lean_usize_of_nat(v___y_3429_);
lean_dec(v___y_3429_);
v___x_3438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3428_, v___x_3436_, v___x_3437_, v___y_3430_);
lean_dec_ref(v___y_3428_);
v___y_3404_ = v___y_3425_;
v___y_3405_ = v___y_3426_;
v___y_3406_ = v___y_3427_;
v___y_3407_ = v___x_3438_;
goto v___jp_3403_;
}
}
}
v___jp_3439_:
{
lean_object* v___x_3445_; uint8_t v___x_3446_; 
v___x_3445_ = lean_array_get_size(v___y_3444_);
v___x_3446_ = lean_nat_dec_lt(v___x_2979_, v___x_3445_);
if (v___x_3446_ == 0)
{
v___y_3425_ = v___y_3441_;
v___y_3426_ = v___y_3440_;
v___y_3427_ = v___y_3442_;
v___y_3428_ = v___y_3444_;
v___y_3429_ = v___x_3445_;
v___y_3430_ = v___y_3443_;
goto v___jp_3424_;
}
else
{
uint8_t v___x_3447_; 
v___x_3447_ = lean_nat_dec_le(v___x_3445_, v___x_3445_);
if (v___x_3447_ == 0)
{
if (v___x_3446_ == 0)
{
v___y_3425_ = v___y_3441_;
v___y_3426_ = v___y_3440_;
v___y_3427_ = v___y_3442_;
v___y_3428_ = v___y_3444_;
v___y_3429_ = v___x_3445_;
v___y_3430_ = v___y_3443_;
goto v___jp_3424_;
}
else
{
size_t v___x_3448_; size_t v___x_3449_; lean_object* v___x_3450_; 
v___x_3448_ = ((size_t)0ULL);
v___x_3449_ = lean_usize_of_nat(v___x_3445_);
v___x_3450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v___y_3444_, v___x_3448_, v___x_3449_, v___y_3443_);
v___y_3425_ = v___y_3441_;
v___y_3426_ = v___y_3440_;
v___y_3427_ = v___y_3442_;
v___y_3428_ = v___y_3444_;
v___y_3429_ = v___x_3445_;
v___y_3430_ = v___x_3450_;
goto v___jp_3424_;
}
}
else
{
size_t v___x_3451_; size_t v___x_3452_; lean_object* v___x_3453_; 
v___x_3451_ = ((size_t)0ULL);
v___x_3452_ = lean_usize_of_nat(v___x_3445_);
v___x_3453_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v___y_3444_, v___x_3451_, v___x_3452_, v___y_3443_);
v___y_3425_ = v___y_3441_;
v___y_3426_ = v___y_3440_;
v___y_3427_ = v___y_3442_;
v___y_3428_ = v___y_3444_;
v___y_3429_ = v___x_3445_;
v___y_3430_ = v___x_3453_;
goto v___jp_3424_;
}
}
}
v___jp_3455_:
{
lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___f_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3457_ = l_Lean_instInhabitedImportState_default;
v___x_3458_ = lean_box(v___x_3297_);
v___x_3459_ = lean_box(v___y_3456_);
v___x_3460_ = lean_box(v___x_2976_);
v___x_3461_ = lean_box(v___x_3454_);
v___x_3462_ = lean_box(v___x_2953_);
lean_inc_ref(v___x_2980_);
lean_inc(v_name_2950_);
v___f_3463_ = lean_alloc_closure((void*)(l_main___lam__0___boxed), 11, 10);
lean_closure_set(v___f_3463_, 0, v___x_3457_);
lean_closure_set(v___f_3463_, 1, v___x_3296_);
lean_closure_set(v___f_3463_, 2, v___x_3458_);
lean_closure_set(v___f_3463_, 3, v_importArts_2951_);
lean_closure_set(v___f_3463_, 4, v___x_3459_);
lean_closure_set(v___f_3463_, 5, v___x_3460_);
lean_closure_set(v___f_3463_, 6, v_name_2950_);
lean_closure_set(v___f_3463_, 7, v___x_3461_);
lean_closure_set(v___f_3463_, 8, v___x_2980_);
lean_closure_set(v___f_3463_, 9, v___x_3462_);
v___x_3464_ = lean_alloc_closure((void*)(l_Lean_withImporting___boxed), 3, 2);
lean_closure_set(v___x_3464_, 0, lean_box(0));
lean_closure_set(v___x_3464_, 1, v___f_3463_);
v___x_3465_ = lean_box(0);
v___x_3466_ = l_Lean_profileitIOUnsafe___redArg(v___x_3292_, v___x_2980_, v___x_3464_, v___x_3465_);
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_object* v_a_3467_; lean_object* v___x_3468_; lean_object* v_ext_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; 
v_a_3467_ = lean_ctor_get(v___x_3466_, 0);
lean_inc(v_a_3467_);
lean_dec_ref_known(v___x_3466_, 1);
v___x_3468_ = l_Lean_Compiler_CSimp_ext;
v_ext_3469_ = lean_ctor_get(v___x_3468_, 1);
lean_inc(v_name_2950_);
v___x_3470_ = l_Lean_Environment_setMainModule(v_a_3467_, v_name_2950_);
lean_inc_ref(v_ext_3469_);
v___x_3471_ = l_main___elam__0___redArg(v___x_3465_, v___x_2966_, v_ext_3469_, v___x_3470_);
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_object* v_a_3472_; lean_object* v___x_3473_; lean_object* v_ext_3474_; lean_object* v___x_3475_; 
v_a_3472_ = lean_ctor_get(v___x_3471_, 0);
lean_inc(v_a_3472_);
lean_dec_ref_known(v___x_3471_, 1);
v___x_3473_ = l_Lean_Meta_instanceExtension;
v_ext_3474_ = lean_ctor_get(v___x_3473_, 1);
lean_inc_ref(v_ext_3474_);
v___x_3475_ = l_main___elam__0___redArg(v___x_3465_, v___x_2966_, v_ext_3474_, v_a_3472_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_object* v_a_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; 
v_a_3476_ = lean_ctor_get(v___x_3475_, 0);
lean_inc(v_a_3476_);
lean_dec_ref_known(v___x_3475_, 1);
v___x_3477_ = l_Lean_classExtension;
v___x_3478_ = l_main___elam__0___redArg(v___x_3465_, v___x_2968_, v___x_3477_, v_a_3476_);
if (lean_obj_tag(v___x_3478_) == 0)
{
lean_object* v_a_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; 
v_a_3479_ = lean_ctor_get(v___x_3478_, 0);
lean_inc(v_a_3479_);
lean_dec_ref_known(v___x_3478_, 1);
v___x_3480_ = l_Lean_Meta_Match_Extension_extension;
v___x_3481_ = l_main___elam__0___redArg(v___x_3465_, v___x_2969_, v___x_3480_, v_a_3479_);
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3509_; 
v_a_3482_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3484_ = v___x_3481_;
v_isShared_3485_ = v_isSharedCheck_3509_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3481_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3509_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3486_; 
v___x_3486_ = l_Lean_Environment_getModuleIdx_x3f(v_a_3482_, v_name_2950_);
if (lean_obj_tag(v___x_3486_) == 1)
{
lean_object* v_val_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; uint8_t v___x_3492_; 
lean_del_object(v___x_3484_);
v_val_3487_ = lean_ctor_get(v___x_3486_, 0);
lean_inc(v_val_3487_);
lean_dec_ref_known(v___x_3486_, 1);
v___x_3488_ = l_Lean_Compiler_LCNF_impureSigExt;
v___x_3489_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2970_, v___x_3488_, v_a_3482_, v_val_3487_, v___x_3297_);
v___x_3490_ = lean_array_get_size(v___x_3489_);
v___x_3491_ = ((lean_object*)(l_main___closed__34));
v___x_3492_ = lean_nat_dec_lt(v___x_2979_, v___x_3490_);
if (v___x_3492_ == 0)
{
lean_dec_ref(v___x_3489_);
v___y_3440_ = v_val_3487_;
v___y_3441_ = v___x_3465_;
v___y_3442_ = v___x_3465_;
v___y_3443_ = v_a_3482_;
v___y_3444_ = v___x_3491_;
goto v___jp_3439_;
}
else
{
uint8_t v___x_3493_; 
v___x_3493_ = lean_nat_dec_le(v___x_3490_, v___x_3490_);
if (v___x_3493_ == 0)
{
if (v___x_3492_ == 0)
{
lean_dec_ref(v___x_3489_);
v___y_3440_ = v_val_3487_;
v___y_3441_ = v___x_3465_;
v___y_3442_ = v___x_3465_;
v___y_3443_ = v_a_3482_;
v___y_3444_ = v___x_3491_;
goto v___jp_3439_;
}
else
{
size_t v___x_3494_; size_t v___x_3495_; lean_object* v___x_3496_; 
v___x_3494_ = ((size_t)0ULL);
v___x_3495_ = lean_usize_of_nat(v___x_3490_);
lean_inc(v_a_3482_);
v___x_3496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_3482_, v___x_3489_, v___x_3494_, v___x_3495_, v___x_3491_);
lean_dec_ref(v___x_3489_);
v___y_3440_ = v_val_3487_;
v___y_3441_ = v___x_3465_;
v___y_3442_ = v___x_3465_;
v___y_3443_ = v_a_3482_;
v___y_3444_ = v___x_3496_;
goto v___jp_3439_;
}
}
else
{
size_t v___x_3497_; size_t v___x_3498_; lean_object* v___x_3499_; 
v___x_3497_ = ((size_t)0ULL);
v___x_3498_ = lean_usize_of_nat(v___x_3490_);
lean_inc(v_a_3482_);
v___x_3499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_3482_, v___x_3489_, v___x_3497_, v___x_3498_, v___x_3491_);
lean_dec_ref(v___x_3489_);
v___y_3440_ = v_val_3487_;
v___y_3441_ = v___x_3465_;
v___y_3442_ = v___x_3465_;
v___y_3443_ = v_a_3482_;
v___y_3444_ = v___x_3499_;
goto v___jp_3439_;
}
}
}
else
{
lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3507_; 
lean_dec(v___x_3486_);
lean_dec(v_a_3482_);
lean_dec_ref(v___x_2980_);
lean_del_object(v___x_2964_);
lean_dec(v_fst_2961_);
lean_dec(v_head_2943_);
lean_del_object(v___x_2941_);
lean_dec(v_head_2939_);
lean_del_object(v___x_2937_);
v___x_3500_ = ((lean_object*)(l_main___closed__35));
v___x_3501_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2950_, v___x_2976_);
v___x_3502_ = lean_string_append(v___x_3500_, v___x_3501_);
lean_dec_ref(v___x_3501_);
v___x_3503_ = ((lean_object*)(l_main___closed__36));
v___x_3504_ = lean_string_append(v___x_3502_, v___x_3503_);
v___x_3505_ = lean_mk_io_user_error(v___x_3504_);
if (v_isShared_3485_ == 0)
{
lean_ctor_set_tag(v___x_3484_, 1);
lean_ctor_set(v___x_3484_, 0, v___x_3505_);
v___x_3507_ = v___x_3484_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___x_3505_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
}
else
{
lean_object* v_a_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3517_; 
lean_dec_ref(v___x_2980_);
lean_del_object(v___x_2964_);
lean_dec(v_fst_2961_);
lean_dec(v_name_2950_);
lean_dec(v_head_2943_);
lean_del_object(v___x_2941_);
lean_dec(v_head_2939_);
lean_del_object(v___x_2937_);
v_a_3510_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3512_ = v___x_3481_;
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3481_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3515_; 
if (v_isShared_3513_ == 0)
{
v___x_3515_ = v___x_3512_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3510_);
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
else
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3525_; 
lean_dec_ref(v___x_2980_);
lean_del_object(v___x_2964_);
lean_dec(v_fst_2961_);
lean_dec(v_name_2950_);
lean_dec(v_head_2943_);
lean_del_object(v___x_2941_);
lean_dec(v_head_2939_);
lean_del_object(v___x_2937_);
v_a_3518_ = lean_ctor_get(v___x_3478_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3478_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3520_ = v___x_3478_;
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3478_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3523_; 
if (v_isShared_3521_ == 0)
{
v___x_3523_ = v___x_3520_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3518_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
}
else
{
lean_object* v_a_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3533_; 
lean_dec_ref(v___x_2980_);
lean_del_object(v___x_2964_);
lean_dec(v_fst_2961_);
lean_dec(v_name_2950_);
lean_dec(v_head_2943_);
lean_del_object(v___x_2941_);
lean_dec(v_head_2939_);
lean_del_object(v___x_2937_);
v_a_3526_ = lean_ctor_get(v___x_3475_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3528_ = v___x_3475_;
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v___x_3475_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3531_; 
if (v_isShared_3529_ == 0)
{
v___x_3531_ = v___x_3528_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_a_3526_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
}
else
{
lean_object* v_a_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3541_; 
lean_dec_ref(v___x_2980_);
lean_del_object(v___x_2964_);
lean_dec(v_fst_2961_);
lean_dec(v_name_2950_);
lean_dec(v_head_2943_);
lean_del_object(v___x_2941_);
lean_dec(v_head_2939_);
lean_del_object(v___x_2937_);
v_a_3534_ = lean_ctor_get(v___x_3471_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3536_ = v___x_3471_;
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_a_3534_);
lean_dec(v___x_3471_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3539_; 
if (v_isShared_3537_ == 0)
{
v___x_3539_ = v___x_3536_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_a_3534_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
}
}
}
}
else
{
lean_object* v_a_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3549_; 
lean_dec_ref(v___x_2980_);
lean_del_object(v___x_2964_);
lean_dec(v_fst_2961_);
lean_dec(v_name_2950_);
lean_dec(v_head_2943_);
lean_del_object(v___x_2941_);
lean_dec(v_head_2939_);
lean_del_object(v___x_2937_);
v_a_3542_ = lean_ctor_get(v___x_3466_, 0);
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3544_ = v___x_3466_;
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_a_3542_);
lean_dec(v___x_3466_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v___x_3547_; 
if (v_isShared_3545_ == 0)
{
v___x_3547_ = v___x_3544_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_a_3542_);
v___x_3547_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
return v___x_3547_;
}
}
}
}
}
}
else
{
lean_object* v_a_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3559_; 
lean_dec(v_a_2959_);
lean_dec(v_importArts_2951_);
lean_dec(v_name_2950_);
lean_dec(v_head_2943_);
lean_del_object(v___x_2941_);
lean_dec(v_head_2939_);
lean_del_object(v___x_2937_);
v_a_3552_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_3559_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_3559_ == 0)
{
v___x_3554_ = v___x_2960_;
v_isShared_3555_ = v_isSharedCheck_3559_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_a_3552_);
lean_dec(v___x_2960_);
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
}
else
{
lean_object* v_a_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3567_; 
lean_dec(v_importArts_2951_);
lean_dec(v_name_2950_);
lean_dec(v_head_2943_);
lean_del_object(v___x_2941_);
lean_dec(v_head_2939_);
lean_del_object(v___x_2937_);
v_a_3560_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_3567_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_3567_ == 0)
{
v___x_3562_ = v___x_2958_;
v_isShared_3563_ = v_isSharedCheck_3567_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_a_3560_);
lean_dec(v___x_2958_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3567_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v___x_3565_; 
if (v_isShared_3563_ == 0)
{
v___x_3565_ = v___x_3562_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v_a_3560_);
v___x_3565_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
return v___x_3565_;
}
}
}
}
}
else
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
lean_del_object(v___x_2946_);
lean_dec(v_tail_2944_);
lean_dec(v_head_2943_);
lean_del_object(v___x_2941_);
lean_dec(v_head_2939_);
lean_del_object(v___x_2937_);
v_a_3569_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_2948_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_2948_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
if (v_isShared_3572_ == 0)
{
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3569_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_tail_2933_, 2);
lean_dec(v_tail_2934_);
lean_dec_ref_known(v_args_2908_, 2);
goto v___jp_2910_;
}
}
else
{
lean_dec_ref_known(v_args_2908_, 2);
lean_dec(v_tail_2933_);
goto v___jp_2910_;
}
}
else
{
lean_dec(v_args_2908_);
goto v___jp_2910_;
}
v___jp_2910_:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2911_ = ((lean_object*)(l_main___closed__0));
v___x_2912_ = l_IO_println___at___00Lean_Environment_displayStats_spec__1(v___x_2911_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2920_; 
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2920_ == 0)
{
lean_object* v_unused_2921_; 
v_unused_2921_ = lean_ctor_get(v___x_2912_, 0);
lean_dec(v_unused_2921_);
v___x_2914_ = v___x_2912_;
v_isShared_2915_ = v_isSharedCheck_2920_;
goto v_resetjp_2913_;
}
else
{
lean_dec(v___x_2912_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2920_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2916_; lean_object* v___x_2918_; 
v___x_2916_ = l_main___boxed__const__1;
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 0, v___x_2916_);
v___x_2918_ = v___x_2914_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v___x_2916_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
else
{
lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
v_a_2922_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2924_ = v___x_2912_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2912_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2922_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
}
v___jp_2930_:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2931_ = l_main___boxed__const__2;
v___x_2932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2931_);
return v___x_2932_;
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_3582_, lean_object* v_a_3583_){
_start:
{
lean_object* v_res_3584_; 
v_res_3584_ = _lean_main(v_args_3582_);
return v_res_3584_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1(lean_object* v_as_3585_, lean_object* v_as_x27_3586_, lean_object* v_b_3587_, lean_object* v_a_3588_){
_start:
{
lean_object* v___x_3590_; 
v___x_3590_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_3586_, v_b_3587_);
return v___x_3590_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___boxed(lean_object* v_as_3591_, lean_object* v_as_x27_3592_, lean_object* v_b_3593_, lean_object* v_a_3594_, lean_object* v___y_3595_){
_start:
{
lean_object* v_res_3596_; 
v_res_3596_ = l_List_forIn_x27_loop___at___00main_spec__1(v_as_3591_, v_as_x27_3592_, v_b_3593_, v_a_3594_);
lean_dec(v_as_x27_3592_);
lean_dec(v_as_3591_);
return v_res_3596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16(lean_object* v___y_3597_, lean_object* v___y_3598_){
_start:
{
lean_object* v___x_3600_; 
v___x_3600_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_3598_);
return v___x_3600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___boxed(lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16(v___y_3601_, v___y_3602_);
lean_dec(v___y_3602_);
lean_dec_ref(v___y_3601_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17(lean_object* v_00_u03b2_3605_, lean_object* v_m_3606_, lean_object* v_a_3607_, lean_object* v_fallback_3608_){
_start:
{
lean_object* v___x_3609_; 
v___x_3609_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_m_3606_, v_a_3607_, v_fallback_3608_);
return v___x_3609_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___boxed(lean_object* v_00_u03b2_3610_, lean_object* v_m_3611_, lean_object* v_a_3612_, lean_object* v_fallback_3613_){
_start:
{
lean_object* v_res_3614_; 
v_res_3614_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17(v_00_u03b2_3610_, v_m_3611_, v_a_3612_, v_fallback_3613_);
lean_dec(v_fallback_3613_);
lean_dec_ref(v_a_3612_);
lean_dec_ref(v_m_3611_);
return v_res_3614_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18(lean_object* v_00_u03b2_3615_, lean_object* v_m_3616_, lean_object* v_a_3617_, lean_object* v_b_3618_){
_start:
{
lean_object* v___x_3619_; 
v___x_3619_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_m_3616_, v_a_3617_, v_b_3618_);
return v___x_3619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21(lean_object* v_n_3620_, lean_object* v_as_3621_, lean_object* v_lo_3622_, lean_object* v_hi_3623_, lean_object* v_w_3624_, lean_object* v_hlo_3625_, lean_object* v_hhi_3626_){
_start:
{
lean_object* v___x_3627_; 
v___x_3627_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_3620_, v_as_3621_, v_lo_3622_, v_hi_3623_);
return v___x_3627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___boxed(lean_object* v_n_3628_, lean_object* v_as_3629_, lean_object* v_lo_3630_, lean_object* v_hi_3631_, lean_object* v_w_3632_, lean_object* v_hlo_3633_, lean_object* v_hhi_3634_){
_start:
{
lean_object* v_res_3635_; 
v_res_3635_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21(v_n_3628_, v_as_3629_, v_lo_3630_, v_hi_3631_, v_w_3632_, v_hlo_3633_, v_hhi_3634_);
lean_dec(v_hi_3631_);
lean_dec(v_n_3628_);
return v_res_3635_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21(lean_object* v_00_u03b2_3636_, lean_object* v_a_3637_, lean_object* v_fallback_3638_, lean_object* v_x_3639_){
_start:
{
lean_object* v___x_3640_; 
v___x_3640_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_3637_, v_fallback_3638_, v_x_3639_);
return v___x_3640_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___boxed(lean_object* v_00_u03b2_3641_, lean_object* v_a_3642_, lean_object* v_fallback_3643_, lean_object* v_x_3644_){
_start:
{
lean_object* v_res_3645_; 
v_res_3645_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21(v_00_u03b2_3641_, v_a_3642_, v_fallback_3643_, v_x_3644_);
lean_dec(v_x_3644_);
lean_dec(v_fallback_3643_);
lean_dec_ref(v_a_3642_);
return v_res_3645_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23(lean_object* v_00_u03b2_3646_, lean_object* v_a_3647_, lean_object* v_x_3648_){
_start:
{
uint8_t v___x_3649_; 
v___x_3649_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_3647_, v_x_3648_);
return v___x_3649_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___boxed(lean_object* v_00_u03b2_3650_, lean_object* v_a_3651_, lean_object* v_x_3652_){
_start:
{
uint8_t v_res_3653_; lean_object* v_r_3654_; 
v_res_3653_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23(v_00_u03b2_3650_, v_a_3651_, v_x_3652_);
lean_dec(v_x_3652_);
lean_dec_ref(v_a_3651_);
v_r_3654_ = lean_box(v_res_3653_);
return v_r_3654_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24(lean_object* v_00_u03b2_3655_, lean_object* v_data_3656_){
_start:
{
lean_object* v___x_3657_; 
v___x_3657_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(v_data_3656_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25(lean_object* v_00_u03b2_3658_, lean_object* v_a_3659_, lean_object* v_b_3660_, lean_object* v_x_3661_){
_start:
{
lean_object* v___x_3662_; 
v___x_3662_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_3659_, v_b_3660_, v_x_3661_);
return v___x_3662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31(lean_object* v_n_3663_, lean_object* v_lo_3664_, lean_object* v_hi_3665_, lean_object* v_hhi_3666_, lean_object* v_pivot_3667_, lean_object* v_as_3668_, lean_object* v_i_3669_, lean_object* v_k_3670_, lean_object* v_ilo_3671_, lean_object* v_ik_3672_, lean_object* v_w_3673_){
_start:
{
lean_object* v___x_3674_; 
v___x_3674_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_3665_, v_pivot_3667_, v_as_3668_, v_i_3669_, v_k_3670_);
return v___x_3674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___boxed(lean_object* v_n_3675_, lean_object* v_lo_3676_, lean_object* v_hi_3677_, lean_object* v_hhi_3678_, lean_object* v_pivot_3679_, lean_object* v_as_3680_, lean_object* v_i_3681_, lean_object* v_k_3682_, lean_object* v_ilo_3683_, lean_object* v_ik_3684_, lean_object* v_w_3685_){
_start:
{
lean_object* v_res_3686_; 
v_res_3686_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31(v_n_3675_, v_lo_3676_, v_hi_3677_, v_hhi_3678_, v_pivot_3679_, v_as_3680_, v_i_3681_, v_k_3682_, v_ilo_3683_, v_ik_3684_, v_w_3685_);
lean_dec_ref(v_pivot_3679_);
lean_dec(v_hi_3677_);
lean_dec(v_lo_3676_);
lean_dec(v_n_3675_);
return v_res_3686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40(lean_object* v_as_3687_, size_t v_sz_3688_, size_t v_i_3689_, lean_object* v_b_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_){
_start:
{
lean_object* v___x_3694_; 
v___x_3694_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_3687_, v_sz_3688_, v_i_3689_, v_b_3690_, v___y_3691_);
return v___x_3694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___boxed(lean_object* v_as_3695_, lean_object* v_sz_3696_, lean_object* v_i_3697_, lean_object* v_b_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_){
_start:
{
size_t v_sz_boxed_3702_; size_t v_i_boxed_3703_; lean_object* v_res_3704_; 
v_sz_boxed_3702_ = lean_unbox_usize(v_sz_3696_);
lean_dec(v_sz_3696_);
v_i_boxed_3703_ = lean_unbox_usize(v_i_3697_);
lean_dec(v_i_3697_);
v_res_3704_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40(v_as_3695_, v_sz_boxed_3702_, v_i_boxed_3703_, v_b_3698_, v___y_3699_, v___y_3700_);
lean_dec(v___y_3700_);
lean_dec_ref(v___y_3699_);
lean_dec_ref(v_as_3695_);
return v_res_3704_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35(lean_object* v_00_u03b2_3705_, lean_object* v_i_3706_, lean_object* v_source_3707_, lean_object* v_target_3708_){
_start:
{
lean_object* v___x_3709_; 
v___x_3709_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(v_i_3706_, v_source_3707_, v_target_3708_);
return v___x_3709_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42(uint8_t v___x_3710_, lean_object* v_as_3711_, size_t v_sz_3712_, size_t v_i_3713_, lean_object* v_b_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_){
_start:
{
lean_object* v___x_3718_; 
v___x_3718_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_3710_, v_as_3711_, v_sz_3712_, v_i_3713_, v_b_3714_, v___y_3715_);
return v___x_3718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___boxed(lean_object* v___x_3719_, lean_object* v_as_3720_, lean_object* v_sz_3721_, lean_object* v_i_3722_, lean_object* v_b_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_){
_start:
{
uint8_t v___x_40158__boxed_3727_; size_t v_sz_boxed_3728_; size_t v_i_boxed_3729_; lean_object* v_res_3730_; 
v___x_40158__boxed_3727_ = lean_unbox(v___x_3719_);
v_sz_boxed_3728_ = lean_unbox_usize(v_sz_3721_);
lean_dec(v_sz_3721_);
v_i_boxed_3729_ = lean_unbox_usize(v_i_3722_);
lean_dec(v_i_3722_);
v_res_3730_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42(v___x_40158__boxed_3727_, v_as_3720_, v_sz_boxed_3728_, v_i_boxed_3729_, v_b_3723_, v___y_3724_, v___y_3725_);
lean_dec(v___y_3725_);
lean_dec_ref(v___y_3724_);
lean_dec_ref(v_as_3720_);
return v_res_3730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51(lean_object* v_as_3731_, size_t v_sz_3732_, size_t v_i_3733_, lean_object* v_b_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_){
_start:
{
lean_object* v___x_3738_; 
v___x_3738_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_3731_, v_sz_3732_, v_i_3733_, v_b_3734_, v___y_3735_);
return v___x_3738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___boxed(lean_object* v_as_3739_, lean_object* v_sz_3740_, lean_object* v_i_3741_, lean_object* v_b_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_){
_start:
{
size_t v_sz_boxed_3746_; size_t v_i_boxed_3747_; lean_object* v_res_3748_; 
v_sz_boxed_3746_ = lean_unbox_usize(v_sz_3740_);
lean_dec(v_sz_3740_);
v_i_boxed_3747_ = lean_unbox_usize(v_i_3741_);
lean_dec(v_i_3741_);
v_res_3748_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51(v_as_3739_, v_sz_boxed_3746_, v_i_boxed_3747_, v_b_3742_, v___y_3743_, v___y_3744_);
lean_dec(v___y_3744_);
lean_dec_ref(v___y_3743_);
lean_dec_ref(v_as_3739_);
return v_res_3748_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44(lean_object* v_00_u03b2_3749_, lean_object* v_x_3750_, lean_object* v_x_3751_){
_start:
{
lean_object* v___x_3752_; 
v___x_3752_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(v_x_3750_, v_x_3751_);
return v___x_3752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49(uint8_t v___x_3753_, lean_object* v_as_3754_, size_t v_sz_3755_, size_t v_i_3756_, lean_object* v_b_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_){
_start:
{
lean_object* v___x_3761_; 
v___x_3761_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_3753_, v_as_3754_, v_sz_3755_, v_i_3756_, v_b_3757_, v___y_3758_);
return v___x_3761_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___boxed(lean_object* v___x_3762_, lean_object* v_as_3763_, lean_object* v_sz_3764_, lean_object* v_i_3765_, lean_object* v_b_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_){
_start:
{
uint8_t v___x_40189__boxed_3770_; size_t v_sz_boxed_3771_; size_t v_i_boxed_3772_; lean_object* v_res_3773_; 
v___x_40189__boxed_3770_ = lean_unbox(v___x_3762_);
v_sz_boxed_3771_ = lean_unbox_usize(v_sz_3764_);
lean_dec(v_sz_3764_);
v_i_boxed_3772_ = lean_unbox_usize(v_i_3765_);
lean_dec(v_i_3765_);
v_res_3773_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49(v___x_40189__boxed_3770_, v_as_3763_, v_sz_boxed_3771_, v_i_boxed_3772_, v_b_3766_, v___y_3767_, v___y_3768_);
lean_dec(v___y_3768_);
lean_dec_ref(v___y_3767_);
lean_dec_ref(v_as_3763_);
return v_res_3773_;
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
