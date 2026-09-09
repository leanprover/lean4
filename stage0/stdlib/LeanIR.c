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
LEAN_EXPORT lean_object* l_main___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
lean_object* v___x_359_; lean_object* v___x_18373__overap_360_; lean_object* v___x_361_; 
v___x_359_ = lean_obj_once(&l_panic___at___00main_spec__5___closed__0, &l_panic___at___00main_spec__5___closed__0_once, _init_l_panic___at___00main_spec__5___closed__0);
v___x_18373__overap_360_ = lean_panic_fn_borrowed(v___x_359_, v_msg_357_);
v___x_361_ = lean_apply_1(v___x_18373__overap_360_, lean_box(0));
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
uint8_t v___x_35144__boxed_512_; uint8_t v___y_35145__boxed_513_; uint8_t v___x_35146__boxed_514_; uint8_t v___x_35147__boxed_515_; uint8_t v___x_35149__boxed_516_; lean_object* v_res_517_; 
v___x_35144__boxed_512_ = lean_unbox(v___x_503_);
v___y_35145__boxed_513_ = lean_unbox(v___y_505_);
v___x_35146__boxed_514_ = lean_unbox(v___x_506_);
v___x_35147__boxed_515_ = lean_unbox(v___x_508_);
v___x_35149__boxed_516_ = lean_unbox(v___x_510_);
v_res_517_ = l_main___lam__0(v___x_501_, v___x_502_, v___x_35144__boxed_512_, v_importArts_504_, v___y_35145__boxed_513_, v___x_35146__boxed_514_, v_name_507_, v___x_35147__boxed_515_, v___x_509_, v___x_35149__boxed_516_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_main___lam__1(lean_object* v___x_521_, lean_object* v___x_522_, lean_object* v_head_523_, lean_object* v___x_524_, lean_object* v___x_525_, lean_object* v___x_526_, lean_object* v___x_527_, lean_object* v_name_528_, lean_object* v_a_529_, uint8_t v___x_530_, lean_object* v___x_531_, lean_object* v___x_532_, lean_object* v___x_533_, lean_object* v___x_534_, lean_object* v___x_535_, lean_object* v___x_536_, uint8_t v___x_537_){
_start:
{
lean_object* v_a_540_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v_env_547_; lean_object* v___x_548_; lean_object* v___x_549_; uint8_t v___x_550_; lean_object* v_toCold_552_; lean_object* v_currRecDepth_553_; lean_object* v_ref_554_; lean_object* v_currNamespace_555_; lean_object* v_openDecls_556_; lean_object* v_initHeartbeats_557_; lean_object* v_maxHeartbeats_558_; lean_object* v_currMacroScope_559_; uint8_t v_suppressElabErrors_560_; lean_object* v___y_561_; uint8_t v___y_593_; uint8_t v___x_613_; 
v___x_543_ = lean_io_get_num_heartbeats();
v___x_544_ = lean_st_mk_ref(v___x_521_);
v___x_545_ = lean_st_ref_get(v___x_522_);
v___x_546_ = lean_st_ref_get(v___x_544_);
v_env_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc_ref(v_env_547_);
lean_dec(v___x_546_);
lean_inc(v___x_525_);
v___x_548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_548_, 0, v_head_523_);
lean_ctor_set(v___x_548_, 1, v___x_524_);
lean_ctor_set(v___x_548_, 2, v___x_525_);
lean_ctor_set(v___x_548_, 3, v___x_526_);
lean_ctor_set(v___x_548_, 4, v___x_545_);
v___x_549_ = l_Lean_diagnostics;
v___x_550_ = l_Lean_Option_get___at___00main_spec__8(v___x_527_, v___x_549_);
v___x_613_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_547_);
lean_dec_ref(v_env_547_);
if (v___x_550_ == 0)
{
if (v___x_613_ == 0)
{
v___y_593_ = v___x_530_;
goto v___jp_592_;
}
else
{
v___y_593_ = v___x_550_;
goto v___jp_592_;
}
}
else
{
v___y_593_ = v___x_613_;
goto v___jp_592_;
}
v___jp_539_:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = lean_mk_io_user_error(v_a_540_);
v___x_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
return v___x_542_;
}
v___jp_551_:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_562_ = l_Lean_maxRecDepth;
v___x_563_ = l_Lean_Option_get___at___00main_spec__9(v___x_527_, v___x_562_);
v___x_564_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_564_, 0, v_toCold_552_);
lean_ctor_set(v___x_564_, 1, v___x_527_);
lean_ctor_set(v___x_564_, 2, v_currRecDepth_553_);
lean_ctor_set(v___x_564_, 3, v___x_563_);
lean_ctor_set(v___x_564_, 4, v_ref_554_);
lean_ctor_set(v___x_564_, 5, v_currNamespace_555_);
lean_ctor_set(v___x_564_, 6, v_openDecls_556_);
lean_ctor_set(v___x_564_, 7, v_initHeartbeats_557_);
lean_ctor_set(v___x_564_, 8, v_maxHeartbeats_558_);
lean_ctor_set(v___x_564_, 9, v_currMacroScope_559_);
lean_ctor_set_uint8(v___x_564_, sizeof(void*)*10, v___x_550_);
lean_ctor_set_uint8(v___x_564_, sizeof(void*)*10 + 1, v_suppressElabErrors_560_);
v___x_565_ = l_Lean_Compiler_LCNF_emitC(v_name_528_, v___x_564_, v___y_561_);
lean_dec(v___y_561_);
lean_dec_ref_known(v___x_564_, 10);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v_a_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_a_566_);
lean_dec_ref_known(v___x_565_, 1);
v___x_567_ = lean_st_ref_get(v___x_544_);
lean_dec(v___x_544_);
lean_dec(v___x_567_);
v___x_568_ = lean_string_to_utf8(v_a_566_);
lean_dec(v_a_566_);
v___x_569_ = lean_io_prim_handle_write(v_a_529_, v___x_568_);
lean_dec_ref(v___x_568_);
return v___x_569_;
}
else
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_591_; 
lean_dec(v___x_544_);
v_a_570_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_591_ == 0)
{
v___x_572_ = v___x_565_;
v_isShared_573_ = v_isSharedCheck_591_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_565_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_591_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
if (lean_obj_tag(v_a_570_) == 0)
{
lean_object* v_msg_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_578_; 
v_msg_574_ = lean_ctor_get(v_a_570_, 1);
lean_inc_ref(v_msg_574_);
lean_dec_ref_known(v_a_570_, 2);
v___x_575_ = l_Lean_MessageData_toString(v_msg_574_);
v___x_576_ = lean_mk_io_user_error(v___x_575_);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v___x_576_);
v___x_578_ = v___x_572_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_576_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
else
{
lean_object* v_id_580_; lean_object* v___x_581_; 
lean_del_object(v___x_572_);
v_id_580_ = lean_ctor_get(v_a_570_, 0);
lean_inc(v_id_580_);
lean_dec_ref_known(v_a_570_, 2);
v___x_581_ = l_Lean_InternalExceptionId_getName(v_id_580_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
lean_dec(v_id_580_);
v_a_582_ = lean_ctor_get(v___x_581_, 0);
lean_inc(v_a_582_);
lean_dec_ref_known(v___x_581_, 1);
v___x_583_ = ((lean_object*)(l_main___lam__1___closed__0));
v___x_584_ = l_Lean_Name_toString(v_a_582_, v___x_530_);
v___x_585_ = lean_string_append(v___x_583_, v___x_584_);
lean_dec_ref(v___x_584_);
v_a_540_ = v___x_585_;
goto v___jp_539_;
}
else
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
lean_dec_ref_known(v___x_581_, 1);
v___x_586_ = ((lean_object*)(l_main___lam__1___closed__1));
v___x_587_ = l_Nat_reprFast(v_id_580_);
v___x_588_ = lean_string_append(v___x_586_, v___x_587_);
lean_dec_ref(v___x_587_);
v___x_589_ = ((lean_object*)(l_main___lam__1___closed__2));
v___x_590_ = lean_string_append(v___x_588_, v___x_589_);
v_a_540_ = v___x_590_;
goto v___jp_539_;
}
}
}
}
}
v___jp_592_:
{
if (v___y_593_ == 0)
{
lean_object* v___x_594_; lean_object* v_env_595_; lean_object* v_nextMacroScope_596_; lean_object* v_ngen_597_; lean_object* v_auxDeclNGen_598_; lean_object* v_traceState_599_; lean_object* v_messages_600_; lean_object* v_infoState_601_; lean_object* v_snapshotTasks_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_611_; 
v___x_594_ = lean_st_ref_take(v___x_544_);
v_env_595_ = lean_ctor_get(v___x_594_, 0);
v_nextMacroScope_596_ = lean_ctor_get(v___x_594_, 1);
v_ngen_597_ = lean_ctor_get(v___x_594_, 2);
v_auxDeclNGen_598_ = lean_ctor_get(v___x_594_, 3);
v_traceState_599_ = lean_ctor_get(v___x_594_, 4);
v_messages_600_ = lean_ctor_get(v___x_594_, 6);
v_infoState_601_ = lean_ctor_get(v___x_594_, 7);
v_snapshotTasks_602_ = lean_ctor_get(v___x_594_, 8);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_611_ == 0)
{
lean_object* v_unused_612_; 
v_unused_612_ = lean_ctor_get(v___x_594_, 5);
lean_dec(v_unused_612_);
v___x_604_ = v___x_594_;
v_isShared_605_ = v_isSharedCheck_611_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_snapshotTasks_602_);
lean_inc(v_infoState_601_);
lean_inc(v_messages_600_);
lean_inc(v_traceState_599_);
lean_inc(v_auxDeclNGen_598_);
lean_inc(v_ngen_597_);
lean_inc(v_nextMacroScope_596_);
lean_inc(v_env_595_);
lean_dec(v___x_594_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_611_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; lean_object* v___x_608_; 
v___x_606_ = l_Lean_Kernel_enableDiag(v_env_595_, v___x_550_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 5, v___x_531_);
lean_ctor_set(v___x_604_, 0, v___x_606_);
v___x_608_ = v___x_604_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_606_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_nextMacroScope_596_);
lean_ctor_set(v_reuseFailAlloc_610_, 2, v_ngen_597_);
lean_ctor_set(v_reuseFailAlloc_610_, 3, v_auxDeclNGen_598_);
lean_ctor_set(v_reuseFailAlloc_610_, 4, v_traceState_599_);
lean_ctor_set(v_reuseFailAlloc_610_, 5, v___x_531_);
lean_ctor_set(v_reuseFailAlloc_610_, 6, v_messages_600_);
lean_ctor_set(v_reuseFailAlloc_610_, 7, v_infoState_601_);
lean_ctor_set(v_reuseFailAlloc_610_, 8, v_snapshotTasks_602_);
v___x_608_ = v_reuseFailAlloc_610_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v___x_609_; 
v___x_609_ = lean_st_ref_put(v___x_544_, v___x_608_);
lean_inc(v___x_544_);
v_toCold_552_ = v___x_548_;
v_currRecDepth_553_ = v___x_532_;
v_ref_554_ = v___x_533_;
v_currNamespace_555_ = v___x_525_;
v_openDecls_556_ = v___x_534_;
v_initHeartbeats_557_ = v___x_543_;
v_maxHeartbeats_558_ = v___x_535_;
v_currMacroScope_559_ = v___x_536_;
v_suppressElabErrors_560_ = v___x_537_;
v___y_561_ = v___x_544_;
goto v___jp_551_;
}
}
}
else
{
lean_dec_ref(v___x_531_);
lean_inc(v___x_544_);
v_toCold_552_ = v___x_548_;
v_currRecDepth_553_ = v___x_532_;
v_ref_554_ = v___x_533_;
v_currNamespace_555_ = v___x_525_;
v_openDecls_556_ = v___x_534_;
v_initHeartbeats_557_ = v___x_543_;
v_maxHeartbeats_558_ = v___x_535_;
v_currMacroScope_559_ = v___x_536_;
v_suppressElabErrors_560_ = v___x_537_;
v___y_561_ = v___x_544_;
goto v___jp_551_;
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__1___boxed(lean_object** _args){
lean_object* v___x_614_ = _args[0];
lean_object* v___x_615_ = _args[1];
lean_object* v_head_616_ = _args[2];
lean_object* v___x_617_ = _args[3];
lean_object* v___x_618_ = _args[4];
lean_object* v___x_619_ = _args[5];
lean_object* v___x_620_ = _args[6];
lean_object* v_name_621_ = _args[7];
lean_object* v_a_622_ = _args[8];
lean_object* v___x_623_ = _args[9];
lean_object* v___x_624_ = _args[10];
lean_object* v___x_625_ = _args[11];
lean_object* v___x_626_ = _args[12];
lean_object* v___x_627_ = _args[13];
lean_object* v___x_628_ = _args[14];
lean_object* v___x_629_ = _args[15];
lean_object* v___x_630_ = _args[16];
lean_object* v___y_631_ = _args[17];
_start:
{
uint8_t v___x_35234__boxed_632_; uint8_t v___x_35241__boxed_633_; lean_object* v_res_634_; 
v___x_35234__boxed_632_ = lean_unbox(v___x_623_);
v___x_35241__boxed_633_ = lean_unbox(v___x_630_);
v_res_634_ = l_main___lam__1(v___x_614_, v___x_615_, v_head_616_, v___x_617_, v___x_618_, v___x_619_, v___x_620_, v_name_621_, v_a_622_, v___x_35234__boxed_632_, v___x_624_, v___x_625_, v___x_626_, v___x_627_, v___x_628_, v___x_629_, v___x_35241__boxed_633_);
lean_dec(v_a_622_);
lean_dec(v___x_615_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(lean_object* v_s_635_){
_start:
{
lean_object* v___x_637_; lean_object* v_putStr_638_; lean_object* v___x_639_; 
v___x_637_ = lean_get_stderr();
v_putStr_638_ = lean_ctor_get(v___x_637_, 4);
lean_inc_ref(v_putStr_638_);
lean_dec_ref(v___x_637_);
v___x_639_ = lean_apply_2(v_putStr_638_, v_s_635_, lean_box(0));
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8___boxed(lean_object* v_s_640_, lean_object* v_a_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v_s_640_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6(lean_object* v_s_643_){
_start:
{
uint32_t v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_645_ = 10;
v___x_646_ = lean_string_push(v_s_643_, v___x_645_);
v___x_647_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v___x_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6___boxed(lean_object* v_s_648_, lean_object* v_a_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_IO_eprintln___at___00main_spec__6(v_s_648_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(lean_object* v_o_654_, lean_object* v_k_655_, lean_object* v_v_656_){
_start:
{
lean_object* v_map_657_; uint8_t v_hasTrace_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_672_; 
v_map_657_ = lean_ctor_get(v_o_654_, 0);
v_hasTrace_658_ = lean_ctor_get_uint8(v_o_654_, sizeof(void*)*1);
v_isSharedCheck_672_ = !lean_is_exclusive(v_o_654_);
if (v_isSharedCheck_672_ == 0)
{
v___x_660_ = v_o_654_;
v_isShared_661_ = v_isSharedCheck_672_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_map_657_);
lean_dec(v_o_654_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_672_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_662_, 0, v_v_656_);
lean_inc(v_k_655_);
v___x_663_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_655_, v___x_662_, v_map_657_);
if (v_hasTrace_658_ == 0)
{
lean_object* v___x_664_; uint8_t v___x_665_; lean_object* v___x_667_; 
v___x_664_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_665_ = l_Lean_Name_isPrefixOf(v___x_664_, v_k_655_);
lean_dec(v_k_655_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v___x_663_);
v___x_667_ = v___x_660_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_663_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
lean_ctor_set_uint8(v___x_667_, sizeof(void*)*1, v___x_665_);
return v___x_667_;
}
}
else
{
lean_object* v___x_670_; 
lean_dec(v_k_655_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v___x_663_);
v___x_670_ = v___x_660_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_663_);
lean_ctor_set_uint8(v_reuseFailAlloc_671_, sizeof(void*)*1, v_hasTrace_658_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00main_spec__3(lean_object* v_opts_673_, lean_object* v_opt_674_, lean_object* v_val_675_){
_start:
{
lean_object* v_name_676_; lean_object* v___x_677_; 
v_name_676_ = lean_ctor_get(v_opt_674_, 0);
lean_inc(v_name_676_);
lean_dec_ref(v_opt_674_);
v___x_677_ = l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(v_opts_673_, v_name_676_, v_val_675_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(lean_object* v___y_679_, lean_object* v_as_680_, size_t v_i_681_, size_t v_stop_682_, lean_object* v_b_683_){
_start:
{
lean_object* v___y_685_; uint8_t v___x_689_; 
v___x_689_ = lean_usize_dec_eq(v_i_681_, v_stop_682_);
if (v___x_689_ == 0)
{
lean_object* v_fst_690_; lean_object* v_snd_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___y_695_; 
v_fst_690_ = lean_ctor_get(v_b_683_, 0);
v_snd_691_ = lean_ctor_get(v_b_683_, 1);
v___x_692_ = lean_array_uget_borrowed(v_as_680_, v_i_681_);
v___x_693_ = l_Lean_IR_Decl_name(v___x_692_);
if (lean_obj_tag(v___x_693_) == 1)
{
lean_object* v_pre_708_; lean_object* v_str_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v_pre_708_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_pre_708_);
v_str_709_ = lean_ctor_get(v___x_693_, 1);
lean_inc_ref(v_str_709_);
v___x_710_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___closed__0));
v___x_711_ = lean_string_dec_eq(v_str_709_, v___x_710_);
lean_dec_ref(v_str_709_);
if (v___x_711_ == 0)
{
lean_dec(v_pre_708_);
lean_inc_ref(v___x_693_);
v___y_695_ = v___x_693_;
goto v___jp_694_;
}
else
{
v___y_695_ = v_pre_708_;
goto v___jp_694_;
}
}
else
{
lean_inc(v___x_693_);
v___y_695_ = v___x_693_;
goto v___jp_694_;
}
v___jp_694_:
{
uint8_t v___x_696_; 
lean_inc_ref(v___y_679_);
v___x_696_ = l_Lean_isExtern(v___y_679_, v___y_695_);
if (v___x_696_ == 0)
{
lean_dec(v___x_693_);
v___y_685_ = v_b_683_;
goto v___jp_684_;
}
else
{
lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_705_; 
lean_inc(v_snd_691_);
lean_inc(v_fst_690_);
v_isSharedCheck_705_ = !lean_is_exclusive(v_b_683_);
if (v_isSharedCheck_705_ == 0)
{
lean_object* v_unused_706_; lean_object* v_unused_707_; 
v_unused_706_ = lean_ctor_get(v_b_683_, 1);
lean_dec(v_unused_706_);
v_unused_707_ = lean_ctor_get(v_b_683_, 0);
lean_dec(v_unused_707_);
v___x_698_ = v_b_683_;
v_isShared_699_ = v_isSharedCheck_705_;
goto v_resetjp_697_;
}
else
{
lean_dec(v_b_683_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_705_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; 
lean_inc_n(v___x_692_, 2);
v___x_700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_692_);
lean_ctor_set(v___x_700_, 1, v_fst_690_);
v___x_701_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(v_snd_691_, v___x_693_, v___x_692_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v___x_701_);
lean_ctor_set(v___x_698_, 0, v___x_700_);
v___x_703_ = v___x_698_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v___x_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
v___y_685_ = v___x_703_;
goto v___jp_684_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_679_);
return v_b_683_;
}
v___jp_684_:
{
size_t v___x_686_; size_t v___x_687_; 
v___x_686_ = ((size_t)1ULL);
v___x_687_ = lean_usize_add(v_i_681_, v___x_686_);
v_i_681_ = v___x_687_;
v_b_683_ = v___y_685_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___boxed(lean_object* v___y_712_, lean_object* v_as_713_, lean_object* v_i_714_, lean_object* v_stop_715_, lean_object* v_b_716_){
_start:
{
size_t v_i_boxed_717_; size_t v_stop_boxed_718_; lean_object* v_res_719_; 
v_i_boxed_717_ = lean_unbox_usize(v_i_714_);
lean_dec(v_i_714_);
v_stop_boxed_718_ = lean_unbox_usize(v_stop_715_);
lean_dec(v_stop_715_);
v_res_719_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_712_, v_as_713_, v_i_boxed_717_, v_stop_boxed_718_, v_b_716_);
lean_dec_ref(v_as_713_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg(lean_object* v_as_x27_721_, lean_object* v_b_722_){
_start:
{
if (lean_obj_tag(v_as_x27_721_) == 0)
{
lean_object* v___x_724_; 
v___x_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_724_, 0, v_b_722_);
return v___x_724_;
}
else
{
lean_object* v_head_725_; lean_object* v_tail_726_; lean_object* v_fst_727_; lean_object* v_snd_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_753_; 
v_head_725_ = lean_ctor_get(v_as_x27_721_, 0);
v_tail_726_ = lean_ctor_get(v_as_x27_721_, 1);
v_fst_727_ = lean_ctor_get(v_b_722_, 0);
v_snd_728_ = lean_ctor_get(v_b_722_, 1);
v_isSharedCheck_753_ = !lean_is_exclusive(v_b_722_);
if (v_isSharedCheck_753_ == 0)
{
v___x_730_ = v_b_722_;
v_isShared_731_ = v_isSharedCheck_753_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_snd_728_);
lean_inc(v_fst_727_);
lean_dec(v_b_722_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_753_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_732_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0));
v___x_733_ = lean_string_dec_eq(v_head_725_, v___x_732_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; 
lean_inc(v_head_725_);
v___x_734_ = l___private_LeanIR_0__setConfigOption(v_snd_728_, v_head_725_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_737_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_a_735_);
lean_dec_ref_known(v___x_734_, 1);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 1, v_a_735_);
v___x_737_ = v___x_730_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_fst_727_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_a_735_);
v___x_737_ = v_reuseFailAlloc_739_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
v_as_x27_721_ = v_tail_726_;
v_b_722_ = v___x_737_;
goto _start;
}
}
else
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_del_object(v___x_730_);
lean_dec(v_fst_727_);
v_a_740_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_734_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_734_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
else
{
lean_object* v___x_748_; lean_object* v___x_750_; 
lean_dec(v_fst_727_);
v___x_748_ = lean_box(v___x_733_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v___x_748_);
v___x_750_ = v___x_730_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v_snd_728_);
v___x_750_ = v_reuseFailAlloc_752_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
v_as_x27_721_ = v_tail_726_;
v_b_722_ = v___x_750_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg___boxed(lean_object* v_as_x27_754_, lean_object* v_b_755_, lean_object* v___y_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_754_, v_b_755_);
lean_dec(v_as_x27_754_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(lean_object* v_as_758_, size_t v_i_759_, size_t v_stop_760_, lean_object* v_b_761_){
_start:
{
uint8_t v___x_762_; 
v___x_762_ = lean_usize_dec_eq(v_i_759_, v_stop_760_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; lean_object* v_toEnvExtension_764_; lean_object* v_asyncMode_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; size_t v___x_769_; size_t v___x_770_; 
v___x_763_ = l_Lean_Compiler_LCNF_impureSigExt;
v_toEnvExtension_764_ = lean_ctor_get(v___x_763_, 0);
v_asyncMode_765_ = lean_ctor_get(v_toEnvExtension_764_, 2);
v___x_766_ = lean_box(0);
v___x_767_ = lean_array_uget_borrowed(v_as_758_, v_i_759_);
lean_inc(v___x_767_);
v___x_768_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_763_, v_b_761_, v___x_767_, v_asyncMode_765_, v___x_766_);
v___x_769_ = ((size_t)1ULL);
v___x_770_ = lean_usize_add(v_i_759_, v___x_769_);
v_i_759_ = v___x_770_;
v_b_761_ = v___x_768_;
goto _start;
}
else
{
return v_b_761_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18___boxed(lean_object* v_as_772_, lean_object* v_i_773_, lean_object* v_stop_774_, lean_object* v_b_775_){
_start:
{
size_t v_i_boxed_776_; size_t v_stop_boxed_777_; lean_object* v_res_778_; 
v_i_boxed_776_ = lean_unbox_usize(v_i_773_);
lean_dec(v_i_773_);
v_stop_boxed_777_ = lean_unbox_usize(v_stop_774_);
lean_dec(v_stop_774_);
v_res_778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_as_772_, v_i_boxed_776_, v_stop_boxed_777_, v_b_775_);
lean_dec_ref(v_as_772_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(lean_object* v_as_782_, size_t v_sz_783_, size_t v_i_784_, lean_object* v_b_785_, lean_object* v___y_786_){
_start:
{
uint8_t v___x_788_; 
v___x_788_ = lean_usize_dec_lt(v_i_784_, v_sz_783_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; 
v___x_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_789_, 0, v_b_785_);
return v___x_789_;
}
else
{
uint8_t v___x_790_; lean_object* v_a_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
lean_dec_ref(v_b_785_);
v___x_790_ = 0;
v_a_791_ = lean_array_uget_borrowed(v_as_782_, v_i_784_);
lean_inc(v_a_791_);
v___x_792_ = l_Lean_Message_toString(v_a_791_, v___x_790_);
v___x_793_ = l_IO_eprintln___at___00main_spec__6(v___x_792_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v___x_794_; size_t v___x_795_; size_t v___x_796_; 
lean_dec_ref_known(v___x_793_, 1);
v___x_794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_795_ = ((size_t)1ULL);
v___x_796_ = lean_usize_add(v_i_784_, v___x_795_);
v_i_784_ = v___x_796_;
v_b_785_ = v___x_794_;
goto _start;
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_810_; 
v_a_798_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_810_ == 0)
{
v___x_800_ = v___x_793_;
v_isShared_801_ = v_isSharedCheck_810_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_793_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_810_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v_ref_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_808_; 
v_ref_802_ = lean_ctor_get(v___y_786_, 4);
v___x_803_ = lean_io_error_to_string(v_a_798_);
v___x_804_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
v___x_805_ = l_Lean_MessageData_ofFormat(v___x_804_);
lean_inc(v_ref_802_);
v___x_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_806_, 0, v_ref_802_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 0, v___x_806_);
v___x_808_ = v___x_800_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___boxed(lean_object* v_as_811_, lean_object* v_sz_812_, lean_object* v_i_813_, lean_object* v_b_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
size_t v_sz_boxed_817_; size_t v_i_boxed_818_; lean_object* v_res_819_; 
v_sz_boxed_817_ = lean_unbox_usize(v_sz_812_);
lean_dec(v_sz_812_);
v_i_boxed_818_ = lean_unbox_usize(v_i_813_);
lean_dec(v_i_813_);
v_res_819_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_811_, v_sz_boxed_817_, v_i_boxed_818_, v_b_814_, v___y_815_);
lean_dec_ref(v___y_815_);
lean_dec_ref(v_as_811_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(lean_object* v_as_820_, size_t v_sz_821_, size_t v_i_822_, lean_object* v_b_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
uint8_t v___x_827_; 
v___x_827_ = lean_usize_dec_lt(v_i_822_, v_sz_821_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; 
v___x_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_828_, 0, v_b_823_);
return v___x_828_;
}
else
{
uint8_t v___x_829_; lean_object* v_a_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
lean_dec_ref(v_b_823_);
v___x_829_ = 0;
v_a_830_ = lean_array_uget_borrowed(v_as_820_, v_i_822_);
lean_inc(v_a_830_);
v___x_831_ = l_Lean_Message_toString(v_a_830_, v___x_829_);
v___x_832_ = l_IO_eprintln___at___00main_spec__6(v___x_831_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v___x_833_; size_t v___x_834_; size_t v___x_835_; lean_object* v___x_836_; 
lean_dec_ref_known(v___x_832_, 1);
v___x_833_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_834_ = ((size_t)1ULL);
v___x_835_ = lean_usize_add(v_i_822_, v___x_834_);
v___x_836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_820_, v_sz_821_, v___x_835_, v___x_833_, v___y_824_);
return v___x_836_;
}
else
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_849_; 
v_a_837_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_849_ == 0)
{
v___x_839_ = v___x_832_;
v_isShared_840_ = v_isSharedCheck_849_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_832_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_849_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v_ref_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_847_; 
v_ref_841_ = lean_ctor_get(v___y_824_, 4);
v___x_842_ = lean_io_error_to_string(v_a_837_);
v___x_843_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_843_, 0, v___x_842_);
v___x_844_ = l_Lean_MessageData_ofFormat(v___x_843_);
lean_inc(v_ref_841_);
v___x_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_845_, 0, v_ref_841_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 0, v___x_845_);
v___x_847_ = v___x_839_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_845_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27___boxed(lean_object* v_as_850_, lean_object* v_sz_851_, lean_object* v_i_852_, lean_object* v_b_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
size_t v_sz_boxed_857_; size_t v_i_boxed_858_; lean_object* v_res_859_; 
v_sz_boxed_857_ = lean_unbox_usize(v_sz_851_);
lean_dec(v_sz_851_);
v_i_boxed_858_ = lean_unbox_usize(v_i_852_);
lean_dec(v_i_852_);
v_res_859_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(v_as_850_, v_sz_boxed_857_, v_i_boxed_858_, v_b_853_, v___y_854_, v___y_855_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec_ref(v_as_850_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(lean_object* v_as_863_, size_t v_sz_864_, size_t v_i_865_, lean_object* v_b_866_, lean_object* v___y_867_){
_start:
{
uint8_t v___x_869_; 
v___x_869_ = lean_usize_dec_lt(v_i_865_, v_sz_864_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; 
v___x_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_870_, 0, v_b_866_);
return v___x_870_;
}
else
{
uint8_t v___x_871_; lean_object* v_a_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
lean_dec_ref(v_b_866_);
v___x_871_ = 0;
v_a_872_ = lean_array_uget_borrowed(v_as_863_, v_i_865_);
lean_inc(v_a_872_);
v___x_873_ = l_Lean_Message_toString(v_a_872_, v___x_871_);
v___x_874_ = l_IO_eprintln___at___00main_spec__6(v___x_873_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v___x_875_; size_t v___x_876_; size_t v___x_877_; 
lean_dec_ref_known(v___x_874_, 1);
v___x_875_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_876_ = ((size_t)1ULL);
v___x_877_ = lean_usize_add(v_i_865_, v___x_876_);
v_i_865_ = v___x_877_;
v_b_866_ = v___x_875_;
goto _start;
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_891_; 
v_a_879_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_891_ == 0)
{
v___x_881_ = v___x_874_;
v_isShared_882_ = v_isSharedCheck_891_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_874_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_891_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v_ref_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_889_; 
v_ref_883_ = lean_ctor_get(v___y_867_, 4);
v___x_884_ = lean_io_error_to_string(v_a_879_);
v___x_885_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
v___x_886_ = l_Lean_MessageData_ofFormat(v___x_885_);
lean_inc(v_ref_883_);
v___x_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_887_, 0, v_ref_883_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_887_);
v___x_889_ = v___x_881_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___boxed(lean_object* v_as_892_, lean_object* v_sz_893_, lean_object* v_i_894_, lean_object* v_b_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
size_t v_sz_boxed_898_; size_t v_i_boxed_899_; lean_object* v_res_900_; 
v_sz_boxed_898_ = lean_unbox_usize(v_sz_893_);
lean_dec(v_sz_893_);
v_i_boxed_899_ = lean_unbox_usize(v_i_894_);
lean_dec(v_i_894_);
v_res_900_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_892_, v_sz_boxed_898_, v_i_boxed_899_, v_b_895_, v___y_896_);
lean_dec_ref(v___y_896_);
lean_dec_ref(v_as_892_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(lean_object* v_as_901_, size_t v_sz_902_, size_t v_i_903_, lean_object* v_b_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
uint8_t v___x_908_; 
v___x_908_ = lean_usize_dec_lt(v_i_903_, v_sz_902_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; 
v___x_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_909_, 0, v_b_904_);
return v___x_909_;
}
else
{
uint8_t v___x_910_; lean_object* v_a_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
lean_dec_ref(v_b_904_);
v___x_910_ = 0;
v_a_911_ = lean_array_uget_borrowed(v_as_901_, v_i_903_);
lean_inc(v_a_911_);
v___x_912_ = l_Lean_Message_toString(v_a_911_, v___x_910_);
v___x_913_ = l_IO_eprintln___at___00main_spec__6(v___x_912_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v___x_914_; size_t v___x_915_; size_t v___x_916_; lean_object* v___x_917_; 
lean_dec_ref_known(v___x_913_, 1);
v___x_914_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_915_ = ((size_t)1ULL);
v___x_916_ = lean_usize_add(v_i_903_, v___x_915_);
v___x_917_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_901_, v_sz_902_, v___x_916_, v___x_914_, v___y_905_);
return v___x_917_;
}
else
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_930_; 
v_a_918_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_930_ == 0)
{
v___x_920_ = v___x_913_;
v_isShared_921_ = v_isSharedCheck_930_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_913_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_930_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v_ref_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_928_; 
v_ref_922_ = lean_ctor_get(v___y_905_, 4);
v___x_923_ = lean_io_error_to_string(v_a_918_);
v___x_924_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
v___x_925_ = l_Lean_MessageData_ofFormat(v___x_924_);
lean_inc(v_ref_922_);
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v_ref_922_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 0, v___x_926_);
v___x_928_ = v___x_920_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_926_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38___boxed(lean_object* v_as_931_, lean_object* v_sz_932_, lean_object* v_i_933_, lean_object* v_b_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
size_t v_sz_boxed_938_; size_t v_i_boxed_939_; lean_object* v_res_940_; 
v_sz_boxed_938_ = lean_unbox_usize(v_sz_932_);
lean_dec(v_sz_932_);
v_i_boxed_939_ = lean_unbox_usize(v_i_933_);
lean_dec(v_i_933_);
v_res_940_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(v_as_931_, v_sz_boxed_938_, v_i_boxed_939_, v_b_934_, v___y_935_, v___y_936_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec_ref(v_as_931_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(lean_object* v_init_941_, lean_object* v_n_942_, lean_object* v_b_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
if (lean_obj_tag(v_n_942_) == 0)
{
lean_object* v_cs_947_; lean_object* v___x_948_; lean_object* v___x_949_; size_t v_sz_950_; size_t v___x_951_; lean_object* v___x_952_; 
v_cs_947_ = lean_ctor_get(v_n_942_, 0);
v___x_948_ = lean_box(0);
v___x_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
lean_ctor_set(v___x_949_, 1, v_b_943_);
v_sz_950_ = lean_array_size(v_cs_947_);
v___x_951_ = ((size_t)0ULL);
v___x_952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(v_init_941_, v_cs_947_, v_sz_950_, v___x_951_, v___x_949_, v___y_944_, v___y_945_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_967_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_967_ == 0)
{
v___x_955_ = v___x_952_;
v_isShared_956_ = v_isSharedCheck_967_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_952_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_967_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v_fst_957_; 
v_fst_957_ = lean_ctor_get(v_a_953_, 0);
if (lean_obj_tag(v_fst_957_) == 0)
{
lean_object* v_snd_958_; lean_object* v___x_959_; lean_object* v___x_961_; 
v_snd_958_ = lean_ctor_get(v_a_953_, 1);
lean_inc(v_snd_958_);
lean_dec(v_a_953_);
v___x_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_959_, 0, v_snd_958_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v___x_959_);
v___x_961_ = v___x_955_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_959_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
else
{
lean_object* v_val_963_; lean_object* v___x_965_; 
lean_inc_ref(v_fst_957_);
lean_dec(v_a_953_);
v_val_963_ = lean_ctor_get(v_fst_957_, 0);
lean_inc(v_val_963_);
lean_dec_ref_known(v_fst_957_, 1);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v_val_963_);
v___x_965_ = v___x_955_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_val_963_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
else
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
v_a_968_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_975_ == 0)
{
v___x_970_ = v___x_952_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_952_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_968_);
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
lean_object* v_vs_976_; lean_object* v___x_977_; lean_object* v___x_978_; size_t v_sz_979_; size_t v___x_980_; lean_object* v___x_981_; 
v_vs_976_ = lean_ctor_get(v_n_942_, 0);
v___x_977_ = lean_box(0);
v___x_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
lean_ctor_set(v___x_978_, 1, v_b_943_);
v_sz_979_ = lean_array_size(v_vs_976_);
v___x_980_ = ((size_t)0ULL);
v___x_981_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(v_vs_976_, v_sz_979_, v___x_980_, v___x_978_, v___y_944_, v___y_945_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_996_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_996_ == 0)
{
v___x_984_ = v___x_981_;
v_isShared_985_ = v_isSharedCheck_996_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v___x_981_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_996_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v_fst_986_; 
v_fst_986_ = lean_ctor_get(v_a_982_, 0);
if (lean_obj_tag(v_fst_986_) == 0)
{
lean_object* v_snd_987_; lean_object* v___x_988_; lean_object* v___x_990_; 
v_snd_987_ = lean_ctor_get(v_a_982_, 1);
lean_inc(v_snd_987_);
lean_dec(v_a_982_);
v___x_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_988_, 0, v_snd_987_);
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 0, v___x_988_);
v___x_990_ = v___x_984_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_988_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
else
{
lean_object* v_val_992_; lean_object* v___x_994_; 
lean_inc_ref(v_fst_986_);
lean_dec(v_a_982_);
v_val_992_ = lean_ctor_get(v_fst_986_, 0);
lean_inc(v_val_992_);
lean_dec_ref_known(v_fst_986_, 1);
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 0, v_val_992_);
v___x_994_ = v___x_984_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_val_992_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
else
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
v_a_997_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_999_ = v___x_981_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_981_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_997_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(lean_object* v_init_1005_, lean_object* v_as_1006_, size_t v_sz_1007_, size_t v_i_1008_, lean_object* v_b_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
uint8_t v___x_1013_; 
v___x_1013_ = lean_usize_dec_lt(v_i_1008_, v_sz_1007_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; 
v___x_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1014_, 0, v_b_1009_);
return v___x_1014_;
}
else
{
lean_object* v_snd_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1049_; 
v_snd_1015_ = lean_ctor_get(v_b_1009_, 1);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_b_1009_);
if (v_isSharedCheck_1049_ == 0)
{
lean_object* v_unused_1050_; 
v_unused_1050_ = lean_ctor_get(v_b_1009_, 0);
lean_dec(v_unused_1050_);
v___x_1017_ = v_b_1009_;
v_isShared_1018_ = v_isSharedCheck_1049_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_snd_1015_);
lean_dec(v_b_1009_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1049_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v_a_1019_; lean_object* v___x_1020_; 
v_a_1019_ = lean_array_uget_borrowed(v_as_1006_, v_i_1008_);
lean_inc(v_snd_1015_);
v___x_1020_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_1005_, v_a_1019_, v_snd_1015_, v___y_1010_, v___y_1011_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1040_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1023_ = v___x_1020_;
v_isShared_1024_ = v_isSharedCheck_1040_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1020_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1040_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
if (lean_obj_tag(v_a_1021_) == 0)
{
lean_object* v___x_1025_; lean_object* v___x_1027_; 
v___x_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1025_, 0, v_a_1021_);
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 0, v___x_1025_);
v___x_1027_ = v___x_1017_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1025_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_snd_1015_);
v___x_1027_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
lean_object* v___x_1029_; 
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v___x_1027_);
v___x_1029_ = v___x_1023_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1027_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1033_; lean_object* v___x_1035_; 
lean_del_object(v___x_1023_);
lean_dec(v_snd_1015_);
v_a_1032_ = lean_ctor_get(v_a_1021_, 0);
lean_inc(v_a_1032_);
lean_dec_ref_known(v_a_1021_, 1);
v___x_1033_ = lean_box(0);
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 1, v_a_1032_);
lean_ctor_set(v___x_1017_, 0, v___x_1033_);
v___x_1035_ = v___x_1017_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1033_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_a_1032_);
v___x_1035_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
size_t v___x_1036_; size_t v___x_1037_; 
v___x_1036_ = ((size_t)1ULL);
v___x_1037_ = lean_usize_add(v_i_1008_, v___x_1036_);
v_i_1008_ = v___x_1037_;
v_b_1009_ = v___x_1035_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
lean_del_object(v___x_1017_);
lean_dec(v_snd_1015_);
v_a_1041_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_1020_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1020_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37___boxed(lean_object* v_init_1051_, lean_object* v_as_1052_, lean_object* v_sz_1053_, lean_object* v_i_1054_, lean_object* v_b_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
size_t v_sz_boxed_1059_; size_t v_i_boxed_1060_; lean_object* v_res_1061_; 
v_sz_boxed_1059_ = lean_unbox_usize(v_sz_1053_);
lean_dec(v_sz_1053_);
v_i_boxed_1060_ = lean_unbox_usize(v_i_1054_);
lean_dec(v_i_1054_);
v_res_1061_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(v_init_1051_, v_as_1052_, v_sz_boxed_1059_, v_i_boxed_1060_, v_b_1055_, v___y_1056_, v___y_1057_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec_ref(v_as_1052_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26___boxed(lean_object* v_init_1062_, lean_object* v_n_1063_, lean_object* v_b_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_1062_, v_n_1063_, v_b_1064_, v___y_1065_, v___y_1066_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec_ref(v_n_1063_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__12(lean_object* v_t_1069_, lean_object* v_init_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v_root_1074_; lean_object* v_tail_1075_; lean_object* v___x_1076_; 
v_root_1074_ = lean_ctor_get(v_t_1069_, 0);
v_tail_1075_ = lean_ctor_get(v_t_1069_, 1);
v___x_1076_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_1070_, v_root_1074_, v_init_1070_, v___y_1071_, v___y_1072_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1113_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1079_ = v___x_1076_;
v_isShared_1080_ = v_isSharedCheck_1113_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1076_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1113_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
if (lean_obj_tag(v_a_1077_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1083_; 
v_a_1081_ = lean_ctor_get(v_a_1077_, 0);
lean_inc(v_a_1081_);
lean_dec_ref_known(v_a_1077_, 1);
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v_a_1081_);
v___x_1083_ = v___x_1079_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1081_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; size_t v_sz_1088_; size_t v___x_1089_; lean_object* v___x_1090_; 
lean_del_object(v___x_1079_);
v_a_1085_ = lean_ctor_get(v_a_1077_, 0);
lean_inc(v_a_1085_);
lean_dec_ref_known(v_a_1077_, 1);
v___x_1086_ = lean_box(0);
v___x_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
lean_ctor_set(v___x_1087_, 1, v_a_1085_);
v_sz_1088_ = lean_array_size(v_tail_1075_);
v___x_1089_ = ((size_t)0ULL);
v___x_1090_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(v_tail_1075_, v_sz_1088_, v___x_1089_, v___x_1087_, v___y_1071_, v___y_1072_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1104_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1093_ = v___x_1090_;
v_isShared_1094_ = v_isSharedCheck_1104_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1090_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1104_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v_fst_1095_; 
v_fst_1095_ = lean_ctor_get(v_a_1091_, 0);
if (lean_obj_tag(v_fst_1095_) == 0)
{
lean_object* v_snd_1096_; lean_object* v___x_1098_; 
v_snd_1096_ = lean_ctor_get(v_a_1091_, 1);
lean_inc(v_snd_1096_);
lean_dec(v_a_1091_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 0, v_snd_1096_);
v___x_1098_ = v___x_1093_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_snd_1096_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
else
{
lean_object* v_val_1100_; lean_object* v___x_1102_; 
lean_inc_ref(v_fst_1095_);
lean_dec(v_a_1091_);
v_val_1100_ = lean_ctor_get(v_fst_1095_, 0);
lean_inc(v_val_1100_);
lean_dec_ref_known(v_fst_1095_, 1);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 0, v_val_1100_);
v___x_1102_ = v___x_1093_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_val_1100_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
else
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
v_a_1105_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_1090_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1090_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1105_);
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
}
}
else
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
v_a_1114_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1076_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1076_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__12___boxed(lean_object* v_t_1122_, lean_object* v_init_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Lean_PersistentArray_forIn___at___00main_spec__12(v_t_1122_, v_init_1123_, v___y_1124_, v___y_1125_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec_ref(v_t_1122_);
return v_res_1127_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0(uint8_t v_suppressElabErrors_1135_, uint8_t v___x_1136_, lean_object* v___x_1137_, lean_object* v_x_1138_){
_start:
{
if (lean_obj_tag(v_x_1138_) == 1)
{
lean_object* v_pre_1139_; 
v_pre_1139_ = lean_ctor_get(v_x_1138_, 0);
switch(lean_obj_tag(v_pre_1139_))
{
case 1:
{
lean_object* v_pre_1140_; 
v_pre_1140_ = lean_ctor_get(v_pre_1139_, 0);
switch(lean_obj_tag(v_pre_1140_))
{
case 0:
{
lean_object* v_str_1141_; lean_object* v_str_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; 
v_str_1141_ = lean_ctor_get(v_x_1138_, 1);
v_str_1142_ = lean_ctor_get(v_pre_1139_, 1);
v___x_1143_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0));
v___x_1144_ = lean_string_dec_eq(v_str_1142_, v___x_1143_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; uint8_t v___x_1146_; 
v___x_1145_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1));
v___x_1146_ = lean_string_dec_eq(v_str_1142_, v___x_1145_);
if (v___x_1146_ == 0)
{
return v___x_1146_;
}
else
{
lean_object* v___x_1147_; uint8_t v___x_1148_; 
v___x_1147_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2));
v___x_1148_ = lean_string_dec_eq(v_str_1141_, v___x_1147_);
if (v___x_1148_ == 0)
{
return v___x_1148_;
}
else
{
return v_suppressElabErrors_1135_;
}
}
}
else
{
lean_object* v___x_1149_; uint8_t v___x_1150_; 
v___x_1149_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3));
v___x_1150_ = lean_string_dec_eq(v_str_1141_, v___x_1149_);
if (v___x_1150_ == 0)
{
return v___x_1150_;
}
else
{
return v_suppressElabErrors_1135_;
}
}
}
case 1:
{
lean_object* v_pre_1151_; 
v_pre_1151_ = lean_ctor_get(v_pre_1140_, 0);
if (lean_obj_tag(v_pre_1151_) == 0)
{
lean_object* v_str_1152_; lean_object* v_str_1153_; lean_object* v_str_1154_; lean_object* v___x_1155_; uint8_t v___x_1156_; 
v_str_1152_ = lean_ctor_get(v_x_1138_, 1);
v_str_1153_ = lean_ctor_get(v_pre_1139_, 1);
v_str_1154_ = lean_ctor_get(v_pre_1140_, 1);
v___x_1155_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4));
v___x_1156_ = lean_string_dec_eq(v_str_1154_, v___x_1155_);
if (v___x_1156_ == 0)
{
return v___x_1156_;
}
else
{
lean_object* v___x_1157_; uint8_t v___x_1158_; 
v___x_1157_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5));
v___x_1158_ = lean_string_dec_eq(v_str_1153_, v___x_1157_);
if (v___x_1158_ == 0)
{
return v___x_1158_;
}
else
{
lean_object* v___x_1159_; uint8_t v___x_1160_; 
v___x_1159_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6));
v___x_1160_ = lean_string_dec_eq(v_str_1152_, v___x_1159_);
if (v___x_1160_ == 0)
{
return v___x_1160_;
}
else
{
return v_suppressElabErrors_1135_;
}
}
}
}
else
{
return v___x_1136_;
}
}
default: 
{
return v___x_1136_;
}
}
}
case 0:
{
lean_object* v_str_1161_; uint8_t v___x_1162_; 
v_str_1161_ = lean_ctor_get(v_x_1138_, 1);
v___x_1162_ = lean_string_dec_eq(v_str_1161_, v___x_1137_);
if (v___x_1162_ == 0)
{
return v___x_1162_;
}
else
{
return v_suppressElabErrors_1135_;
}
}
default: 
{
return v___x_1136_;
}
}
}
else
{
return v___x_1136_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___boxed(lean_object* v_suppressElabErrors_1163_, lean_object* v___x_1164_, lean_object* v___x_1165_, lean_object* v_x_1166_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1167_; uint8_t v___x_36126__boxed_1168_; uint8_t v_res_1169_; lean_object* v_r_1170_; 
v_suppressElabErrors_boxed_1167_ = lean_unbox(v_suppressElabErrors_1163_);
v___x_36126__boxed_1168_ = lean_unbox(v___x_1164_);
v_res_1169_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0(v_suppressElabErrors_boxed_1167_, v___x_36126__boxed_1168_, v___x_1165_, v_x_1166_);
lean_dec(v_x_1166_);
lean_dec_ref(v___x_1165_);
v_r_1170_ = lean_box(v_res_1169_);
return v_r_1170_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0(void){
_start:
{
lean_object* v___x_1171_; double v___x_1172_; 
v___x_1171_ = lean_unsigned_to_nat(0u);
v___x_1172_ = lean_float_of_nat(v___x_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(uint8_t v___x_1174_, lean_object* v_as_1175_, size_t v_sz_1176_, size_t v_i_1177_, lean_object* v_b_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v_a_1183_; uint8_t v___x_1187_; 
v___x_1187_ = lean_usize_dec_lt(v_i_1177_, v_sz_1176_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1188_; 
v___x_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1188_, 0, v_b_1178_);
return v___x_1188_;
}
else
{
lean_object* v_a_1189_; lean_object* v_fst_1190_; lean_object* v_snd_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1268_; 
v_a_1189_ = lean_array_uget(v_as_1175_, v_i_1177_);
v_fst_1190_ = lean_ctor_get(v_a_1189_, 0);
v_snd_1191_ = lean_ctor_get(v_a_1189_, 1);
v_isSharedCheck_1268_ = !lean_is_exclusive(v_a_1189_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1193_ = v_a_1189_;
v_isShared_1194_ = v_isSharedCheck_1268_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_snd_1191_);
lean_inc(v_fst_1190_);
lean_dec(v_a_1189_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1268_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v_fst_1195_; lean_object* v_snd_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1267_; 
v_fst_1195_ = lean_ctor_get(v_fst_1190_, 0);
v_snd_1196_ = lean_ctor_get(v_fst_1190_, 1);
v_isSharedCheck_1267_ = !lean_is_exclusive(v_fst_1190_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1198_ = v_fst_1190_;
v_isShared_1199_ = v_isSharedCheck_1267_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_snd_1196_);
lean_inc(v_fst_1195_);
lean_dec(v_fst_1190_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1267_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; double v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v_toCold_1205_; uint8_t v_suppressElabErrors_1206_; lean_object* v_fileName_1207_; lean_object* v_fileMap_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1215_; 
v___x_1200_ = lean_box(0);
v___x_1201_ = lean_box(0);
v___x_1202_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0);
v___x_1203_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1));
v___x_1204_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1204_, 0, v___x_1200_);
lean_ctor_set(v___x_1204_, 1, v___x_1201_);
lean_ctor_set(v___x_1204_, 2, v___x_1203_);
lean_ctor_set_float(v___x_1204_, sizeof(void*)*3, v___x_1202_);
lean_ctor_set_float(v___x_1204_, sizeof(void*)*3 + 8, v___x_1202_);
lean_ctor_set_uint8(v___x_1204_, sizeof(void*)*3 + 16, v___x_1187_);
v_toCold_1205_ = lean_ctor_get(v___y_1179_, 0);
v_suppressElabErrors_1206_ = lean_ctor_get_uint8(v___y_1179_, sizeof(void*)*10 + 1);
v_fileName_1207_ = lean_ctor_get(v_toCold_1205_, 0);
v_fileMap_1208_ = lean_ctor_get(v_toCold_1205_, 1);
v___x_1209_ = lean_box(0);
v___x_1210_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_1211_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_1212_ = l_Lean_MessageData_nil;
v___x_1213_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1204_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
lean_ctor_set(v___x_1213_, 2, v_snd_1191_);
if (v_isShared_1199_ == 0)
{
lean_ctor_set_tag(v___x_1198_, 8);
lean_ctor_set(v___x_1198_, 1, v___x_1213_);
lean_ctor_set(v___x_1198_, 0, v___x_1211_);
v___x_1215_ = v___x_1198_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1211_);
lean_ctor_set(v_reuseFailAlloc_1266_, 1, v___x_1213_);
v___x_1215_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
uint8_t v___x_1216_; lean_object* v___x_1217_; lean_object* v___y_1219_; lean_object* v___y_1220_; 
v___x_1216_ = 0;
lean_inc_ref(v_fileMap_1208_);
lean_inc_ref(v_fileName_1207_);
v___x_1217_ = l_Lean_Elab_mkMessageCore(v_fileName_1207_, v_fileMap_1208_, v___x_1215_, v___x_1216_, v_fst_1195_, v_snd_1196_);
lean_dec(v_snd_1196_);
lean_dec(v_fst_1195_);
if (v_suppressElabErrors_1206_ == 0)
{
v___y_1219_ = v___y_1179_;
v___y_1220_ = v___y_1180_;
goto v___jp_1218_;
}
else
{
lean_object* v_data_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___f_1264_; uint8_t v___x_1265_; 
v_data_1261_ = lean_ctor_get(v___x_1217_, 4);
lean_inc(v_data_1261_);
v___x_1262_ = lean_box(v_suppressElabErrors_1206_);
v___x_1263_ = lean_box(v___x_1174_);
v___f_1264_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1264_, 0, v___x_1262_);
lean_closure_set(v___f_1264_, 1, v___x_1263_);
lean_closure_set(v___f_1264_, 2, v___x_1210_);
v___x_1265_ = l_Lean_MessageData_hasTag(v___f_1264_, v_data_1261_);
if (v___x_1265_ == 0)
{
lean_dec_ref(v___x_1217_);
lean_del_object(v___x_1193_);
v_a_1183_ = v___x_1209_;
goto v___jp_1182_;
}
else
{
v___y_1219_ = v___y_1179_;
v___y_1220_ = v___y_1180_;
goto v___jp_1218_;
}
}
v___jp_1218_:
{
lean_object* v___x_1221_; lean_object* v_fileName_1222_; lean_object* v_pos_1223_; lean_object* v_endPos_1224_; uint8_t v_keepFullRange_1225_; uint8_t v_severity_1226_; uint8_t v_isSilent_1227_; lean_object* v_caption_1228_; lean_object* v_data_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1260_; 
v___x_1221_ = lean_st_ref_take(v___y_1220_);
v_fileName_1222_ = lean_ctor_get(v___x_1217_, 0);
v_pos_1223_ = lean_ctor_get(v___x_1217_, 1);
v_endPos_1224_ = lean_ctor_get(v___x_1217_, 2);
v_keepFullRange_1225_ = lean_ctor_get_uint8(v___x_1217_, sizeof(void*)*5);
v_severity_1226_ = lean_ctor_get_uint8(v___x_1217_, sizeof(void*)*5 + 1);
v_isSilent_1227_ = lean_ctor_get_uint8(v___x_1217_, sizeof(void*)*5 + 2);
v_caption_1228_ = lean_ctor_get(v___x_1217_, 3);
v_data_1229_ = lean_ctor_get(v___x_1217_, 4);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1231_ = v___x_1217_;
v_isShared_1232_ = v_isSharedCheck_1260_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_data_1229_);
lean_inc(v_caption_1228_);
lean_inc(v_endPos_1224_);
lean_inc(v_pos_1223_);
lean_inc(v_fileName_1222_);
lean_dec(v___x_1217_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1260_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v_currNamespace_1233_; lean_object* v_openDecls_1234_; lean_object* v_env_1235_; lean_object* v_nextMacroScope_1236_; lean_object* v_ngen_1237_; lean_object* v_auxDeclNGen_1238_; lean_object* v_traceState_1239_; lean_object* v_cache_1240_; lean_object* v_messages_1241_; lean_object* v_infoState_1242_; lean_object* v_snapshotTasks_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1259_; 
v_currNamespace_1233_ = lean_ctor_get(v___y_1219_, 5);
v_openDecls_1234_ = lean_ctor_get(v___y_1219_, 6);
v_env_1235_ = lean_ctor_get(v___x_1221_, 0);
v_nextMacroScope_1236_ = lean_ctor_get(v___x_1221_, 1);
v_ngen_1237_ = lean_ctor_get(v___x_1221_, 2);
v_auxDeclNGen_1238_ = lean_ctor_get(v___x_1221_, 3);
v_traceState_1239_ = lean_ctor_get(v___x_1221_, 4);
v_cache_1240_ = lean_ctor_get(v___x_1221_, 5);
v_messages_1241_ = lean_ctor_get(v___x_1221_, 6);
v_infoState_1242_ = lean_ctor_get(v___x_1221_, 7);
v_snapshotTasks_1243_ = lean_ctor_get(v___x_1221_, 8);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1245_ = v___x_1221_;
v_isShared_1246_ = v_isSharedCheck_1259_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_snapshotTasks_1243_);
lean_inc(v_infoState_1242_);
lean_inc(v_messages_1241_);
lean_inc(v_cache_1240_);
lean_inc(v_traceState_1239_);
lean_inc(v_auxDeclNGen_1238_);
lean_inc(v_ngen_1237_);
lean_inc(v_nextMacroScope_1236_);
lean_inc(v_env_1235_);
lean_dec(v___x_1221_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1259_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
lean_inc(v_openDecls_1234_);
lean_inc(v_currNamespace_1233_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 1, v_openDecls_1234_);
lean_ctor_set(v___x_1193_, 0, v_currNamespace_1233_);
v___x_1248_ = v___x_1193_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_currNamespace_1233_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v_openDecls_1234_);
v___x_1248_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
lean_object* v___x_1249_; lean_object* v___x_1251_; 
v___x_1249_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1248_);
lean_ctor_set(v___x_1249_, 1, v_data_1229_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 4, v___x_1249_);
v___x_1251_ = v___x_1231_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_fileName_1222_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v_pos_1223_);
lean_ctor_set(v_reuseFailAlloc_1257_, 2, v_endPos_1224_);
lean_ctor_set(v_reuseFailAlloc_1257_, 3, v_caption_1228_);
lean_ctor_set(v_reuseFailAlloc_1257_, 4, v___x_1249_);
lean_ctor_set_uint8(v_reuseFailAlloc_1257_, sizeof(void*)*5, v_keepFullRange_1225_);
lean_ctor_set_uint8(v_reuseFailAlloc_1257_, sizeof(void*)*5 + 1, v_severity_1226_);
lean_ctor_set_uint8(v_reuseFailAlloc_1257_, sizeof(void*)*5 + 2, v_isSilent_1227_);
v___x_1251_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1252_; lean_object* v___x_1254_; 
v___x_1252_ = l_Lean_MessageLog_add(v___x_1251_, v_messages_1241_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 6, v___x_1252_);
v___x_1254_ = v___x_1245_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_env_1235_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v_nextMacroScope_1236_);
lean_ctor_set(v_reuseFailAlloc_1256_, 2, v_ngen_1237_);
lean_ctor_set(v_reuseFailAlloc_1256_, 3, v_auxDeclNGen_1238_);
lean_ctor_set(v_reuseFailAlloc_1256_, 4, v_traceState_1239_);
lean_ctor_set(v_reuseFailAlloc_1256_, 5, v_cache_1240_);
lean_ctor_set(v_reuseFailAlloc_1256_, 6, v___x_1252_);
lean_ctor_set(v_reuseFailAlloc_1256_, 7, v_infoState_1242_);
lean_ctor_set(v_reuseFailAlloc_1256_, 8, v_snapshotTasks_1243_);
v___x_1254_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
lean_object* v___x_1255_; 
v___x_1255_ = lean_st_ref_put(v___y_1220_, v___x_1254_);
v_a_1183_ = v___x_1209_;
goto v___jp_1182_;
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
v___jp_1182_:
{
size_t v___x_1184_; size_t v___x_1185_; 
v___x_1184_ = ((size_t)1ULL);
v___x_1185_ = lean_usize_add(v_i_1177_, v___x_1184_);
v_i_1177_ = v___x_1185_;
v_b_1178_ = v_a_1183_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___boxed(lean_object* v___x_1269_, lean_object* v_as_1270_, lean_object* v_sz_1271_, lean_object* v_i_1272_, lean_object* v_b_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
uint8_t v___x_36199__boxed_1277_; size_t v_sz_boxed_1278_; size_t v_i_boxed_1279_; lean_object* v_res_1280_; 
v___x_36199__boxed_1277_ = lean_unbox(v___x_1269_);
v_sz_boxed_1278_ = lean_unbox_usize(v_sz_1271_);
lean_dec(v_sz_1271_);
v_i_boxed_1279_ = lean_unbox_usize(v_i_1272_);
lean_dec(v_i_1272_);
v_res_1280_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(v___x_36199__boxed_1277_, v_as_1270_, v_sz_boxed_1278_, v_i_boxed_1279_, v_b_1273_, v___y_1274_, v___y_1275_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec_ref(v_as_1270_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(lean_object* v_opts_1281_, lean_object* v_opt_1282_){
_start:
{
lean_object* v_name_1283_; lean_object* v_map_1284_; lean_object* v___x_1285_; 
v_name_1283_ = lean_ctor_get(v_opt_1282_, 0);
v_map_1284_ = lean_ctor_get(v_opts_1281_, 0);
v___x_1285_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1284_, v_name_1283_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v___x_1286_; 
v___x_1286_ = lean_box(0);
return v___x_1286_;
}
else
{
lean_object* v_val_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1296_; 
v_val_1287_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1289_ = v___x_1285_;
v_isShared_1290_ = v_isSharedCheck_1296_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_val_1287_);
lean_dec(v___x_1285_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1296_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
if (lean_obj_tag(v_val_1287_) == 0)
{
lean_object* v_v_1291_; lean_object* v___x_1293_; 
v_v_1291_ = lean_ctor_get(v_val_1287_, 0);
lean_inc_ref(v_v_1291_);
lean_dec_ref_known(v_val_1287_, 1);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v_v_1291_);
v___x_1293_ = v___x_1289_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_v_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
else
{
lean_object* v___x_1295_; 
lean_del_object(v___x_1289_);
lean_dec(v_val_1287_);
v___x_1295_ = lean_box(0);
return v___x_1295_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15___boxed(lean_object* v_opts_1297_, lean_object* v_opt_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(v_opts_1297_, v_opt_1298_);
lean_dec_ref(v_opt_1298_);
lean_dec_ref(v_opts_1297_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(lean_object* v_a_1300_, lean_object* v_fallback_1301_, lean_object* v_x_1302_){
_start:
{
if (lean_obj_tag(v_x_1302_) == 0)
{
lean_inc(v_fallback_1301_);
return v_fallback_1301_;
}
else
{
lean_object* v_key_1303_; lean_object* v_value_1304_; lean_object* v_tail_1305_; lean_object* v_fst_1306_; lean_object* v_snd_1307_; lean_object* v_fst_1308_; lean_object* v_snd_1309_; uint8_t v_decide_1310_; 
v_key_1303_ = lean_ctor_get(v_x_1302_, 0);
v_value_1304_ = lean_ctor_get(v_x_1302_, 1);
v_tail_1305_ = lean_ctor_get(v_x_1302_, 2);
v_fst_1306_ = lean_ctor_get(v_key_1303_, 0);
v_snd_1307_ = lean_ctor_get(v_key_1303_, 1);
v_fst_1308_ = lean_ctor_get(v_a_1300_, 0);
v_snd_1309_ = lean_ctor_get(v_a_1300_, 1);
v_decide_1310_ = lean_nat_dec_eq(v_fst_1306_, v_fst_1308_);
if (v_decide_1310_ == 0)
{
v_x_1302_ = v_tail_1305_;
goto _start;
}
else
{
uint8_t v_decide_1312_; 
v_decide_1312_ = lean_nat_dec_eq(v_snd_1307_, v_snd_1309_);
if (v_decide_1312_ == 0)
{
v_x_1302_ = v_tail_1305_;
goto _start;
}
else
{
lean_inc(v_value_1304_);
return v_value_1304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg___boxed(lean_object* v_a_1314_, lean_object* v_fallback_1315_, lean_object* v_x_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_1314_, v_fallback_1315_, v_x_1316_);
lean_dec(v_x_1316_);
lean_dec(v_fallback_1315_);
lean_dec_ref(v_a_1314_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(lean_object* v_m_1318_, lean_object* v_a_1319_, lean_object* v_fallback_1320_){
_start:
{
lean_object* v_buckets_1321_; lean_object* v_fst_1322_; lean_object* v_snd_1323_; lean_object* v___x_1324_; uint64_t v___x_1325_; uint64_t v___x_1326_; uint64_t v___x_1327_; uint64_t v___x_1328_; uint64_t v___x_1329_; uint64_t v_fold_1330_; uint64_t v___x_1331_; uint64_t v___x_1332_; uint64_t v___x_1333_; size_t v___x_1334_; size_t v___x_1335_; size_t v___x_1336_; size_t v___x_1337_; size_t v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v_buckets_1321_ = lean_ctor_get(v_m_1318_, 1);
v_fst_1322_ = lean_ctor_get(v_a_1319_, 0);
v_snd_1323_ = lean_ctor_get(v_a_1319_, 1);
v___x_1324_ = lean_array_get_size(v_buckets_1321_);
v___x_1325_ = l_String_instHashableRaw_hash(v_fst_1322_);
v___x_1326_ = l_String_instHashableRaw_hash(v_snd_1323_);
v___x_1327_ = lean_uint64_mix_hash(v___x_1325_, v___x_1326_);
v___x_1328_ = 32ULL;
v___x_1329_ = lean_uint64_shift_right(v___x_1327_, v___x_1328_);
v_fold_1330_ = lean_uint64_xor(v___x_1327_, v___x_1329_);
v___x_1331_ = 16ULL;
v___x_1332_ = lean_uint64_shift_right(v_fold_1330_, v___x_1331_);
v___x_1333_ = lean_uint64_xor(v_fold_1330_, v___x_1332_);
v___x_1334_ = lean_uint64_to_usize(v___x_1333_);
v___x_1335_ = lean_usize_of_nat(v___x_1324_);
v___x_1336_ = ((size_t)1ULL);
v___x_1337_ = lean_usize_sub(v___x_1335_, v___x_1336_);
v___x_1338_ = lean_usize_land(v___x_1334_, v___x_1337_);
v___x_1339_ = lean_array_uget_borrowed(v_buckets_1321_, v___x_1338_);
v___x_1340_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_1319_, v_fallback_1320_, v___x_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg___boxed(lean_object* v_m_1341_, lean_object* v_a_1342_, lean_object* v_fallback_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_m_1341_, v_a_1342_, v_fallback_1343_);
lean_dec(v_fallback_1343_);
lean_dec_ref(v_a_1342_);
lean_dec_ref(v_m_1341_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(lean_object* v_x_1345_, lean_object* v_x_1346_){
_start:
{
if (lean_obj_tag(v_x_1346_) == 0)
{
return v_x_1345_;
}
else
{
lean_object* v_key_1347_; lean_object* v_value_1348_; lean_object* v_tail_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1376_; 
v_key_1347_ = lean_ctor_get(v_x_1346_, 0);
v_value_1348_ = lean_ctor_get(v_x_1346_, 1);
v_tail_1349_ = lean_ctor_get(v_x_1346_, 2);
v_isSharedCheck_1376_ = !lean_is_exclusive(v_x_1346_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1351_ = v_x_1346_;
v_isShared_1352_ = v_isSharedCheck_1376_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_tail_1349_);
lean_inc(v_value_1348_);
lean_inc(v_key_1347_);
lean_dec(v_x_1346_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1376_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v_fst_1353_; lean_object* v_snd_1354_; lean_object* v___x_1355_; uint64_t v___x_1356_; uint64_t v___x_1357_; uint64_t v___x_1358_; uint64_t v___x_1359_; uint64_t v___x_1360_; uint64_t v_fold_1361_; uint64_t v___x_1362_; uint64_t v___x_1363_; uint64_t v___x_1364_; size_t v___x_1365_; size_t v___x_1366_; size_t v___x_1367_; size_t v___x_1368_; size_t v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1372_; 
v_fst_1353_ = lean_ctor_get(v_key_1347_, 0);
v_snd_1354_ = lean_ctor_get(v_key_1347_, 1);
v___x_1355_ = lean_array_get_size(v_x_1345_);
v___x_1356_ = l_String_instHashableRaw_hash(v_fst_1353_);
v___x_1357_ = l_String_instHashableRaw_hash(v_snd_1354_);
v___x_1358_ = lean_uint64_mix_hash(v___x_1356_, v___x_1357_);
v___x_1359_ = 32ULL;
v___x_1360_ = lean_uint64_shift_right(v___x_1358_, v___x_1359_);
v_fold_1361_ = lean_uint64_xor(v___x_1358_, v___x_1360_);
v___x_1362_ = 16ULL;
v___x_1363_ = lean_uint64_shift_right(v_fold_1361_, v___x_1362_);
v___x_1364_ = lean_uint64_xor(v_fold_1361_, v___x_1363_);
v___x_1365_ = lean_uint64_to_usize(v___x_1364_);
v___x_1366_ = lean_usize_of_nat(v___x_1355_);
v___x_1367_ = ((size_t)1ULL);
v___x_1368_ = lean_usize_sub(v___x_1366_, v___x_1367_);
v___x_1369_ = lean_usize_land(v___x_1365_, v___x_1368_);
v___x_1370_ = lean_array_uget_borrowed(v_x_1345_, v___x_1369_);
lean_inc(v___x_1370_);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 2, v___x_1370_);
v___x_1372_ = v___x_1351_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_key_1347_);
lean_ctor_set(v_reuseFailAlloc_1375_, 1, v_value_1348_);
lean_ctor_set(v_reuseFailAlloc_1375_, 2, v___x_1370_);
v___x_1372_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
lean_object* v___x_1373_; 
v___x_1373_ = lean_array_uset(v_x_1345_, v___x_1369_, v___x_1372_);
v_x_1345_ = v___x_1373_;
v_x_1346_ = v_tail_1349_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(lean_object* v_i_1377_, lean_object* v_source_1378_, lean_object* v_target_1379_){
_start:
{
lean_object* v___x_1380_; uint8_t v___x_1381_; 
v___x_1380_ = lean_array_get_size(v_source_1378_);
v___x_1381_ = lean_nat_dec_lt(v_i_1377_, v___x_1380_);
if (v___x_1381_ == 0)
{
lean_dec_ref(v_source_1378_);
lean_dec(v_i_1377_);
return v_target_1379_;
}
else
{
lean_object* v_es_1382_; lean_object* v___x_1383_; lean_object* v_source_1384_; lean_object* v_target_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v_es_1382_ = lean_array_fget(v_source_1378_, v_i_1377_);
v___x_1383_ = lean_box(0);
v_source_1384_ = lean_array_fset(v_source_1378_, v_i_1377_, v___x_1383_);
v_target_1385_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(v_target_1379_, v_es_1382_);
v___x_1386_ = lean_unsigned_to_nat(1u);
v___x_1387_ = lean_nat_add(v_i_1377_, v___x_1386_);
lean_dec(v_i_1377_);
v_i_1377_ = v___x_1387_;
v_source_1378_ = v_source_1384_;
v_target_1379_ = v_target_1385_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(lean_object* v_data_1389_){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v_nbuckets_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1390_ = lean_array_get_size(v_data_1389_);
v___x_1391_ = lean_unsigned_to_nat(2u);
v_nbuckets_1392_ = lean_nat_mul(v___x_1390_, v___x_1391_);
v___x_1393_ = lean_unsigned_to_nat(0u);
v___x_1394_ = lean_box(0);
v___x_1395_ = lean_mk_array(v_nbuckets_1392_, v___x_1394_);
v___x_1396_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(v___x_1393_, v_data_1389_, v___x_1395_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(lean_object* v_a_1397_, lean_object* v_b_1398_, lean_object* v_x_1399_){
_start:
{
if (lean_obj_tag(v_x_1399_) == 0)
{
lean_dec(v_b_1398_);
lean_dec_ref(v_a_1397_);
return v_x_1399_;
}
else
{
lean_object* v_key_1400_; lean_object* v_value_1401_; lean_object* v_tail_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1418_; 
v_key_1400_ = lean_ctor_get(v_x_1399_, 0);
v_value_1401_ = lean_ctor_get(v_x_1399_, 1);
v_tail_1402_ = lean_ctor_get(v_x_1399_, 2);
v_isSharedCheck_1418_ = !lean_is_exclusive(v_x_1399_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1404_ = v_x_1399_;
v_isShared_1405_ = v_isSharedCheck_1418_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_tail_1402_);
lean_inc(v_value_1401_);
lean_inc(v_key_1400_);
lean_dec(v_x_1399_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1418_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v_fst_1411_; lean_object* v_snd_1412_; lean_object* v_fst_1413_; lean_object* v_snd_1414_; uint8_t v_decide_1415_; 
v_fst_1411_ = lean_ctor_get(v_key_1400_, 0);
v_snd_1412_ = lean_ctor_get(v_key_1400_, 1);
v_fst_1413_ = lean_ctor_get(v_a_1397_, 0);
v_snd_1414_ = lean_ctor_get(v_a_1397_, 1);
v_decide_1415_ = lean_nat_dec_eq(v_fst_1411_, v_fst_1413_);
if (v_decide_1415_ == 0)
{
goto v___jp_1406_;
}
else
{
uint8_t v_decide_1416_; 
v_decide_1416_ = lean_nat_dec_eq(v_snd_1412_, v_snd_1414_);
if (v_decide_1416_ == 0)
{
goto v___jp_1406_;
}
else
{
lean_object* v___x_1417_; 
lean_del_object(v___x_1404_);
lean_dec(v_value_1401_);
lean_dec(v_key_1400_);
v___x_1417_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1417_, 0, v_a_1397_);
lean_ctor_set(v___x_1417_, 1, v_b_1398_);
lean_ctor_set(v___x_1417_, 2, v_tail_1402_);
return v___x_1417_;
}
}
v___jp_1406_:
{
lean_object* v___x_1407_; lean_object* v___x_1409_; 
v___x_1407_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_1397_, v_b_1398_, v_tail_1402_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 2, v___x_1407_);
v___x_1409_ = v___x_1404_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_key_1400_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_value_1401_);
lean_ctor_set(v_reuseFailAlloc_1410_, 2, v___x_1407_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(lean_object* v_a_1419_, lean_object* v_x_1420_){
_start:
{
if (lean_obj_tag(v_x_1420_) == 0)
{
uint8_t v___x_1421_; 
v___x_1421_ = 0;
return v___x_1421_;
}
else
{
lean_object* v_key_1422_; lean_object* v_tail_1423_; lean_object* v_fst_1424_; lean_object* v_snd_1425_; lean_object* v_fst_1426_; lean_object* v_snd_1427_; uint8_t v_decide_1428_; 
v_key_1422_ = lean_ctor_get(v_x_1420_, 0);
v_tail_1423_ = lean_ctor_get(v_x_1420_, 2);
v_fst_1424_ = lean_ctor_get(v_key_1422_, 0);
v_snd_1425_ = lean_ctor_get(v_key_1422_, 1);
v_fst_1426_ = lean_ctor_get(v_a_1419_, 0);
v_snd_1427_ = lean_ctor_get(v_a_1419_, 1);
v_decide_1428_ = lean_nat_dec_eq(v_fst_1424_, v_fst_1426_);
if (v_decide_1428_ == 0)
{
v_x_1420_ = v_tail_1423_;
goto _start;
}
else
{
uint8_t v_decide_1430_; 
v_decide_1430_ = lean_nat_dec_eq(v_snd_1425_, v_snd_1427_);
if (v_decide_1430_ == 0)
{
v_x_1420_ = v_tail_1423_;
goto _start;
}
else
{
return v_decide_1430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg___boxed(lean_object* v_a_1432_, lean_object* v_x_1433_){
_start:
{
uint8_t v_res_1434_; lean_object* v_r_1435_; 
v_res_1434_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_1432_, v_x_1433_);
lean_dec(v_x_1433_);
lean_dec_ref(v_a_1432_);
v_r_1435_ = lean_box(v_res_1434_);
return v_r_1435_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(lean_object* v_m_1436_, lean_object* v_a_1437_, lean_object* v_b_1438_){
_start:
{
lean_object* v_size_1439_; lean_object* v_buckets_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1487_; 
v_size_1439_ = lean_ctor_get(v_m_1436_, 0);
v_buckets_1440_ = lean_ctor_get(v_m_1436_, 1);
v_isSharedCheck_1487_ = !lean_is_exclusive(v_m_1436_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1442_ = v_m_1436_;
v_isShared_1443_ = v_isSharedCheck_1487_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_buckets_1440_);
lean_inc(v_size_1439_);
lean_dec(v_m_1436_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1487_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v_fst_1444_; lean_object* v_snd_1445_; lean_object* v___x_1446_; uint64_t v___x_1447_; uint64_t v___x_1448_; uint64_t v___x_1449_; uint64_t v___x_1450_; uint64_t v___x_1451_; uint64_t v_fold_1452_; uint64_t v___x_1453_; uint64_t v___x_1454_; uint64_t v___x_1455_; size_t v___x_1456_; size_t v___x_1457_; size_t v___x_1458_; size_t v___x_1459_; size_t v___x_1460_; lean_object* v_bkt_1461_; uint8_t v___x_1462_; 
v_fst_1444_ = lean_ctor_get(v_a_1437_, 0);
v_snd_1445_ = lean_ctor_get(v_a_1437_, 1);
v___x_1446_ = lean_array_get_size(v_buckets_1440_);
v___x_1447_ = l_String_instHashableRaw_hash(v_fst_1444_);
v___x_1448_ = l_String_instHashableRaw_hash(v_snd_1445_);
v___x_1449_ = lean_uint64_mix_hash(v___x_1447_, v___x_1448_);
v___x_1450_ = 32ULL;
v___x_1451_ = lean_uint64_shift_right(v___x_1449_, v___x_1450_);
v_fold_1452_ = lean_uint64_xor(v___x_1449_, v___x_1451_);
v___x_1453_ = 16ULL;
v___x_1454_ = lean_uint64_shift_right(v_fold_1452_, v___x_1453_);
v___x_1455_ = lean_uint64_xor(v_fold_1452_, v___x_1454_);
v___x_1456_ = lean_uint64_to_usize(v___x_1455_);
v___x_1457_ = lean_usize_of_nat(v___x_1446_);
v___x_1458_ = ((size_t)1ULL);
v___x_1459_ = lean_usize_sub(v___x_1457_, v___x_1458_);
v___x_1460_ = lean_usize_land(v___x_1456_, v___x_1459_);
v_bkt_1461_ = lean_array_uget_borrowed(v_buckets_1440_, v___x_1460_);
v___x_1462_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_1437_, v_bkt_1461_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; lean_object* v_size_x27_1464_; lean_object* v___x_1465_; lean_object* v_buckets_x27_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; uint8_t v___x_1472_; 
v___x_1463_ = lean_unsigned_to_nat(1u);
v_size_x27_1464_ = lean_nat_add(v_size_1439_, v___x_1463_);
lean_dec(v_size_1439_);
lean_inc(v_bkt_1461_);
v___x_1465_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1465_, 0, v_a_1437_);
lean_ctor_set(v___x_1465_, 1, v_b_1438_);
lean_ctor_set(v___x_1465_, 2, v_bkt_1461_);
v_buckets_x27_1466_ = lean_array_uset(v_buckets_1440_, v___x_1460_, v___x_1465_);
v___x_1467_ = lean_unsigned_to_nat(4u);
v___x_1468_ = lean_nat_mul(v_size_x27_1464_, v___x_1467_);
v___x_1469_ = lean_unsigned_to_nat(3u);
v___x_1470_ = lean_nat_div(v___x_1468_, v___x_1469_);
lean_dec(v___x_1468_);
v___x_1471_ = lean_array_get_size(v_buckets_x27_1466_);
v___x_1472_ = lean_nat_dec_le(v___x_1470_, v___x_1471_);
lean_dec(v___x_1470_);
if (v___x_1472_ == 0)
{
lean_object* v_val_1473_; lean_object* v___x_1475_; 
v_val_1473_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(v_buckets_x27_1466_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 1, v_val_1473_);
lean_ctor_set(v___x_1442_, 0, v_size_x27_1464_);
v___x_1475_ = v___x_1442_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_size_x27_1464_);
lean_ctor_set(v_reuseFailAlloc_1476_, 1, v_val_1473_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
else
{
lean_object* v___x_1478_; 
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 1, v_buckets_x27_1466_);
lean_ctor_set(v___x_1442_, 0, v_size_x27_1464_);
v___x_1478_ = v___x_1442_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_size_x27_1464_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_buckets_x27_1466_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
else
{
lean_object* v___x_1480_; lean_object* v_buckets_x27_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1485_; 
lean_inc(v_bkt_1461_);
v___x_1480_ = lean_box(0);
v_buckets_x27_1481_ = lean_array_uset(v_buckets_1440_, v___x_1460_, v___x_1480_);
v___x_1482_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_1437_, v_b_1438_, v_bkt_1461_);
v___x_1483_ = lean_array_uset(v_buckets_x27_1481_, v___x_1460_, v___x_1482_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 1, v___x_1483_);
v___x_1485_ = v___x_1442_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_size_1439_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v___x_1483_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(uint8_t v___x_1490_, lean_object* v_as_1491_, size_t v_sz_1492_, size_t v_i_1493_, lean_object* v_b_1494_, lean_object* v___y_1495_){
_start:
{
uint8_t v___x_1497_; 
v___x_1497_ = lean_usize_dec_lt(v_i_1493_, v_sz_1492_);
if (v___x_1497_ == 0)
{
lean_object* v___x_1498_; 
v___x_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1498_, 0, v_b_1494_);
return v___x_1498_;
}
else
{
lean_object* v_snd_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1536_; 
v_snd_1499_ = lean_ctor_get(v_b_1494_, 1);
v_isSharedCheck_1536_ = !lean_is_exclusive(v_b_1494_);
if (v_isSharedCheck_1536_ == 0)
{
lean_object* v_unused_1537_; 
v_unused_1537_ = lean_ctor_get(v_b_1494_, 0);
lean_dec(v_unused_1537_);
v___x_1501_ = v_b_1494_;
v_isShared_1502_ = v_isSharedCheck_1536_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_snd_1499_);
lean_dec(v_b_1494_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1536_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v_ref_1503_; lean_object* v_a_1504_; lean_object* v_ref_1505_; lean_object* v_msg_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1535_; 
v_ref_1503_ = lean_ctor_get(v___y_1495_, 4);
v_a_1504_ = lean_array_uget(v_as_1491_, v_i_1493_);
v_ref_1505_ = lean_ctor_get(v_a_1504_, 0);
v_msg_1506_ = lean_ctor_get(v_a_1504_, 1);
v_isSharedCheck_1535_ = !lean_is_exclusive(v_a_1504_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1508_ = v_a_1504_;
v_isShared_1509_ = v_isSharedCheck_1535_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_msg_1506_);
lean_inc(v_ref_1505_);
lean_dec(v_a_1504_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1535_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1510_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v_ref_1527_; lean_object* v___y_1529_; lean_object* v___x_1532_; 
v___x_1510_ = lean_box(0);
v_ref_1527_ = l_Lean_replaceRef(v_ref_1505_, v_ref_1503_);
lean_dec(v_ref_1505_);
v___x_1532_ = l_Lean_Syntax_getPos_x3f(v_ref_1527_, v___x_1490_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v___x_1533_; 
v___x_1533_ = lean_unsigned_to_nat(0u);
v___y_1529_ = v___x_1533_;
goto v___jp_1528_;
}
else
{
lean_object* v_val_1534_; 
v_val_1534_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_val_1534_);
lean_dec_ref_known(v___x_1532_, 1);
v___y_1529_ = v_val_1534_;
goto v___jp_1528_;
}
v___jp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 1, v___y_1513_);
lean_ctor_set(v___x_1501_, 0, v___y_1512_);
v___x_1515_ = v___x_1501_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___y_1512_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v___y_1513_);
v___x_1515_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v_pos2traces_1519_; lean_object* v___x_1521_; 
v___x_1516_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1517_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1499_, v___x_1515_, v___x_1516_);
v___x_1518_ = lean_array_push(v___x_1517_, v_msg_1506_);
v_pos2traces_1519_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1499_, v___x_1515_, v___x_1518_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 1, v_pos2traces_1519_);
lean_ctor_set(v___x_1508_, 0, v___x_1510_);
v___x_1521_ = v___x_1508_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1510_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_pos2traces_1519_);
v___x_1521_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
size_t v___x_1522_; size_t v___x_1523_; 
v___x_1522_ = ((size_t)1ULL);
v___x_1523_ = lean_usize_add(v_i_1493_, v___x_1522_);
v_i_1493_ = v___x_1523_;
v_b_1494_ = v___x_1521_;
goto _start;
}
}
}
v___jp_1528_:
{
lean_object* v___x_1530_; 
v___x_1530_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1527_, v___x_1490_);
lean_dec(v_ref_1527_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_inc(v___y_1529_);
v___y_1512_ = v___y_1529_;
v___y_1513_ = v___y_1529_;
goto v___jp_1511_;
}
else
{
lean_object* v_val_1531_; 
v_val_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_val_1531_);
lean_dec_ref_known(v___x_1530_, 1);
v___y_1512_ = v___y_1529_;
v___y_1513_ = v_val_1531_;
goto v___jp_1511_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___boxed(lean_object* v___x_1538_, lean_object* v_as_1539_, lean_object* v_sz_1540_, lean_object* v_i_1541_, lean_object* v_b_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
uint8_t v___x_36668__boxed_1545_; size_t v_sz_boxed_1546_; size_t v_i_boxed_1547_; lean_object* v_res_1548_; 
v___x_36668__boxed_1545_ = lean_unbox(v___x_1538_);
v_sz_boxed_1546_ = lean_unbox_usize(v_sz_1540_);
lean_dec(v_sz_1540_);
v_i_boxed_1547_ = lean_unbox_usize(v_i_1541_);
lean_dec(v_i_1541_);
v_res_1548_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_36668__boxed_1545_, v_as_1539_, v_sz_boxed_1546_, v_i_boxed_1547_, v_b_1542_, v___y_1543_);
lean_dec_ref(v___y_1543_);
lean_dec_ref(v_as_1539_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(uint8_t v___x_1549_, lean_object* v_as_1550_, size_t v_sz_1551_, size_t v_i_1552_, lean_object* v_b_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
uint8_t v___x_1557_; 
v___x_1557_ = lean_usize_dec_lt(v_i_1552_, v_sz_1551_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; 
v___x_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1558_, 0, v_b_1553_);
return v___x_1558_;
}
else
{
lean_object* v_snd_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1596_; 
v_snd_1559_ = lean_ctor_get(v_b_1553_, 1);
v_isSharedCheck_1596_ = !lean_is_exclusive(v_b_1553_);
if (v_isSharedCheck_1596_ == 0)
{
lean_object* v_unused_1597_; 
v_unused_1597_ = lean_ctor_get(v_b_1553_, 0);
lean_dec(v_unused_1597_);
v___x_1561_ = v_b_1553_;
v_isShared_1562_ = v_isSharedCheck_1596_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_snd_1559_);
lean_dec(v_b_1553_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1596_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v_ref_1563_; lean_object* v_a_1564_; lean_object* v_ref_1565_; lean_object* v_msg_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1595_; 
v_ref_1563_ = lean_ctor_get(v___y_1554_, 4);
v_a_1564_ = lean_array_uget(v_as_1550_, v_i_1552_);
v_ref_1565_ = lean_ctor_get(v_a_1564_, 0);
v_msg_1566_ = lean_ctor_get(v_a_1564_, 1);
v_isSharedCheck_1595_ = !lean_is_exclusive(v_a_1564_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1568_ = v_a_1564_;
v_isShared_1569_ = v_isSharedCheck_1595_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_msg_1566_);
lean_inc(v_ref_1565_);
lean_dec(v_a_1564_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1595_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1570_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v_ref_1587_; lean_object* v___y_1589_; lean_object* v___x_1592_; 
v___x_1570_ = lean_box(0);
v_ref_1587_ = l_Lean_replaceRef(v_ref_1565_, v_ref_1563_);
lean_dec(v_ref_1565_);
v___x_1592_ = l_Lean_Syntax_getPos_x3f(v_ref_1587_, v___x_1549_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v___x_1593_; 
v___x_1593_ = lean_unsigned_to_nat(0u);
v___y_1589_ = v___x_1593_;
goto v___jp_1588_;
}
else
{
lean_object* v_val_1594_; 
v_val_1594_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_val_1594_);
lean_dec_ref_known(v___x_1592_, 1);
v___y_1589_ = v_val_1594_;
goto v___jp_1588_;
}
v___jp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 1, v___y_1573_);
lean_ctor_set(v___x_1561_, 0, v___y_1572_);
v___x_1575_ = v___x_1561_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___y_1572_);
lean_ctor_set(v_reuseFailAlloc_1586_, 1, v___y_1573_);
v___x_1575_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v_pos2traces_1579_; lean_object* v___x_1581_; 
v___x_1576_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1577_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1559_, v___x_1575_, v___x_1576_);
v___x_1578_ = lean_array_push(v___x_1577_, v_msg_1566_);
v_pos2traces_1579_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1559_, v___x_1575_, v___x_1578_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 1, v_pos2traces_1579_);
lean_ctor_set(v___x_1568_, 0, v___x_1570_);
v___x_1581_ = v___x_1568_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1570_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v_pos2traces_1579_);
v___x_1581_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
size_t v___x_1582_; size_t v___x_1583_; lean_object* v___x_1584_; 
v___x_1582_ = ((size_t)1ULL);
v___x_1583_ = lean_usize_add(v_i_1552_, v___x_1582_);
v___x_1584_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_1549_, v_as_1550_, v_sz_1551_, v___x_1583_, v___x_1581_, v___y_1554_);
return v___x_1584_;
}
}
}
v___jp_1588_:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1587_, v___x_1549_);
lean_dec(v_ref_1587_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_inc(v___y_1589_);
v___y_1572_ = v___y_1589_;
v___y_1573_ = v___y_1589_;
goto v___jp_1571_;
}
else
{
lean_object* v_val_1591_; 
v_val_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_val_1591_);
lean_dec_ref_known(v___x_1590_, 1);
v___y_1572_ = v___y_1589_;
v___y_1573_ = v_val_1591_;
goto v___jp_1571_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40___boxed(lean_object* v___x_1598_, lean_object* v_as_1599_, lean_object* v_sz_1600_, lean_object* v_i_1601_, lean_object* v_b_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
uint8_t v___x_36749__boxed_1606_; size_t v_sz_boxed_1607_; size_t v_i_boxed_1608_; lean_object* v_res_1609_; 
v___x_36749__boxed_1606_ = lean_unbox(v___x_1598_);
v_sz_boxed_1607_ = lean_unbox_usize(v_sz_1600_);
lean_dec(v_sz_1600_);
v_i_boxed_1608_ = lean_unbox_usize(v_i_1601_);
lean_dec(v_i_1601_);
v_res_1609_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(v___x_36749__boxed_1606_, v_as_1599_, v_sz_boxed_1607_, v_i_boxed_1608_, v_b_1602_, v___y_1603_, v___y_1604_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec_ref(v_as_1599_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(lean_object* v_init_1610_, uint8_t v___x_1611_, lean_object* v_n_1612_, lean_object* v_b_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
if (lean_obj_tag(v_n_1612_) == 0)
{
lean_object* v_cs_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; size_t v_sz_1620_; size_t v___x_1621_; lean_object* v___x_1622_; 
v_cs_1617_ = lean_ctor_get(v_n_1612_, 0);
v___x_1618_ = lean_box(0);
v___x_1619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
lean_ctor_set(v___x_1619_, 1, v_b_1613_);
v_sz_1620_ = lean_array_size(v_cs_1617_);
v___x_1621_ = ((size_t)0ULL);
v___x_1622_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(v_init_1610_, v___x_1611_, v_cs_1617_, v_sz_1620_, v___x_1621_, v___x_1619_, v___y_1614_, v___y_1615_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1637_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1625_ = v___x_1622_;
v_isShared_1626_ = v_isSharedCheck_1637_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1622_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1637_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v_fst_1627_; 
v_fst_1627_ = lean_ctor_get(v_a_1623_, 0);
if (lean_obj_tag(v_fst_1627_) == 0)
{
lean_object* v_snd_1628_; lean_object* v___x_1629_; lean_object* v___x_1631_; 
v_snd_1628_ = lean_ctor_get(v_a_1623_, 1);
lean_inc(v_snd_1628_);
lean_dec(v_a_1623_);
v___x_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1629_, 0, v_snd_1628_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v___x_1629_);
v___x_1631_ = v___x_1625_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1629_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
else
{
lean_object* v_val_1633_; lean_object* v___x_1635_; 
lean_inc_ref(v_fst_1627_);
lean_dec(v_a_1623_);
v_val_1633_ = lean_ctor_get(v_fst_1627_, 0);
lean_inc(v_val_1633_);
lean_dec_ref_known(v_fst_1627_, 1);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v_val_1633_);
v___x_1635_ = v___x_1625_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_val_1633_);
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
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
v_a_1638_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1622_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1622_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
else
{
lean_object* v_vs_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; size_t v_sz_1649_; size_t v___x_1650_; lean_object* v___x_1651_; 
v_vs_1646_ = lean_ctor_get(v_n_1612_, 0);
v___x_1647_ = lean_box(0);
v___x_1648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
lean_ctor_set(v___x_1648_, 1, v_b_1613_);
v_sz_1649_ = lean_array_size(v_vs_1646_);
v___x_1650_ = ((size_t)0ULL);
v___x_1651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(v___x_1611_, v_vs_1646_, v_sz_1649_, v___x_1650_, v___x_1648_, v___y_1614_, v___y_1615_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1666_; 
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1654_ = v___x_1651_;
v_isShared_1655_ = v_isSharedCheck_1666_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1651_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1666_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v_fst_1656_; 
v_fst_1656_ = lean_ctor_get(v_a_1652_, 0);
if (lean_obj_tag(v_fst_1656_) == 0)
{
lean_object* v_snd_1657_; lean_object* v___x_1658_; lean_object* v___x_1660_; 
v_snd_1657_ = lean_ctor_get(v_a_1652_, 1);
lean_inc(v_snd_1657_);
lean_dec(v_a_1652_);
v___x_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1658_, 0, v_snd_1657_);
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 0, v___x_1658_);
v___x_1660_ = v___x_1654_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1658_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
else
{
lean_object* v_val_1662_; lean_object* v___x_1664_; 
lean_inc_ref(v_fst_1656_);
lean_dec(v_a_1652_);
v_val_1662_ = lean_ctor_get(v_fst_1656_, 0);
lean_inc(v_val_1662_);
lean_dec_ref_known(v_fst_1656_, 1);
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 0, v_val_1662_);
v___x_1664_ = v___x_1654_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_val_1662_);
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
else
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1674_; 
v_a_1667_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1669_ = v___x_1651_;
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1651_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1667_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(lean_object* v_init_1675_, uint8_t v___x_1676_, lean_object* v_as_1677_, size_t v_sz_1678_, size_t v_i_1679_, lean_object* v_b_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
uint8_t v___x_1684_; 
v___x_1684_ = lean_usize_dec_lt(v_i_1679_, v_sz_1678_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1685_; 
v___x_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1685_, 0, v_b_1680_);
return v___x_1685_;
}
else
{
lean_object* v_snd_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1720_; 
v_snd_1686_ = lean_ctor_get(v_b_1680_, 1);
v_isSharedCheck_1720_ = !lean_is_exclusive(v_b_1680_);
if (v_isSharedCheck_1720_ == 0)
{
lean_object* v_unused_1721_; 
v_unused_1721_ = lean_ctor_get(v_b_1680_, 0);
lean_dec(v_unused_1721_);
v___x_1688_ = v_b_1680_;
v_isShared_1689_ = v_isSharedCheck_1720_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_snd_1686_);
lean_dec(v_b_1680_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1720_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v_a_1690_; lean_object* v___x_1691_; 
v_a_1690_ = lean_array_uget_borrowed(v_as_1677_, v_i_1679_);
lean_inc(v_snd_1686_);
v___x_1691_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1675_, v___x_1676_, v_a_1690_, v_snd_1686_, v___y_1681_, v___y_1682_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1711_; 
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1694_ = v___x_1691_;
v_isShared_1695_ = v_isSharedCheck_1711_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1691_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1711_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
if (lean_obj_tag(v_a_1692_) == 0)
{
lean_object* v___x_1696_; lean_object* v___x_1698_; 
v___x_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1696_, 0, v_a_1692_);
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 0, v___x_1696_);
v___x_1698_ = v___x_1688_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1696_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v_snd_1686_);
v___x_1698_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
lean_object* v___x_1700_; 
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 0, v___x_1698_);
v___x_1700_ = v___x_1694_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1704_; lean_object* v___x_1706_; 
lean_del_object(v___x_1694_);
lean_dec(v_snd_1686_);
v_a_1703_ = lean_ctor_get(v_a_1692_, 0);
lean_inc(v_a_1703_);
lean_dec_ref_known(v_a_1692_, 1);
v___x_1704_ = lean_box(0);
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 1, v_a_1703_);
lean_ctor_set(v___x_1688_, 0, v___x_1704_);
v___x_1706_ = v___x_1688_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1704_);
lean_ctor_set(v_reuseFailAlloc_1710_, 1, v_a_1703_);
v___x_1706_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
size_t v___x_1707_; size_t v___x_1708_; 
v___x_1707_ = ((size_t)1ULL);
v___x_1708_ = lean_usize_add(v_i_1679_, v___x_1707_);
v_i_1679_ = v___x_1708_;
v_b_1680_ = v___x_1706_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
lean_del_object(v___x_1688_);
lean_dec(v_snd_1686_);
v_a_1712_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1691_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1691_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1712_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39___boxed(lean_object* v_init_1722_, lean_object* v___x_1723_, lean_object* v_as_1724_, lean_object* v_sz_1725_, lean_object* v_i_1726_, lean_object* v_b_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
uint8_t v___x_36830__boxed_1731_; size_t v_sz_boxed_1732_; size_t v_i_boxed_1733_; lean_object* v_res_1734_; 
v___x_36830__boxed_1731_ = lean_unbox(v___x_1723_);
v_sz_boxed_1732_ = lean_unbox_usize(v_sz_1725_);
lean_dec(v_sz_1725_);
v_i_boxed_1733_ = lean_unbox_usize(v_i_1726_);
lean_dec(v_i_1726_);
v_res_1734_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(v_init_1722_, v___x_36830__boxed_1731_, v_as_1724_, v_sz_boxed_1732_, v_i_boxed_1733_, v_b_1727_, v___y_1728_, v___y_1729_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec_ref(v_as_1724_);
lean_dec_ref(v_init_1722_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27___boxed(lean_object* v_init_1735_, lean_object* v___x_1736_, lean_object* v_n_1737_, lean_object* v_b_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
uint8_t v___x_36850__boxed_1742_; lean_object* v_res_1743_; 
v___x_36850__boxed_1742_ = lean_unbox(v___x_1736_);
v_res_1743_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1735_, v___x_36850__boxed_1742_, v_n_1737_, v_b_1738_, v___y_1739_, v___y_1740_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec_ref(v_n_1737_);
lean_dec_ref(v_init_1735_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(uint8_t v___x_1744_, lean_object* v_as_1745_, size_t v_sz_1746_, size_t v_i_1747_, lean_object* v_b_1748_, lean_object* v___y_1749_){
_start:
{
uint8_t v___x_1751_; 
v___x_1751_ = lean_usize_dec_lt(v_i_1747_, v_sz_1746_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1752_; 
v___x_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1752_, 0, v_b_1748_);
return v___x_1752_;
}
else
{
lean_object* v_snd_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1790_; 
v_snd_1753_ = lean_ctor_get(v_b_1748_, 1);
v_isSharedCheck_1790_ = !lean_is_exclusive(v_b_1748_);
if (v_isSharedCheck_1790_ == 0)
{
lean_object* v_unused_1791_; 
v_unused_1791_ = lean_ctor_get(v_b_1748_, 0);
lean_dec(v_unused_1791_);
v___x_1755_ = v_b_1748_;
v_isShared_1756_ = v_isSharedCheck_1790_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_snd_1753_);
lean_dec(v_b_1748_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1790_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v_ref_1757_; lean_object* v_a_1758_; lean_object* v_ref_1759_; lean_object* v_msg_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1789_; 
v_ref_1757_ = lean_ctor_get(v___y_1749_, 4);
v_a_1758_ = lean_array_uget(v_as_1745_, v_i_1747_);
v_ref_1759_ = lean_ctor_get(v_a_1758_, 0);
v_msg_1760_ = lean_ctor_get(v_a_1758_, 1);
v_isSharedCheck_1789_ = !lean_is_exclusive(v_a_1758_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1762_ = v_a_1758_;
v_isShared_1763_ = v_isSharedCheck_1789_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_msg_1760_);
lean_inc(v_ref_1759_);
lean_dec(v_a_1758_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1789_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1764_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v_ref_1781_; lean_object* v___y_1783_; lean_object* v___x_1786_; 
v___x_1764_ = lean_box(0);
v_ref_1781_ = l_Lean_replaceRef(v_ref_1759_, v_ref_1757_);
lean_dec(v_ref_1759_);
v___x_1786_ = l_Lean_Syntax_getPos_x3f(v_ref_1781_, v___x_1744_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v___x_1787_; 
v___x_1787_ = lean_unsigned_to_nat(0u);
v___y_1783_ = v___x_1787_;
goto v___jp_1782_;
}
else
{
lean_object* v_val_1788_; 
v_val_1788_ = lean_ctor_get(v___x_1786_, 0);
lean_inc(v_val_1788_);
lean_dec_ref_known(v___x_1786_, 1);
v___y_1783_ = v_val_1788_;
goto v___jp_1782_;
}
v___jp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 1, v___y_1767_);
lean_ctor_set(v___x_1755_, 0, v___y_1766_);
v___x_1769_ = v___x_1755_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___y_1766_);
lean_ctor_set(v_reuseFailAlloc_1780_, 1, v___y_1767_);
v___x_1769_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v_pos2traces_1773_; lean_object* v___x_1775_; 
v___x_1770_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1771_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1753_, v___x_1769_, v___x_1770_);
v___x_1772_ = lean_array_push(v___x_1771_, v_msg_1760_);
v_pos2traces_1773_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1753_, v___x_1769_, v___x_1772_);
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 1, v_pos2traces_1773_);
lean_ctor_set(v___x_1762_, 0, v___x_1764_);
v___x_1775_ = v___x_1762_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1764_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v_pos2traces_1773_);
v___x_1775_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
size_t v___x_1776_; size_t v___x_1777_; 
v___x_1776_ = ((size_t)1ULL);
v___x_1777_ = lean_usize_add(v_i_1747_, v___x_1776_);
v_i_1747_ = v___x_1777_;
v_b_1748_ = v___x_1775_;
goto _start;
}
}
}
v___jp_1782_:
{
lean_object* v___x_1784_; 
v___x_1784_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1781_, v___x_1744_);
lean_dec(v_ref_1781_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_inc(v___y_1783_);
v___y_1766_ = v___y_1783_;
v___y_1767_ = v___y_1783_;
goto v___jp_1765_;
}
else
{
lean_object* v_val_1785_; 
v_val_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_val_1785_);
lean_dec_ref_known(v___x_1784_, 1);
v___y_1766_ = v___y_1783_;
v___y_1767_ = v_val_1785_;
goto v___jp_1765_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg___boxed(lean_object* v___x_1792_, lean_object* v_as_1793_, lean_object* v_sz_1794_, lean_object* v_i_1795_, lean_object* v_b_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
uint8_t v___x_37033__boxed_1799_; size_t v_sz_boxed_1800_; size_t v_i_boxed_1801_; lean_object* v_res_1802_; 
v___x_37033__boxed_1799_ = lean_unbox(v___x_1792_);
v_sz_boxed_1800_ = lean_unbox_usize(v_sz_1794_);
lean_dec(v_sz_1794_);
v_i_boxed_1801_ = lean_unbox_usize(v_i_1795_);
lean_dec(v_i_1795_);
v_res_1802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_37033__boxed_1799_, v_as_1793_, v_sz_boxed_1800_, v_i_boxed_1801_, v_b_1796_, v___y_1797_);
lean_dec_ref(v___y_1797_);
lean_dec_ref(v_as_1793_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(uint8_t v___x_1803_, lean_object* v_as_1804_, size_t v_sz_1805_, size_t v_i_1806_, lean_object* v_b_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
uint8_t v___x_1811_; 
v___x_1811_ = lean_usize_dec_lt(v_i_1806_, v_sz_1805_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; 
v___x_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1812_, 0, v_b_1807_);
return v___x_1812_;
}
else
{
lean_object* v_snd_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1850_; 
v_snd_1813_ = lean_ctor_get(v_b_1807_, 1);
v_isSharedCheck_1850_ = !lean_is_exclusive(v_b_1807_);
if (v_isSharedCheck_1850_ == 0)
{
lean_object* v_unused_1851_; 
v_unused_1851_ = lean_ctor_get(v_b_1807_, 0);
lean_dec(v_unused_1851_);
v___x_1815_ = v_b_1807_;
v_isShared_1816_ = v_isSharedCheck_1850_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_snd_1813_);
lean_dec(v_b_1807_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1850_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v_ref_1817_; lean_object* v_a_1818_; lean_object* v_ref_1819_; lean_object* v_msg_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1849_; 
v_ref_1817_ = lean_ctor_get(v___y_1808_, 4);
v_a_1818_ = lean_array_uget(v_as_1804_, v_i_1806_);
v_ref_1819_ = lean_ctor_get(v_a_1818_, 0);
v_msg_1820_ = lean_ctor_get(v_a_1818_, 1);
v_isSharedCheck_1849_ = !lean_is_exclusive(v_a_1818_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1822_ = v_a_1818_;
v_isShared_1823_ = v_isSharedCheck_1849_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_msg_1820_);
lean_inc(v_ref_1819_);
lean_dec(v_a_1818_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1849_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1824_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v_ref_1841_; lean_object* v___y_1843_; lean_object* v___x_1846_; 
v___x_1824_ = lean_box(0);
v_ref_1841_ = l_Lean_replaceRef(v_ref_1819_, v_ref_1817_);
lean_dec(v_ref_1819_);
v___x_1846_ = l_Lean_Syntax_getPos_x3f(v_ref_1841_, v___x_1803_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v___x_1847_; 
v___x_1847_ = lean_unsigned_to_nat(0u);
v___y_1843_ = v___x_1847_;
goto v___jp_1842_;
}
else
{
lean_object* v_val_1848_; 
v_val_1848_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_val_1848_);
lean_dec_ref_known(v___x_1846_, 1);
v___y_1843_ = v_val_1848_;
goto v___jp_1842_;
}
v___jp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 1, v___y_1827_);
lean_ctor_set(v___x_1815_, 0, v___y_1826_);
v___x_1829_ = v___x_1815_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___y_1826_);
lean_ctor_set(v_reuseFailAlloc_1840_, 1, v___y_1827_);
v___x_1829_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v_pos2traces_1833_; lean_object* v___x_1835_; 
v___x_1830_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1831_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1813_, v___x_1829_, v___x_1830_);
v___x_1832_ = lean_array_push(v___x_1831_, v_msg_1820_);
v_pos2traces_1833_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1813_, v___x_1829_, v___x_1832_);
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 1, v_pos2traces_1833_);
lean_ctor_set(v___x_1822_, 0, v___x_1824_);
v___x_1835_ = v___x_1822_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1824_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v_pos2traces_1833_);
v___x_1835_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
size_t v___x_1836_; size_t v___x_1837_; lean_object* v___x_1838_; 
v___x_1836_ = ((size_t)1ULL);
v___x_1837_ = lean_usize_add(v_i_1806_, v___x_1836_);
v___x_1838_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_1803_, v_as_1804_, v_sz_1805_, v___x_1837_, v___x_1835_, v___y_1808_);
return v___x_1838_;
}
}
}
v___jp_1842_:
{
lean_object* v___x_1844_; 
v___x_1844_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1841_, v___x_1803_);
lean_dec(v_ref_1841_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_inc(v___y_1843_);
v___y_1826_ = v___y_1843_;
v___y_1827_ = v___y_1843_;
goto v___jp_1825_;
}
else
{
lean_object* v_val_1845_; 
v_val_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_val_1845_);
lean_dec_ref_known(v___x_1844_, 1);
v___y_1826_ = v___y_1843_;
v___y_1827_ = v_val_1845_;
goto v___jp_1825_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28___boxed(lean_object* v___x_1852_, lean_object* v_as_1853_, lean_object* v_sz_1854_, lean_object* v_i_1855_, lean_object* v_b_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
uint8_t v___x_37113__boxed_1860_; size_t v_sz_boxed_1861_; size_t v_i_boxed_1862_; lean_object* v_res_1863_; 
v___x_37113__boxed_1860_ = lean_unbox(v___x_1852_);
v_sz_boxed_1861_ = lean_unbox_usize(v_sz_1854_);
lean_dec(v_sz_1854_);
v_i_boxed_1862_ = lean_unbox_usize(v_i_1855_);
lean_dec(v_i_1855_);
v_res_1863_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(v___x_37113__boxed_1860_, v_as_1853_, v_sz_boxed_1861_, v_i_boxed_1862_, v_b_1856_, v___y_1857_, v___y_1858_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec_ref(v_as_1853_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(uint8_t v___x_1864_, lean_object* v_t_1865_, lean_object* v_init_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v_root_1870_; lean_object* v_tail_1871_; lean_object* v___x_1872_; 
v_root_1870_ = lean_ctor_get(v_t_1865_, 0);
v_tail_1871_ = lean_ctor_get(v_t_1865_, 1);
lean_inc_ref(v_init_1866_);
v___x_1872_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1866_, v___x_1864_, v_root_1870_, v_init_1866_, v___y_1867_, v___y_1868_);
lean_dec_ref(v_init_1866_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1909_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1875_ = v___x_1872_;
v_isShared_1876_ = v_isSharedCheck_1909_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1872_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1909_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
if (lean_obj_tag(v_a_1873_) == 0)
{
lean_object* v_a_1877_; lean_object* v___x_1879_; 
v_a_1877_ = lean_ctor_get(v_a_1873_, 0);
lean_inc(v_a_1877_);
lean_dec_ref_known(v_a_1873_, 1);
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v_a_1877_);
v___x_1879_ = v___x_1875_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1877_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
else
{
lean_object* v_a_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; size_t v_sz_1884_; size_t v___x_1885_; lean_object* v___x_1886_; 
lean_del_object(v___x_1875_);
v_a_1881_ = lean_ctor_get(v_a_1873_, 0);
lean_inc(v_a_1881_);
lean_dec_ref_known(v_a_1873_, 1);
v___x_1882_ = lean_box(0);
v___x_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
lean_ctor_set(v___x_1883_, 1, v_a_1881_);
v_sz_1884_ = lean_array_size(v_tail_1871_);
v___x_1885_ = ((size_t)0ULL);
v___x_1886_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(v___x_1864_, v_tail_1871_, v_sz_1884_, v___x_1885_, v___x_1883_, v___y_1867_, v___y_1868_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1900_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1889_ = v___x_1886_;
v_isShared_1890_ = v_isSharedCheck_1900_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1886_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1900_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v_fst_1891_; 
v_fst_1891_ = lean_ctor_get(v_a_1887_, 0);
if (lean_obj_tag(v_fst_1891_) == 0)
{
lean_object* v_snd_1892_; lean_object* v___x_1894_; 
v_snd_1892_ = lean_ctor_get(v_a_1887_, 1);
lean_inc(v_snd_1892_);
lean_dec(v_a_1887_);
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 0, v_snd_1892_);
v___x_1894_ = v___x_1889_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_snd_1892_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
else
{
lean_object* v_val_1896_; lean_object* v___x_1898_; 
lean_inc_ref(v_fst_1891_);
lean_dec(v_a_1887_);
v_val_1896_ = lean_ctor_get(v_fst_1891_, 0);
lean_inc(v_val_1896_);
lean_dec_ref_known(v_fst_1891_, 1);
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 0, v_val_1896_);
v___x_1898_ = v___x_1889_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_val_1896_);
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
else
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
v_a_1901_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1886_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1886_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
}
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
v_a_1910_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1912_ = v___x_1872_;
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1872_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1910_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19___boxed(lean_object* v___x_1918_, lean_object* v_t_1919_, lean_object* v_init_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
uint8_t v___x_37194__boxed_1924_; lean_object* v_res_1925_; 
v___x_37194__boxed_1924_ = lean_unbox(v___x_1918_);
v_res_1925_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(v___x_37194__boxed_1924_, v_t_1919_, v_init_1920_, v___y_1921_, v___y_1922_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
lean_dec_ref(v_t_1919_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(lean_object* v_x_1926_, lean_object* v_x_1927_){
_start:
{
if (lean_obj_tag(v_x_1927_) == 0)
{
return v_x_1926_;
}
else
{
lean_object* v_key_1928_; lean_object* v_value_1929_; lean_object* v_tail_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v_key_1928_ = lean_ctor_get(v_x_1927_, 0);
v_value_1929_ = lean_ctor_get(v_x_1927_, 1);
v_tail_1930_ = lean_ctor_get(v_x_1927_, 2);
lean_inc(v_value_1929_);
lean_inc(v_key_1928_);
v___x_1931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1931_, 0, v_key_1928_);
lean_ctor_set(v___x_1931_, 1, v_value_1929_);
v___x_1932_ = lean_array_push(v_x_1926_, v___x_1931_);
v_x_1926_ = v___x_1932_;
v_x_1927_ = v_tail_1930_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22___boxed(lean_object* v_x_1934_, lean_object* v_x_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(v_x_1934_, v_x_1935_);
lean_dec(v_x_1935_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(lean_object* v_as_1937_, size_t v_i_1938_, size_t v_stop_1939_, lean_object* v_b_1940_){
_start:
{
uint8_t v___x_1941_; 
v___x_1941_ = lean_usize_dec_eq(v_i_1938_, v_stop_1939_);
if (v___x_1941_ == 0)
{
lean_object* v___x_1942_; lean_object* v___x_1943_; size_t v___x_1944_; size_t v___x_1945_; 
v___x_1942_ = lean_array_uget_borrowed(v_as_1937_, v_i_1938_);
v___x_1943_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(v_b_1940_, v___x_1942_);
v___x_1944_ = ((size_t)1ULL);
v___x_1945_ = lean_usize_add(v_i_1938_, v___x_1944_);
v_i_1938_ = v___x_1945_;
v_b_1940_ = v___x_1943_;
goto _start;
}
else
{
return v_b_1940_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23___boxed(lean_object* v_as_1947_, lean_object* v_i_1948_, lean_object* v_stop_1949_, lean_object* v_b_1950_){
_start:
{
size_t v_i_boxed_1951_; size_t v_stop_boxed_1952_; lean_object* v_res_1953_; 
v_i_boxed_1951_ = lean_unbox_usize(v_i_1948_);
lean_dec(v_i_1948_);
v_stop_boxed_1952_ = lean_unbox_usize(v_stop_1949_);
lean_dec(v_stop_1949_);
v_res_1953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_as_1947_, v_i_boxed_1951_, v_stop_boxed_1952_, v_b_1950_);
lean_dec_ref(v_as_1947_);
return v_res_1953_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0(void){
_start:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1954_ = lean_unsigned_to_nat(32u);
v___x_1955_ = lean_mk_empty_array_with_capacity(v___x_1954_);
v___x_1956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1955_);
return v___x_1956_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1(void){
_start:
{
size_t v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1957_ = ((size_t)5ULL);
v___x_1958_ = lean_unsigned_to_nat(0u);
v___x_1959_ = lean_unsigned_to_nat(32u);
v___x_1960_ = lean_mk_empty_array_with_capacity(v___x_1959_);
v___x_1961_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0);
v___x_1962_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1962_, 0, v___x_1961_);
lean_ctor_set(v___x_1962_, 1, v___x_1960_);
lean_ctor_set(v___x_1962_, 2, v___x_1958_);
lean_ctor_set(v___x_1962_, 3, v___x_1958_);
lean_ctor_set_usize(v___x_1962_, 4, v___x_1957_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(lean_object* v___y_1963_){
_start:
{
lean_object* v___x_1965_; lean_object* v_traceState_1966_; lean_object* v_traces_1967_; lean_object* v___x_1968_; lean_object* v_traceState_1969_; lean_object* v_env_1970_; lean_object* v_nextMacroScope_1971_; lean_object* v_ngen_1972_; lean_object* v_auxDeclNGen_1973_; lean_object* v_cache_1974_; lean_object* v_messages_1975_; lean_object* v_infoState_1976_; lean_object* v_snapshotTasks_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1996_; 
v___x_1965_ = lean_st_ref_get(v___y_1963_);
v_traceState_1966_ = lean_ctor_get(v___x_1965_, 4);
lean_inc_ref(v_traceState_1966_);
lean_dec(v___x_1965_);
v_traces_1967_ = lean_ctor_get(v_traceState_1966_, 0);
lean_inc_ref(v_traces_1967_);
lean_dec_ref(v_traceState_1966_);
v___x_1968_ = lean_st_ref_take(v___y_1963_);
v_traceState_1969_ = lean_ctor_get(v___x_1968_, 4);
v_env_1970_ = lean_ctor_get(v___x_1968_, 0);
v_nextMacroScope_1971_ = lean_ctor_get(v___x_1968_, 1);
v_ngen_1972_ = lean_ctor_get(v___x_1968_, 2);
v_auxDeclNGen_1973_ = lean_ctor_get(v___x_1968_, 3);
v_cache_1974_ = lean_ctor_get(v___x_1968_, 5);
v_messages_1975_ = lean_ctor_get(v___x_1968_, 6);
v_infoState_1976_ = lean_ctor_get(v___x_1968_, 7);
v_snapshotTasks_1977_ = lean_ctor_get(v___x_1968_, 8);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1979_ = v___x_1968_;
v_isShared_1980_ = v_isSharedCheck_1996_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_snapshotTasks_1977_);
lean_inc(v_infoState_1976_);
lean_inc(v_messages_1975_);
lean_inc(v_cache_1974_);
lean_inc(v_traceState_1969_);
lean_inc(v_auxDeclNGen_1973_);
lean_inc(v_ngen_1972_);
lean_inc(v_nextMacroScope_1971_);
lean_inc(v_env_1970_);
lean_dec(v___x_1968_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1996_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
uint64_t v_tid_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1994_; 
v_tid_1981_ = lean_ctor_get_uint64(v_traceState_1969_, sizeof(void*)*1);
v_isSharedCheck_1994_ = !lean_is_exclusive(v_traceState_1969_);
if (v_isSharedCheck_1994_ == 0)
{
lean_object* v_unused_1995_; 
v_unused_1995_ = lean_ctor_get(v_traceState_1969_, 0);
lean_dec(v_unused_1995_);
v___x_1983_ = v_traceState_1969_;
v_isShared_1984_ = v_isSharedCheck_1994_;
goto v_resetjp_1982_;
}
else
{
lean_dec(v_traceState_1969_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1994_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1985_; lean_object* v___x_1987_; 
v___x_1985_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 0, v___x_1985_);
v___x_1987_ = v___x_1983_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1985_);
lean_ctor_set_uint64(v_reuseFailAlloc_1993_, sizeof(void*)*1, v_tid_1981_);
v___x_1987_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
lean_object* v___x_1989_; 
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 4, v___x_1987_);
v___x_1989_ = v___x_1979_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_env_1970_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v_nextMacroScope_1971_);
lean_ctor_set(v_reuseFailAlloc_1992_, 2, v_ngen_1972_);
lean_ctor_set(v_reuseFailAlloc_1992_, 3, v_auxDeclNGen_1973_);
lean_ctor_set(v_reuseFailAlloc_1992_, 4, v___x_1987_);
lean_ctor_set(v_reuseFailAlloc_1992_, 5, v_cache_1974_);
lean_ctor_set(v_reuseFailAlloc_1992_, 6, v_messages_1975_);
lean_ctor_set(v_reuseFailAlloc_1992_, 7, v_infoState_1976_);
lean_ctor_set(v_reuseFailAlloc_1992_, 8, v_snapshotTasks_1977_);
v___x_1989_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1990_ = lean_st_ref_put(v___y_1963_, v___x_1989_);
v___x_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1991_, 0, v_traces_1967_);
return v___x_1991_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___boxed(lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v_res_1999_; 
v_res_1999_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_1997_);
lean_dec(v___y_1997_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(lean_object* v_hi_2000_, lean_object* v_pivot_2001_, lean_object* v_as_2002_, lean_object* v_i_2003_, lean_object* v_k_2004_){
_start:
{
uint8_t v___x_2005_; 
v___x_2005_ = lean_nat_dec_lt(v_k_2004_, v_hi_2000_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
lean_dec(v_k_2004_);
v___x_2006_ = lean_array_fswap(v_as_2002_, v_i_2003_, v_hi_2000_);
v___x_2007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2007_, 0, v_i_2003_);
lean_ctor_set(v___x_2007_, 1, v___x_2006_);
return v___x_2007_;
}
else
{
lean_object* v___x_2008_; lean_object* v_fst_2009_; lean_object* v_fst_2010_; lean_object* v_fst_2011_; lean_object* v_fst_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; uint8_t v___x_2015_; 
v___x_2008_ = lean_array_fget_borrowed(v_as_2002_, v_k_2004_);
v_fst_2009_ = lean_ctor_get(v___x_2008_, 0);
v_fst_2010_ = lean_ctor_get(v_pivot_2001_, 0);
v_fst_2011_ = lean_ctor_get(v_fst_2009_, 0);
v_fst_2012_ = lean_ctor_get(v_fst_2010_, 0);
v___x_2013_ = lean_unsigned_to_nat(1u);
v___x_2014_ = lean_nat_add(v_fst_2011_, v___x_2013_);
v___x_2015_ = lean_nat_dec_le(v___x_2014_, v_fst_2012_);
lean_dec(v___x_2014_);
if (v___x_2015_ == 0)
{
lean_object* v___x_2016_; 
v___x_2016_ = lean_nat_add(v_k_2004_, v___x_2013_);
lean_dec(v_k_2004_);
v_k_2004_ = v___x_2016_;
goto _start;
}
else
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2018_ = lean_array_fswap(v_as_2002_, v_i_2003_, v_k_2004_);
v___x_2019_ = lean_nat_add(v_i_2003_, v___x_2013_);
lean_dec(v_i_2003_);
v___x_2020_ = lean_nat_add(v_k_2004_, v___x_2013_);
lean_dec(v_k_2004_);
v_as_2002_ = v___x_2018_;
v_i_2003_ = v___x_2019_;
v_k_2004_ = v___x_2020_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg___boxed(lean_object* v_hi_2022_, lean_object* v_pivot_2023_, lean_object* v_as_2024_, lean_object* v_i_2025_, lean_object* v_k_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_2022_, v_pivot_2023_, v_as_2024_, v_i_2025_, v_k_2026_);
lean_dec_ref(v_pivot_2023_);
lean_dec(v_hi_2022_);
return v_res_2027_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(lean_object* v_x_2028_, lean_object* v_x_2029_){
_start:
{
lean_object* v_fst_2030_; lean_object* v_fst_2031_; lean_object* v_fst_2032_; lean_object* v_fst_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; uint8_t v___x_2036_; 
v_fst_2030_ = lean_ctor_get(v_x_2028_, 0);
v_fst_2031_ = lean_ctor_get(v_x_2029_, 0);
v_fst_2032_ = lean_ctor_get(v_fst_2030_, 0);
v_fst_2033_ = lean_ctor_get(v_fst_2031_, 0);
v___x_2034_ = lean_unsigned_to_nat(1u);
v___x_2035_ = lean_nat_add(v_fst_2032_, v___x_2034_);
v___x_2036_ = lean_nat_dec_le(v___x_2035_, v_fst_2033_);
lean_dec(v___x_2035_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0___boxed(lean_object* v_x_2037_, lean_object* v_x_2038_){
_start:
{
uint8_t v_res_2039_; lean_object* v_r_2040_; 
v_res_2039_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v_x_2037_, v_x_2038_);
lean_dec_ref(v_x_2038_);
lean_dec_ref(v_x_2037_);
v_r_2040_ = lean_box(v_res_2039_);
return v_r_2040_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(lean_object* v_n_2041_, lean_object* v_as_2042_, lean_object* v_lo_2043_, lean_object* v_hi_2044_){
_start:
{
lean_object* v___y_2046_; uint8_t v___x_2056_; 
v___x_2056_ = lean_nat_dec_lt(v_lo_2043_, v_hi_2044_);
if (v___x_2056_ == 0)
{
lean_dec(v_lo_2043_);
return v_as_2042_;
}
else
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v_mid_2059_; lean_object* v___y_2061_; lean_object* v___y_2067_; lean_object* v___x_2072_; lean_object* v___x_2073_; uint8_t v___x_2074_; 
v___x_2057_ = lean_nat_add(v_lo_2043_, v_hi_2044_);
v___x_2058_ = lean_unsigned_to_nat(1u);
v_mid_2059_ = lean_nat_shiftr(v___x_2057_, v___x_2058_);
lean_dec(v___x_2057_);
v___x_2072_ = lean_array_fget_borrowed(v_as_2042_, v_mid_2059_);
v___x_2073_ = lean_array_fget_borrowed(v_as_2042_, v_lo_2043_);
v___x_2074_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2072_, v___x_2073_);
if (v___x_2074_ == 0)
{
v___y_2067_ = v_as_2042_;
goto v___jp_2066_;
}
else
{
lean_object* v___x_2075_; 
v___x_2075_ = lean_array_fswap(v_as_2042_, v_lo_2043_, v_mid_2059_);
v___y_2067_ = v___x_2075_;
goto v___jp_2066_;
}
v___jp_2060_:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; 
v___x_2062_ = lean_array_fget_borrowed(v___y_2061_, v_mid_2059_);
v___x_2063_ = lean_array_fget_borrowed(v___y_2061_, v_hi_2044_);
v___x_2064_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2062_, v___x_2063_);
if (v___x_2064_ == 0)
{
lean_dec(v_mid_2059_);
v___y_2046_ = v___y_2061_;
goto v___jp_2045_;
}
else
{
lean_object* v___x_2065_; 
v___x_2065_ = lean_array_fswap(v___y_2061_, v_mid_2059_, v_hi_2044_);
lean_dec(v_mid_2059_);
v___y_2046_ = v___x_2065_;
goto v___jp_2045_;
}
}
v___jp_2066_:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; uint8_t v___x_2070_; 
v___x_2068_ = lean_array_fget_borrowed(v___y_2067_, v_hi_2044_);
v___x_2069_ = lean_array_fget_borrowed(v___y_2067_, v_lo_2043_);
v___x_2070_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2068_, v___x_2069_);
if (v___x_2070_ == 0)
{
v___y_2061_ = v___y_2067_;
goto v___jp_2060_;
}
else
{
lean_object* v___x_2071_; 
v___x_2071_ = lean_array_fswap(v___y_2067_, v_lo_2043_, v_hi_2044_);
v___y_2061_ = v___x_2071_;
goto v___jp_2060_;
}
}
}
v___jp_2045_:
{
lean_object* v_pivot_2047_; lean_object* v___x_2048_; lean_object* v_fst_2049_; lean_object* v_snd_2050_; uint8_t v___x_2051_; 
v_pivot_2047_ = lean_array_fget(v___y_2046_, v_hi_2044_);
lean_inc_n(v_lo_2043_, 2);
v___x_2048_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_2044_, v_pivot_2047_, v___y_2046_, v_lo_2043_, v_lo_2043_);
lean_dec(v_pivot_2047_);
v_fst_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_fst_2049_);
v_snd_2050_ = lean_ctor_get(v___x_2048_, 1);
lean_inc(v_snd_2050_);
lean_dec_ref(v___x_2048_);
v___x_2051_ = lean_nat_dec_le(v_hi_2044_, v_fst_2049_);
if (v___x_2051_ == 0)
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2052_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_2041_, v_snd_2050_, v_lo_2043_, v_fst_2049_);
v___x_2053_ = lean_unsigned_to_nat(1u);
v___x_2054_ = lean_nat_add(v_fst_2049_, v___x_2053_);
lean_dec(v_fst_2049_);
v_as_2042_ = v___x_2052_;
v_lo_2043_ = v___x_2054_;
goto _start;
}
else
{
lean_dec(v_fst_2049_);
lean_dec(v_lo_2043_);
return v_snd_2050_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___boxed(lean_object* v_n_2076_, lean_object* v_as_2077_, lean_object* v_lo_2078_, lean_object* v_hi_2079_){
_start:
{
lean_object* v_res_2080_; 
v_res_2080_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_2076_, v_as_2077_, v_lo_2078_, v_hi_2079_);
lean_dec(v_hi_2079_);
lean_dec(v_n_2076_);
return v_res_2080_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0(void){
_start:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2081_ = lean_box(0);
v___x_2082_ = lean_unsigned_to_nat(16u);
v___x_2083_ = lean_mk_array(v___x_2082_, v___x_2081_);
return v___x_2083_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1(void){
_start:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v_pos2traces_2086_; 
v___x_2084_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0, &l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0);
v___x_2085_ = lean_unsigned_to_nat(0u);
v_pos2traces_2086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos2traces_2086_, 0, v___x_2085_);
lean_ctor_set(v_pos2traces_2086_, 1, v___x_2084_);
return v_pos2traces_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10(lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
lean_object* v_options_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
v_options_2093_ = lean_ctor_get(v___y_2087_, 1);
v___x_2094_ = l_Lean_trace_profiler_output;
v___x_2095_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(v_options_2093_, v___x_2094_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v___x_2096_; uint8_t v___x_2097_; 
v___x_2096_ = l_Lean_trace_profiler_serve;
v___x_2097_ = l_Lean_Option_get___at___00main_spec__8(v_options_2093_, v___x_2096_);
if (v___x_2097_ == 0)
{
lean_object* v___x_2098_; lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2161_; 
v___x_2098_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_2088_);
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2101_ = v___x_2098_;
v_isShared_2102_ = v_isSharedCheck_2161_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2098_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2161_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
uint8_t v___x_2103_; 
v___x_2103_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_2099_);
if (v___x_2103_ == 0)
{
lean_object* v___x_2104_; lean_object* v_pos2traces_2105_; lean_object* v___x_2106_; 
lean_del_object(v___x_2101_);
v___x_2104_ = lean_unsigned_to_nat(0u);
v_pos2traces_2105_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1, &l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1);
v___x_2106_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(v___x_2103_, v_a_2099_, v_pos2traces_2105_, v___y_2087_, v___y_2088_);
lean_dec(v_a_2099_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; lean_object* v___y_2109_; lean_object* v___y_2123_; lean_object* v___y_2124_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v___y_2129_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2135_; lean_object* v_size_2141_; lean_object* v_buckets_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; uint8_t v___x_2145_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_a_2107_);
lean_dec_ref_known(v___x_2106_, 1);
v_size_2141_ = lean_ctor_get(v_a_2107_, 0);
lean_inc(v_size_2141_);
v_buckets_2142_ = lean_ctor_get(v_a_2107_, 1);
lean_inc_ref(v_buckets_2142_);
lean_dec(v_a_2107_);
v___x_2143_ = lean_mk_empty_array_with_capacity(v_size_2141_);
lean_dec(v_size_2141_);
v___x_2144_ = lean_array_get_size(v_buckets_2142_);
v___x_2145_ = lean_nat_dec_lt(v___x_2104_, v___x_2144_);
if (v___x_2145_ == 0)
{
lean_dec_ref(v_buckets_2142_);
v___y_2135_ = v___x_2143_;
goto v___jp_2134_;
}
else
{
size_t v___x_2146_; size_t v___x_2147_; lean_object* v___x_2148_; 
v___x_2146_ = ((size_t)0ULL);
v___x_2147_ = lean_usize_of_nat(v___x_2144_);
v___x_2148_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_buckets_2142_, v___x_2146_, v___x_2147_, v___x_2143_);
lean_dec_ref(v_buckets_2142_);
v___y_2135_ = v___x_2148_;
goto v___jp_2134_;
}
v___jp_2108_:
{
lean_object* v___x_2110_; size_t v_sz_2111_; size_t v___x_2112_; lean_object* v___x_2113_; 
v___x_2110_ = lean_box(0);
v_sz_2111_ = lean_array_size(v___y_2109_);
v___x_2112_ = ((size_t)0ULL);
v___x_2113_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(v___x_2097_, v___y_2109_, v_sz_2111_, v___x_2112_, v___x_2110_, v___y_2087_, v___y_2088_);
lean_dec_ref(v___y_2109_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2120_; 
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2120_ == 0)
{
lean_object* v_unused_2121_; 
v_unused_2121_ = lean_ctor_get(v___x_2113_, 0);
lean_dec(v_unused_2121_);
v___x_2115_ = v___x_2113_;
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
else
{
lean_dec(v___x_2113_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 0, v___x_2110_);
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2110_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
else
{
return v___x_2113_;
}
}
v___jp_2122_:
{
lean_object* v___x_2127_; 
v___x_2127_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v___y_2123_, v___y_2125_, v___y_2124_, v___y_2126_);
lean_dec(v___y_2126_);
lean_dec(v___y_2123_);
v___y_2109_ = v___x_2127_;
goto v___jp_2108_;
}
v___jp_2128_:
{
uint8_t v___x_2133_; 
v___x_2133_ = lean_nat_dec_le(v___y_2132_, v___y_2130_);
if (v___x_2133_ == 0)
{
lean_dec(v___y_2130_);
lean_inc(v___y_2132_);
v___y_2123_ = v___y_2129_;
v___y_2124_ = v___y_2132_;
v___y_2125_ = v___y_2131_;
v___y_2126_ = v___y_2132_;
goto v___jp_2122_;
}
else
{
v___y_2123_ = v___y_2129_;
v___y_2124_ = v___y_2132_;
v___y_2125_ = v___y_2131_;
v___y_2126_ = v___y_2130_;
goto v___jp_2122_;
}
}
v___jp_2134_:
{
lean_object* v___x_2136_; uint8_t v___x_2137_; 
v___x_2136_ = lean_array_get_size(v___y_2135_);
v___x_2137_ = lean_nat_dec_eq(v___x_2136_, v___x_2104_);
if (v___x_2137_ == 0)
{
lean_object* v___x_2138_; lean_object* v___x_2139_; uint8_t v___x_2140_; 
v___x_2138_ = lean_unsigned_to_nat(1u);
v___x_2139_ = lean_nat_sub(v___x_2136_, v___x_2138_);
v___x_2140_ = lean_nat_dec_le(v___x_2104_, v___x_2139_);
if (v___x_2140_ == 0)
{
lean_inc(v___x_2139_);
v___y_2129_ = v___x_2136_;
v___y_2130_ = v___x_2139_;
v___y_2131_ = v___y_2135_;
v___y_2132_ = v___x_2139_;
goto v___jp_2128_;
}
else
{
v___y_2129_ = v___x_2136_;
v___y_2130_ = v___x_2139_;
v___y_2131_ = v___y_2135_;
v___y_2132_ = v___x_2104_;
goto v___jp_2128_;
}
}
else
{
v___y_2109_ = v___y_2135_;
goto v___jp_2108_;
}
}
}
else
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2156_; 
v_a_2149_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2151_ = v___x_2106_;
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2106_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_a_2149_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
else
{
lean_object* v___x_2157_; lean_object* v___x_2159_; 
lean_dec(v_a_2099_);
v___x_2157_ = lean_box(0);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 0, v___x_2157_);
v___x_2159_ = v___x_2101_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2157_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
else
{
goto v___jp_2090_;
}
}
else
{
lean_dec_ref_known(v___x_2095_, 1);
goto v___jp_2090_;
}
v___jp_2090_:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = lean_box(0);
v___x_2092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
return v___x_2092_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10___boxed(lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v_res_2165_; 
v_res_2165_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2162_, v___y_2163_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(lean_object* v_as_2166_, size_t v_sz_2167_, size_t v_i_2168_, lean_object* v_b_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
uint8_t v___x_2173_; 
v___x_2173_ = lean_usize_dec_lt(v_i_2168_, v_sz_2167_);
if (v___x_2173_ == 0)
{
lean_object* v___x_2174_; 
v___x_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2174_, 0, v_b_2169_);
return v___x_2174_;
}
else
{
lean_object* v_options_2175_; lean_object* v_a_2176_; lean_object* v___x_2177_; 
v_options_2175_ = lean_ctor_get(v___y_2170_, 1);
v_a_2176_ = lean_array_uget_borrowed(v_as_2166_, v_i_2168_);
lean_inc_ref(v_options_2175_);
lean_inc(v_a_2176_);
v___x_2177_ = l_Lean_Compiler_LCNF_resumeCompilation(v_a_2176_, v_options_2175_, v___y_2170_, v___y_2171_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v___x_2178_; 
lean_dec_ref_known(v___x_2177_, 1);
v___x_2178_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2170_, v___y_2171_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v___x_2179_; size_t v___x_2180_; size_t v___x_2181_; 
lean_dec_ref_known(v___x_2178_, 1);
v___x_2179_ = lean_box(0);
v___x_2180_ = ((size_t)1ULL);
v___x_2181_ = lean_usize_add(v_i_2168_, v___x_2180_);
v_i_2168_ = v___x_2181_;
v_b_2169_ = v___x_2179_;
goto _start;
}
else
{
return v___x_2178_;
}
}
else
{
lean_object* v_a_2183_; lean_object* v___x_2184_; 
v_a_2183_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_a_2183_);
lean_dec_ref_known(v___x_2177_, 1);
v___x_2184_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2170_, v___y_2171_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2191_ == 0)
{
lean_object* v_unused_2192_; 
v_unused_2192_ = lean_ctor_get(v___x_2184_, 0);
lean_dec(v_unused_2192_);
v___x_2186_ = v___x_2184_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_dec(v___x_2184_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
lean_ctor_set_tag(v___x_2186_, 1);
lean_ctor_set(v___x_2186_, 0, v_a_2183_);
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2183_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
else
{
lean_dec(v_a_2183_);
return v___x_2184_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11___boxed(lean_object* v_as_2193_, lean_object* v_sz_2194_, lean_object* v_i_2195_, lean_object* v_b_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
size_t v_sz_boxed_2200_; size_t v_i_boxed_2201_; lean_object* v_res_2202_; 
v_sz_boxed_2200_ = lean_unbox_usize(v_sz_2194_);
lean_dec(v_sz_2194_);
v_i_boxed_2201_ = lean_unbox_usize(v_i_2195_);
lean_dec(v_i_2195_);
v_res_2202_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(v_as_2193_, v_sz_boxed_2200_, v_i_boxed_2201_, v_b_2196_, v___y_2197_, v___y_2198_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec_ref(v_as_2193_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(lean_object* v_as_2203_, size_t v_sz_2204_, size_t v_i_2205_, lean_object* v_b_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_){
_start:
{
uint8_t v___x_2210_; 
v___x_2210_ = lean_usize_dec_lt(v_i_2205_, v_sz_2204_);
if (v___x_2210_ == 0)
{
lean_object* v___x_2211_; 
v___x_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2211_, 0, v_b_2206_);
return v___x_2211_;
}
else
{
lean_object* v_a_2212_; lean_object* v_declNames_2213_; lean_object* v___x_2214_; size_t v_sz_2215_; size_t v___x_2216_; lean_object* v___x_2217_; 
v_a_2212_ = lean_array_uget_borrowed(v_as_2203_, v_i_2205_);
v_declNames_2213_ = lean_ctor_get(v_a_2212_, 0);
v___x_2214_ = lean_box(0);
v_sz_2215_ = lean_array_size(v_declNames_2213_);
v___x_2216_ = ((size_t)0ULL);
v___x_2217_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(v_declNames_2213_, v_sz_2215_, v___x_2216_, v___x_2214_, v___y_2207_, v___y_2208_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v___x_2218_; 
lean_dec_ref_known(v___x_2217_, 1);
v___x_2218_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v___y_2208_);
if (lean_obj_tag(v___x_2218_) == 0)
{
lean_object* v_a_2219_; lean_object* v_unreported_2220_; lean_object* v___x_2221_; 
v_a_2219_ = lean_ctor_get(v___x_2218_, 0);
lean_inc(v_a_2219_);
lean_dec_ref_known(v___x_2218_, 1);
v_unreported_2220_ = lean_ctor_get(v_a_2219_, 1);
lean_inc_ref(v_unreported_2220_);
lean_dec(v_a_2219_);
v___x_2221_ = l_Lean_PersistentArray_forIn___at___00main_spec__12(v_unreported_2220_, v___x_2214_, v___y_2207_, v___y_2208_);
lean_dec_ref(v_unreported_2220_);
if (lean_obj_tag(v___x_2221_) == 0)
{
size_t v___x_2222_; size_t v___x_2223_; 
lean_dec_ref_known(v___x_2221_, 1);
v___x_2222_ = ((size_t)1ULL);
v___x_2223_ = lean_usize_add(v_i_2205_, v___x_2222_);
v_i_2205_ = v___x_2223_;
v_b_2206_ = v___x_2214_;
goto _start;
}
else
{
return v___x_2221_;
}
}
else
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
v_a_2225_ = lean_ctor_get(v___x_2218_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v___x_2218_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2218_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2228_ == 0)
{
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2225_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
else
{
return v___x_2217_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13___boxed(lean_object* v_as_2233_, lean_object* v_sz_2234_, lean_object* v_i_2235_, lean_object* v_b_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
size_t v_sz_boxed_2240_; size_t v_i_boxed_2241_; lean_object* v_res_2242_; 
v_sz_boxed_2240_ = lean_unbox_usize(v_sz_2234_);
lean_dec(v_sz_2234_);
v_i_boxed_2241_ = lean_unbox_usize(v_i_2235_);
lean_dec(v_i_2235_);
v_res_2242_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(v_as_2233_, v_sz_boxed_2240_, v_i_boxed_2241_, v_b_2236_, v___y_2237_, v___y_2238_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec_ref(v_as_2233_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(lean_object* v_as_2243_, size_t v_i_2244_, size_t v_stop_2245_, lean_object* v_b_2246_){
_start:
{
uint8_t v___x_2247_; 
v___x_2247_ = lean_usize_dec_eq(v_i_2244_, v_stop_2245_);
if (v___x_2247_ == 0)
{
lean_object* v___x_2248_; lean_object* v_name_2249_; lean_object* v___x_2250_; size_t v___x_2251_; size_t v___x_2252_; 
v___x_2248_ = lean_array_uget_borrowed(v_as_2243_, v_i_2244_);
v_name_2249_ = lean_ctor_get(v___x_2248_, 0);
lean_inc(v_name_2249_);
v___x_2250_ = l_Lean_Compiler_LCNF_setDeclPublic(v_b_2246_, v_name_2249_);
v___x_2251_ = ((size_t)1ULL);
v___x_2252_ = lean_usize_add(v_i_2244_, v___x_2251_);
v_i_2244_ = v___x_2252_;
v_b_2246_ = v___x_2250_;
goto _start;
}
else
{
return v_b_2246_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___boxed(lean_object* v_as_2254_, lean_object* v_i_2255_, lean_object* v_stop_2256_, lean_object* v_b_2257_){
_start:
{
size_t v_i_boxed_2258_; size_t v_stop_boxed_2259_; lean_object* v_res_2260_; 
v_i_boxed_2258_ = lean_unbox_usize(v_i_2255_);
lean_dec(v_i_2255_);
v_stop_boxed_2259_ = lean_unbox_usize(v_stop_2256_);
lean_dec(v_stop_2256_);
v_res_2260_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v_as_2254_, v_i_boxed_2258_, v_stop_boxed_2259_, v_b_2257_);
lean_dec_ref(v_as_2254_);
return v_res_2260_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0(uint8_t v_suppressElabErrors_2261_, uint8_t v___y_2262_, lean_object* v_x_2263_){
_start:
{
if (lean_obj_tag(v_x_2263_) == 1)
{
lean_object* v_pre_2264_; 
v_pre_2264_ = lean_ctor_get(v_x_2263_, 0);
switch(lean_obj_tag(v_pre_2264_))
{
case 1:
{
lean_object* v_pre_2265_; 
v_pre_2265_ = lean_ctor_get(v_pre_2264_, 0);
switch(lean_obj_tag(v_pre_2265_))
{
case 0:
{
lean_object* v_str_2266_; lean_object* v_str_2267_; lean_object* v___x_2268_; uint8_t v___x_2269_; 
v_str_2266_ = lean_ctor_get(v_x_2263_, 1);
v_str_2267_ = lean_ctor_get(v_pre_2264_, 1);
v___x_2268_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0));
v___x_2269_ = lean_string_dec_eq(v_str_2267_, v___x_2268_);
if (v___x_2269_ == 0)
{
lean_object* v___x_2270_; uint8_t v___x_2271_; 
v___x_2270_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1));
v___x_2271_ = lean_string_dec_eq(v_str_2267_, v___x_2270_);
if (v___x_2271_ == 0)
{
return v___x_2271_;
}
else
{
lean_object* v___x_2272_; uint8_t v___x_2273_; 
v___x_2272_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2));
v___x_2273_ = lean_string_dec_eq(v_str_2266_, v___x_2272_);
if (v___x_2273_ == 0)
{
return v___x_2273_;
}
else
{
return v_suppressElabErrors_2261_;
}
}
}
else
{
lean_object* v___x_2274_; uint8_t v___x_2275_; 
v___x_2274_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3));
v___x_2275_ = lean_string_dec_eq(v_str_2266_, v___x_2274_);
if (v___x_2275_ == 0)
{
return v___x_2275_;
}
else
{
return v_suppressElabErrors_2261_;
}
}
}
case 1:
{
lean_object* v_pre_2276_; 
v_pre_2276_ = lean_ctor_get(v_pre_2265_, 0);
if (lean_obj_tag(v_pre_2276_) == 0)
{
lean_object* v_str_2277_; lean_object* v_str_2278_; lean_object* v_str_2279_; lean_object* v___x_2280_; uint8_t v___x_2281_; 
v_str_2277_ = lean_ctor_get(v_x_2263_, 1);
v_str_2278_ = lean_ctor_get(v_pre_2264_, 1);
v_str_2279_ = lean_ctor_get(v_pre_2265_, 1);
v___x_2280_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4));
v___x_2281_ = lean_string_dec_eq(v_str_2279_, v___x_2280_);
if (v___x_2281_ == 0)
{
return v___x_2281_;
}
else
{
lean_object* v___x_2282_; uint8_t v___x_2283_; 
v___x_2282_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5));
v___x_2283_ = lean_string_dec_eq(v_str_2278_, v___x_2282_);
if (v___x_2283_ == 0)
{
return v___x_2283_;
}
else
{
lean_object* v___x_2284_; uint8_t v___x_2285_; 
v___x_2284_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6));
v___x_2285_ = lean_string_dec_eq(v_str_2277_, v___x_2284_);
if (v___x_2285_ == 0)
{
return v___x_2285_;
}
else
{
return v_suppressElabErrors_2261_;
}
}
}
}
else
{
return v___y_2262_;
}
}
default: 
{
return v___y_2262_;
}
}
}
case 0:
{
lean_object* v_str_2286_; lean_object* v___x_2287_; uint8_t v___x_2288_; 
v_str_2286_ = lean_ctor_get(v_x_2263_, 1);
v___x_2287_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_2288_ = lean_string_dec_eq(v_str_2286_, v___x_2287_);
if (v___x_2288_ == 0)
{
return v___x_2288_;
}
else
{
return v_suppressElabErrors_2261_;
}
}
default: 
{
return v___y_2262_;
}
}
}
else
{
return v___y_2262_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0___boxed(lean_object* v_suppressElabErrors_2289_, lean_object* v___y_2290_, lean_object* v_x_2291_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2292_; uint8_t v___y_37794__boxed_2293_; uint8_t v_res_2294_; lean_object* v_r_2295_; 
v_suppressElabErrors_boxed_2292_ = lean_unbox(v_suppressElabErrors_2289_);
v___y_37794__boxed_2293_ = lean_unbox(v___y_2290_);
v_res_2294_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0(v_suppressElabErrors_boxed_2292_, v___y_37794__boxed_2293_, v_x_2291_);
lean_dec(v_x_2291_);
v_r_2295_ = lean_box(v_res_2294_);
return v_r_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(lean_object* v_ref_2296_, lean_object* v_msgData_2297_, uint8_t v_severity_2298_, uint8_t v_isSilent_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v___y_2304_; lean_object* v___y_2305_; uint8_t v___y_2306_; lean_object* v___y_2307_; uint8_t v___y_2308_; lean_object* v___y_2309_; lean_object* v___y_2310_; lean_object* v___y_2311_; lean_object* v___y_2312_; lean_object* v___y_2340_; uint8_t v___y_2341_; uint8_t v___y_2342_; lean_object* v___y_2343_; uint8_t v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v___y_2366_; uint8_t v___y_2367_; lean_object* v___y_2368_; uint8_t v___y_2369_; uint8_t v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2376_; uint8_t v___y_2377_; lean_object* v___y_2378_; uint8_t v___y_2379_; lean_object* v___y_2380_; uint8_t v___y_2381_; uint8_t v___x_2386_; uint8_t v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2391_; uint8_t v___y_2392_; uint8_t v___y_2393_; uint8_t v___y_2395_; uint8_t v___x_2409_; 
v___x_2386_ = 2;
v___x_2409_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2298_, v___x_2386_);
if (v___x_2409_ == 0)
{
v___y_2395_ = v___x_2409_;
goto v___jp_2394_;
}
else
{
uint8_t v___x_2410_; 
lean_inc_ref(v_msgData_2297_);
v___x_2410_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2297_);
v___y_2395_ = v___x_2410_;
goto v___jp_2394_;
}
v___jp_2303_:
{
lean_object* v___x_2313_; lean_object* v_currNamespace_2314_; lean_object* v_openDecls_2315_; lean_object* v_env_2316_; lean_object* v_nextMacroScope_2317_; lean_object* v_ngen_2318_; lean_object* v_auxDeclNGen_2319_; lean_object* v_traceState_2320_; lean_object* v_cache_2321_; lean_object* v_messages_2322_; lean_object* v_infoState_2323_; lean_object* v_snapshotTasks_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2338_; 
v___x_2313_ = lean_st_ref_take(v___y_2312_);
v_currNamespace_2314_ = lean_ctor_get(v___y_2311_, 5);
v_openDecls_2315_ = lean_ctor_get(v___y_2311_, 6);
v_env_2316_ = lean_ctor_get(v___x_2313_, 0);
v_nextMacroScope_2317_ = lean_ctor_get(v___x_2313_, 1);
v_ngen_2318_ = lean_ctor_get(v___x_2313_, 2);
v_auxDeclNGen_2319_ = lean_ctor_get(v___x_2313_, 3);
v_traceState_2320_ = lean_ctor_get(v___x_2313_, 4);
v_cache_2321_ = lean_ctor_get(v___x_2313_, 5);
v_messages_2322_ = lean_ctor_get(v___x_2313_, 6);
v_infoState_2323_ = lean_ctor_get(v___x_2313_, 7);
v_snapshotTasks_2324_ = lean_ctor_get(v___x_2313_, 8);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2326_ = v___x_2313_;
v_isShared_2327_ = v_isSharedCheck_2338_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_snapshotTasks_2324_);
lean_inc(v_infoState_2323_);
lean_inc(v_messages_2322_);
lean_inc(v_cache_2321_);
lean_inc(v_traceState_2320_);
lean_inc(v_auxDeclNGen_2319_);
lean_inc(v_ngen_2318_);
lean_inc(v_nextMacroScope_2317_);
lean_inc(v_env_2316_);
lean_dec(v___x_2313_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2338_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2333_; 
lean_inc(v_openDecls_2315_);
lean_inc(v_currNamespace_2314_);
v___x_2328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2328_, 0, v_currNamespace_2314_);
lean_ctor_set(v___x_2328_, 1, v_openDecls_2315_);
v___x_2329_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2328_);
lean_ctor_set(v___x_2329_, 1, v___y_2309_);
lean_inc_ref(v___y_2304_);
lean_inc_ref(v___y_2310_);
v___x_2330_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2330_, 0, v___y_2310_);
lean_ctor_set(v___x_2330_, 1, v___y_2307_);
lean_ctor_set(v___x_2330_, 2, v___y_2305_);
lean_ctor_set(v___x_2330_, 3, v___y_2304_);
lean_ctor_set(v___x_2330_, 4, v___x_2329_);
lean_ctor_set_uint8(v___x_2330_, sizeof(void*)*5, v___y_2308_);
lean_ctor_set_uint8(v___x_2330_, sizeof(void*)*5 + 1, v___y_2306_);
lean_ctor_set_uint8(v___x_2330_, sizeof(void*)*5 + 2, v_isSilent_2299_);
v___x_2331_ = l_Lean_MessageLog_add(v___x_2330_, v_messages_2322_);
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 6, v___x_2331_);
v___x_2333_ = v___x_2326_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_env_2316_);
lean_ctor_set(v_reuseFailAlloc_2337_, 1, v_nextMacroScope_2317_);
lean_ctor_set(v_reuseFailAlloc_2337_, 2, v_ngen_2318_);
lean_ctor_set(v_reuseFailAlloc_2337_, 3, v_auxDeclNGen_2319_);
lean_ctor_set(v_reuseFailAlloc_2337_, 4, v_traceState_2320_);
lean_ctor_set(v_reuseFailAlloc_2337_, 5, v_cache_2321_);
lean_ctor_set(v_reuseFailAlloc_2337_, 6, v___x_2331_);
lean_ctor_set(v_reuseFailAlloc_2337_, 7, v_infoState_2323_);
lean_ctor_set(v_reuseFailAlloc_2337_, 8, v_snapshotTasks_2324_);
v___x_2333_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2334_ = lean_st_ref_put(v___y_2312_, v___x_2333_);
v___x_2335_ = lean_box(0);
v___x_2336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2335_);
return v___x_2336_;
}
}
}
v___jp_2339_:
{
lean_object* v_fileName_2347_; lean_object* v_fileMap_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2364_; 
v_fileName_2347_ = lean_ctor_get(v___y_2345_, 0);
v_fileMap_2348_ = lean_ctor_get(v___y_2345_, 1);
v___x_2349_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2297_);
v___x_2350_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(v___x_2349_, v___y_2300_, v___y_2301_);
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2353_ = v___x_2350_;
v_isShared_2354_ = v_isSharedCheck_2364_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2350_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2364_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
lean_inc_ref_n(v_fileMap_2348_, 2);
v___x_2355_ = l_Lean_FileMap_toPosition(v_fileMap_2348_, v___y_2343_);
lean_dec(v___y_2343_);
v___x_2356_ = l_Lean_FileMap_toPosition(v_fileMap_2348_, v___y_2346_);
lean_dec(v___y_2346_);
v___x_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2356_);
v___x_2358_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1));
if (v___y_2341_ == 0)
{
lean_del_object(v___x_2353_);
lean_dec_ref(v___y_2340_);
v___y_2304_ = v___x_2358_;
v___y_2305_ = v___x_2357_;
v___y_2306_ = v___y_2342_;
v___y_2307_ = v___x_2355_;
v___y_2308_ = v___y_2344_;
v___y_2309_ = v_a_2351_;
v___y_2310_ = v_fileName_2347_;
v___y_2311_ = v___y_2300_;
v___y_2312_ = v___y_2301_;
goto v___jp_2303_;
}
else
{
uint8_t v___x_2359_; 
lean_inc(v_a_2351_);
v___x_2359_ = l_Lean_MessageData_hasTag(v___y_2340_, v_a_2351_);
if (v___x_2359_ == 0)
{
lean_object* v___x_2360_; lean_object* v___x_2362_; 
lean_dec_ref_known(v___x_2357_, 1);
lean_dec_ref(v___x_2355_);
lean_dec(v_a_2351_);
v___x_2360_ = lean_box(0);
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 0, v___x_2360_);
v___x_2362_ = v___x_2353_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2360_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
else
{
lean_del_object(v___x_2353_);
v___y_2304_ = v___x_2358_;
v___y_2305_ = v___x_2357_;
v___y_2306_ = v___y_2342_;
v___y_2307_ = v___x_2355_;
v___y_2308_ = v___y_2344_;
v___y_2309_ = v_a_2351_;
v___y_2310_ = v_fileName_2347_;
v___y_2311_ = v___y_2300_;
v___y_2312_ = v___y_2301_;
goto v___jp_2303_;
}
}
}
}
v___jp_2365_:
{
lean_object* v___x_2373_; 
v___x_2373_ = l_Lean_Syntax_getTailPos_x3f(v___y_2368_, v___y_2370_);
lean_dec(v___y_2368_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_inc(v___y_2372_);
v___y_2340_ = v___y_2366_;
v___y_2341_ = v___y_2367_;
v___y_2342_ = v___y_2369_;
v___y_2343_ = v___y_2372_;
v___y_2344_ = v___y_2370_;
v___y_2345_ = v___y_2371_;
v___y_2346_ = v___y_2372_;
goto v___jp_2339_;
}
else
{
lean_object* v_val_2374_; 
v_val_2374_ = lean_ctor_get(v___x_2373_, 0);
lean_inc(v_val_2374_);
lean_dec_ref_known(v___x_2373_, 1);
v___y_2340_ = v___y_2366_;
v___y_2341_ = v___y_2367_;
v___y_2342_ = v___y_2369_;
v___y_2343_ = v___y_2372_;
v___y_2344_ = v___y_2370_;
v___y_2345_ = v___y_2371_;
v___y_2346_ = v_val_2374_;
goto v___jp_2339_;
}
}
v___jp_2375_:
{
lean_object* v_ref_2382_; lean_object* v___x_2383_; 
v_ref_2382_ = l_Lean_replaceRef(v_ref_2296_, v___y_2378_);
v___x_2383_ = l_Lean_Syntax_getPos_x3f(v_ref_2382_, v___y_2379_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v___x_2384_; 
v___x_2384_ = lean_unsigned_to_nat(0u);
v___y_2366_ = v___y_2376_;
v___y_2367_ = v___y_2377_;
v___y_2368_ = v_ref_2382_;
v___y_2369_ = v___y_2381_;
v___y_2370_ = v___y_2379_;
v___y_2371_ = v___y_2380_;
v___y_2372_ = v___x_2384_;
goto v___jp_2365_;
}
else
{
lean_object* v_val_2385_; 
v_val_2385_ = lean_ctor_get(v___x_2383_, 0);
lean_inc(v_val_2385_);
lean_dec_ref_known(v___x_2383_, 1);
v___y_2366_ = v___y_2376_;
v___y_2367_ = v___y_2377_;
v___y_2368_ = v_ref_2382_;
v___y_2369_ = v___y_2381_;
v___y_2370_ = v___y_2379_;
v___y_2371_ = v___y_2380_;
v___y_2372_ = v_val_2385_;
goto v___jp_2365_;
}
}
v___jp_2387_:
{
if (v___y_2393_ == 0)
{
v___y_2376_ = v___y_2391_;
v___y_2377_ = v___y_2388_;
v___y_2378_ = v___y_2389_;
v___y_2379_ = v___y_2392_;
v___y_2380_ = v___y_2390_;
v___y_2381_ = v_severity_2298_;
goto v___jp_2375_;
}
else
{
v___y_2376_ = v___y_2391_;
v___y_2377_ = v___y_2388_;
v___y_2378_ = v___y_2389_;
v___y_2379_ = v___y_2392_;
v___y_2380_ = v___y_2390_;
v___y_2381_ = v___x_2386_;
goto v___jp_2375_;
}
}
v___jp_2394_:
{
if (v___y_2395_ == 0)
{
lean_object* v_toCold_2396_; lean_object* v_options_2397_; lean_object* v_ref_2398_; uint8_t v_suppressElabErrors_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___f_2402_; uint8_t v___x_2403_; uint8_t v___x_2404_; 
v_toCold_2396_ = lean_ctor_get(v___y_2300_, 0);
v_options_2397_ = lean_ctor_get(v___y_2300_, 1);
v_ref_2398_ = lean_ctor_get(v___y_2300_, 4);
v_suppressElabErrors_2399_ = lean_ctor_get_uint8(v___y_2300_, sizeof(void*)*10 + 1);
v___x_2400_ = lean_box(v_suppressElabErrors_2399_);
v___x_2401_ = lean_box(v___y_2395_);
v___f_2402_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2402_, 0, v___x_2400_);
lean_closure_set(v___f_2402_, 1, v___x_2401_);
v___x_2403_ = 1;
v___x_2404_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2298_, v___x_2403_);
if (v___x_2404_ == 0)
{
v___y_2388_ = v_suppressElabErrors_2399_;
v___y_2389_ = v_ref_2398_;
v___y_2390_ = v_toCold_2396_;
v___y_2391_ = v___f_2402_;
v___y_2392_ = v___y_2395_;
v___y_2393_ = v___x_2404_;
goto v___jp_2387_;
}
else
{
lean_object* v___x_2405_; uint8_t v___x_2406_; 
v___x_2405_ = l_Lean_warningAsError;
v___x_2406_ = l_Lean_Option_get___at___00main_spec__8(v_options_2397_, v___x_2405_);
v___y_2388_ = v_suppressElabErrors_2399_;
v___y_2389_ = v_ref_2398_;
v___y_2390_ = v_toCold_2396_;
v___y_2391_ = v___f_2402_;
v___y_2392_ = v___y_2395_;
v___y_2393_ = v___x_2406_;
goto v___jp_2387_;
}
}
else
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
lean_dec_ref(v_msgData_2297_);
v___x_2407_ = lean_box(0);
v___x_2408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2407_);
return v___x_2408_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___boxed(lean_object* v_ref_2411_, lean_object* v_msgData_2412_, lean_object* v_severity_2413_, lean_object* v_isSilent_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
uint8_t v_severity_boxed_2418_; uint8_t v_isSilent_boxed_2419_; lean_object* v_res_2420_; 
v_severity_boxed_2418_ = lean_unbox(v_severity_2413_);
v_isSilent_boxed_2419_ = lean_unbox(v_isSilent_2414_);
v_res_2420_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(v_ref_2411_, v_msgData_2412_, v_severity_boxed_2418_, v_isSilent_boxed_2419_, v___y_2415_, v___y_2416_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v_ref_2411_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(lean_object* v_msgData_2421_, uint8_t v_severity_2422_, uint8_t v_isSilent_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v_ref_2427_; lean_object* v___x_2428_; 
v_ref_2427_ = lean_ctor_get(v___y_2424_, 4);
v___x_2428_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(v_ref_2427_, v_msgData_2421_, v_severity_2422_, v_isSilent_2423_, v___y_2424_, v___y_2425_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30___boxed(lean_object* v_msgData_2429_, lean_object* v_severity_2430_, lean_object* v_isSilent_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
uint8_t v_severity_boxed_2435_; uint8_t v_isSilent_boxed_2436_; lean_object* v_res_2437_; 
v_severity_boxed_2435_ = lean_unbox(v_severity_2430_);
v_isSilent_boxed_2436_ = lean_unbox(v_isSilent_2431_);
v_res_2437_ = l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(v_msgData_2429_, v_severity_boxed_2435_, v_isSilent_boxed_2436_, v___y_2432_, v___y_2433_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__14(lean_object* v_msgData_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
uint8_t v___x_2442_; uint8_t v___x_2443_; lean_object* v___x_2444_; 
v___x_2442_ = 2;
v___x_2443_ = 0;
v___x_2444_ = l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(v_msgData_2438_, v___x_2442_, v___x_2443_, v___y_2439_, v___y_2440_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__14___boxed(lean_object* v_msgData_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l_Lean_logError___at___00main_spec__14(v_msgData_2445_, v___y_2446_, v___y_2447_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(lean_object* v_x2_2450_, lean_object* v_as_2451_, size_t v_i_2452_, size_t v_stop_2453_, lean_object* v_b_2454_){
_start:
{
uint8_t v___x_2455_; 
v___x_2455_ = lean_usize_dec_eq(v_i_2452_, v_stop_2453_);
if (v___x_2455_ == 0)
{
lean_object* v___x_2456_; lean_object* v___x_2457_; size_t v___x_2458_; size_t v___x_2459_; 
v___x_2456_ = lean_array_uget_borrowed(v_as_2451_, v_i_2452_);
lean_inc_ref(v_x2_2450_);
lean_inc(v___x_2456_);
v___x_2457_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2456_, v_x2_2450_, v_b_2454_);
v___x_2458_ = ((size_t)1ULL);
v___x_2459_ = lean_usize_add(v_i_2452_, v___x_2458_);
v_i_2452_ = v___x_2459_;
v_b_2454_ = v___x_2457_;
goto _start;
}
else
{
lean_dec_ref(v_x2_2450_);
return v_b_2454_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2___boxed(lean_object* v_x2_2461_, lean_object* v_as_2462_, lean_object* v_i_2463_, lean_object* v_stop_2464_, lean_object* v_b_2465_){
_start:
{
size_t v_i_boxed_2466_; size_t v_stop_boxed_2467_; lean_object* v_res_2468_; 
v_i_boxed_2466_ = lean_unbox_usize(v_i_2463_);
lean_dec(v_i_2463_);
v_stop_boxed_2467_ = lean_unbox_usize(v_stop_2464_);
lean_dec(v_stop_2464_);
v_res_2468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v_x2_2461_, v_as_2462_, v_i_boxed_2466_, v_stop_boxed_2467_, v_b_2465_);
lean_dec_ref(v_as_2462_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(lean_object* v_as_2469_, size_t v_i_2470_, size_t v_stop_2471_, lean_object* v_b_2472_){
_start:
{
lean_object* v___y_2474_; uint8_t v___x_2478_; 
v___x_2478_ = lean_usize_dec_eq(v_i_2470_, v_stop_2471_);
if (v___x_2478_ == 0)
{
lean_object* v___x_2479_; lean_object* v_declNames_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; uint8_t v___x_2483_; 
v___x_2479_ = lean_array_uget_borrowed(v_as_2469_, v_i_2470_);
v_declNames_2480_ = lean_ctor_get(v___x_2479_, 0);
v___x_2481_ = lean_unsigned_to_nat(0u);
v___x_2482_ = lean_array_get_size(v_declNames_2480_);
v___x_2483_ = lean_nat_dec_lt(v___x_2481_, v___x_2482_);
if (v___x_2483_ == 0)
{
v___y_2474_ = v_b_2472_;
goto v___jp_2473_;
}
else
{
uint8_t v___x_2484_; 
v___x_2484_ = lean_nat_dec_le(v___x_2482_, v___x_2482_);
if (v___x_2484_ == 0)
{
if (v___x_2483_ == 0)
{
v___y_2474_ = v_b_2472_;
goto v___jp_2473_;
}
else
{
size_t v___x_2485_; size_t v___x_2486_; lean_object* v___x_2487_; 
v___x_2485_ = ((size_t)0ULL);
v___x_2486_ = lean_usize_of_nat(v___x_2482_);
lean_inc(v___x_2479_);
v___x_2487_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_2479_, v_declNames_2480_, v___x_2485_, v___x_2486_, v_b_2472_);
v___y_2474_ = v___x_2487_;
goto v___jp_2473_;
}
}
else
{
size_t v___x_2488_; size_t v___x_2489_; lean_object* v___x_2490_; 
v___x_2488_ = ((size_t)0ULL);
v___x_2489_ = lean_usize_of_nat(v___x_2482_);
lean_inc(v___x_2479_);
v___x_2490_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_2479_, v_declNames_2480_, v___x_2488_, v___x_2489_, v_b_2472_);
v___y_2474_ = v___x_2490_;
goto v___jp_2473_;
}
}
}
else
{
return v_b_2472_;
}
v___jp_2473_:
{
size_t v___x_2475_; size_t v___x_2476_; 
v___x_2475_ = ((size_t)1ULL);
v___x_2476_ = lean_usize_add(v_i_2470_, v___x_2475_);
v_i_2470_ = v___x_2476_;
v_b_2472_ = v___y_2474_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___boxed(lean_object* v_as_2491_, lean_object* v_i_2492_, lean_object* v_stop_2493_, lean_object* v_b_2494_){
_start:
{
size_t v_i_boxed_2495_; size_t v_stop_boxed_2496_; lean_object* v_res_2497_; 
v_i_boxed_2495_ = lean_unbox_usize(v_i_2492_);
lean_dec(v_i_2492_);
v_stop_boxed_2496_ = lean_unbox_usize(v_stop_2493_);
lean_dec(v_stop_2493_);
v_res_2497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v_as_2491_, v_i_boxed_2495_, v_stop_boxed_2496_, v_b_2494_);
lean_dec_ref(v_as_2491_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(lean_object* v_a_2498_, lean_object* v_as_2499_, size_t v_i_2500_, size_t v_stop_2501_, lean_object* v_b_2502_){
_start:
{
lean_object* v___y_2504_; uint8_t v___x_2508_; 
v___x_2508_ = lean_usize_dec_eq(v_i_2500_, v_stop_2501_);
if (v___x_2508_ == 0)
{
lean_object* v___x_2509_; lean_object* v_name_2510_; uint8_t v___x_2511_; 
v___x_2509_ = lean_array_uget_borrowed(v_as_2499_, v_i_2500_);
v_name_2510_ = lean_ctor_get(v___x_2509_, 0);
lean_inc(v_name_2510_);
lean_inc_ref(v_a_2498_);
v___x_2511_ = l_Lean_isExtern(v_a_2498_, v_name_2510_);
if (v___x_2511_ == 0)
{
v___y_2504_ = v_b_2502_;
goto v___jp_2503_;
}
else
{
lean_object* v___x_2512_; 
lean_inc(v___x_2509_);
v___x_2512_ = lean_array_push(v_b_2502_, v___x_2509_);
v___y_2504_ = v___x_2512_;
goto v___jp_2503_;
}
}
else
{
lean_dec_ref(v_a_2498_);
return v_b_2502_;
}
v___jp_2503_:
{
size_t v___x_2505_; size_t v___x_2506_; 
v___x_2505_ = ((size_t)1ULL);
v___x_2506_ = lean_usize_add(v_i_2500_, v___x_2505_);
v_i_2500_ = v___x_2506_;
v_b_2502_ = v___y_2504_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19___boxed(lean_object* v_a_2513_, lean_object* v_as_2514_, lean_object* v_i_2515_, lean_object* v_stop_2516_, lean_object* v_b_2517_){
_start:
{
size_t v_i_boxed_2518_; size_t v_stop_boxed_2519_; lean_object* v_res_2520_; 
v_i_boxed_2518_ = lean_unbox_usize(v_i_2515_);
lean_dec(v_i_2515_);
v_stop_boxed_2519_ = lean_unbox_usize(v_stop_2516_);
lean_dec(v_stop_2516_);
v_res_2520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_2513_, v_as_2514_, v_i_boxed_2518_, v_stop_boxed_2519_, v_b_2517_);
lean_dec_ref(v_as_2514_);
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(lean_object* v_as_2521_, size_t v_sz_2522_, size_t v_i_2523_, lean_object* v_b_2524_){
_start:
{
uint8_t v___x_2526_; 
v___x_2526_ = lean_usize_dec_lt(v_i_2523_, v_sz_2522_);
if (v___x_2526_ == 0)
{
lean_object* v___x_2527_; 
v___x_2527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2527_, 0, v_b_2524_);
return v___x_2527_;
}
else
{
uint8_t v___x_2528_; lean_object* v_a_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
lean_dec_ref(v_b_2524_);
v___x_2528_ = 0;
v_a_2529_ = lean_array_uget_borrowed(v_as_2521_, v_i_2523_);
lean_inc(v_a_2529_);
v___x_2530_ = l_Lean_Message_toString(v_a_2529_, v___x_2528_);
v___x_2531_ = l_IO_eprintln___at___00main_spec__6(v___x_2530_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v___x_2532_; size_t v___x_2533_; size_t v___x_2534_; 
lean_dec_ref_known(v___x_2531_, 1);
v___x_2532_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_2533_ = ((size_t)1ULL);
v___x_2534_ = lean_usize_add(v_i_2523_, v___x_2533_);
v_i_2523_ = v___x_2534_;
v_b_2524_ = v___x_2532_;
goto _start;
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
v_a_2536_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___x_2531_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2531_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27___boxed(lean_object* v_as_2544_, lean_object* v_sz_2545_, lean_object* v_i_2546_, lean_object* v_b_2547_, lean_object* v___y_2548_){
_start:
{
size_t v_sz_boxed_2549_; size_t v_i_boxed_2550_; lean_object* v_res_2551_; 
v_sz_boxed_2549_ = lean_unbox_usize(v_sz_2545_);
lean_dec(v_sz_2545_);
v_i_boxed_2550_ = lean_unbox_usize(v_i_2546_);
lean_dec(v_i_2546_);
v_res_2551_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(v_as_2544_, v_sz_boxed_2549_, v_i_boxed_2550_, v_b_2547_);
lean_dec_ref(v_as_2544_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(lean_object* v_as_2552_, size_t v_sz_2553_, size_t v_i_2554_, lean_object* v_b_2555_){
_start:
{
uint8_t v___x_2557_; 
v___x_2557_ = lean_usize_dec_lt(v_i_2554_, v_sz_2553_);
if (v___x_2557_ == 0)
{
lean_object* v___x_2558_; 
v___x_2558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2558_, 0, v_b_2555_);
return v___x_2558_;
}
else
{
uint8_t v___x_2559_; lean_object* v_a_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
lean_dec_ref(v_b_2555_);
v___x_2559_ = 0;
v_a_2560_ = lean_array_uget_borrowed(v_as_2552_, v_i_2554_);
lean_inc(v_a_2560_);
v___x_2561_ = l_Lean_Message_toString(v_a_2560_, v___x_2559_);
v___x_2562_ = l_IO_eprintln___at___00main_spec__6(v___x_2561_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v___x_2563_; size_t v___x_2564_; size_t v___x_2565_; lean_object* v___x_2566_; 
lean_dec_ref_known(v___x_2562_, 1);
v___x_2563_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_2564_ = ((size_t)1ULL);
v___x_2565_ = lean_usize_add(v_i_2554_, v___x_2564_);
v___x_2566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(v_as_2552_, v_sz_2553_, v___x_2565_, v___x_2563_);
return v___x_2566_;
}
else
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2574_; 
v_a_2567_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2569_ = v___x_2562_;
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2562_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14___boxed(lean_object* v_as_2575_, lean_object* v_sz_2576_, lean_object* v_i_2577_, lean_object* v_b_2578_, lean_object* v___y_2579_){
_start:
{
size_t v_sz_boxed_2580_; size_t v_i_boxed_2581_; lean_object* v_res_2582_; 
v_sz_boxed_2580_ = lean_unbox_usize(v_sz_2576_);
lean_dec(v_sz_2576_);
v_i_boxed_2581_ = lean_unbox_usize(v_i_2577_);
lean_dec(v_i_2577_);
v_res_2582_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(v_as_2575_, v_sz_boxed_2580_, v_i_boxed_2581_, v_b_2578_);
lean_dec_ref(v_as_2575_);
return v_res_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(lean_object* v_init_2583_, lean_object* v_n_2584_, lean_object* v_b_2585_){
_start:
{
if (lean_obj_tag(v_n_2584_) == 0)
{
lean_object* v_cs_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; size_t v_sz_2590_; size_t v___x_2591_; lean_object* v___x_2592_; 
v_cs_2587_ = lean_ctor_get(v_n_2584_, 0);
v___x_2588_ = lean_box(0);
v___x_2589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2588_);
lean_ctor_set(v___x_2589_, 1, v_b_2585_);
v_sz_2590_ = lean_array_size(v_cs_2587_);
v___x_2591_ = ((size_t)0ULL);
v___x_2592_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_init_2583_, v_cs_2587_, v_sz_2590_, v___x_2591_, v___x_2589_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2607_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2595_ = v___x_2592_;
v_isShared_2596_ = v_isSharedCheck_2607_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2592_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2607_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v_fst_2597_; 
v_fst_2597_ = lean_ctor_get(v_a_2593_, 0);
if (lean_obj_tag(v_fst_2597_) == 0)
{
lean_object* v_snd_2598_; lean_object* v___x_2599_; lean_object* v___x_2601_; 
v_snd_2598_ = lean_ctor_get(v_a_2593_, 1);
lean_inc(v_snd_2598_);
lean_dec(v_a_2593_);
v___x_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2599_, 0, v_snd_2598_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 0, v___x_2599_);
v___x_2601_ = v___x_2595_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___x_2599_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
else
{
lean_object* v_val_2603_; lean_object* v___x_2605_; 
lean_inc_ref(v_fst_2597_);
lean_dec(v_a_2593_);
v_val_2603_ = lean_ctor_get(v_fst_2597_, 0);
lean_inc(v_val_2603_);
lean_dec_ref_known(v_fst_2597_, 1);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 0, v_val_2603_);
v___x_2605_ = v___x_2595_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_val_2603_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
else
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
v_a_2608_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v___x_2592_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2592_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2611_ == 0)
{
v___x_2613_ = v___x_2610_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2608_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
else
{
lean_object* v_vs_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; size_t v_sz_2619_; size_t v___x_2620_; lean_object* v___x_2621_; 
v_vs_2616_ = lean_ctor_get(v_n_2584_, 0);
v___x_2617_ = lean_box(0);
v___x_2618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2617_);
lean_ctor_set(v___x_2618_, 1, v_b_2585_);
v_sz_2619_ = lean_array_size(v_vs_2616_);
v___x_2620_ = ((size_t)0ULL);
v___x_2621_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(v_vs_2616_, v_sz_2619_, v___x_2620_, v___x_2618_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2636_; 
v_a_2622_ = lean_ctor_get(v___x_2621_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2624_ = v___x_2621_;
v_isShared_2625_ = v_isSharedCheck_2636_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___x_2621_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2636_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v_fst_2626_; 
v_fst_2626_ = lean_ctor_get(v_a_2622_, 0);
if (lean_obj_tag(v_fst_2626_) == 0)
{
lean_object* v_snd_2627_; lean_object* v___x_2628_; lean_object* v___x_2630_; 
v_snd_2627_ = lean_ctor_get(v_a_2622_, 1);
lean_inc(v_snd_2627_);
lean_dec(v_a_2622_);
v___x_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2628_, 0, v_snd_2627_);
if (v_isShared_2625_ == 0)
{
lean_ctor_set(v___x_2624_, 0, v___x_2628_);
v___x_2630_ = v___x_2624_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v___x_2628_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
else
{
lean_object* v_val_2632_; lean_object* v___x_2634_; 
lean_inc_ref(v_fst_2626_);
lean_dec(v_a_2622_);
v_val_2632_ = lean_ctor_get(v_fst_2626_, 0);
lean_inc(v_val_2632_);
lean_dec_ref_known(v_fst_2626_, 1);
if (v_isShared_2625_ == 0)
{
lean_ctor_set(v___x_2624_, 0, v_val_2632_);
v___x_2634_ = v___x_2624_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_val_2632_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
v_a_2637_ = lean_ctor_get(v___x_2621_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___x_2621_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2621_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2637_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(lean_object* v_init_2645_, lean_object* v_as_2646_, size_t v_sz_2647_, size_t v_i_2648_, lean_object* v_b_2649_){
_start:
{
uint8_t v___x_2651_; 
v___x_2651_ = lean_usize_dec_lt(v_i_2648_, v_sz_2647_);
if (v___x_2651_ == 0)
{
lean_object* v___x_2652_; 
v___x_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2652_, 0, v_b_2649_);
return v___x_2652_;
}
else
{
lean_object* v_snd_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2687_; 
v_snd_2653_ = lean_ctor_get(v_b_2649_, 1);
v_isSharedCheck_2687_ = !lean_is_exclusive(v_b_2649_);
if (v_isSharedCheck_2687_ == 0)
{
lean_object* v_unused_2688_; 
v_unused_2688_ = lean_ctor_get(v_b_2649_, 0);
lean_dec(v_unused_2688_);
v___x_2655_ = v_b_2649_;
v_isShared_2656_ = v_isSharedCheck_2687_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_snd_2653_);
lean_dec(v_b_2649_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2687_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v_a_2657_; lean_object* v___x_2658_; 
v_a_2657_ = lean_array_uget_borrowed(v_as_2646_, v_i_2648_);
lean_inc(v_snd_2653_);
v___x_2658_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2645_, v_a_2657_, v_snd_2653_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2678_; 
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2661_ = v___x_2658_;
v_isShared_2662_ = v_isSharedCheck_2678_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v___x_2658_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2678_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
if (lean_obj_tag(v_a_2659_) == 0)
{
lean_object* v___x_2663_; lean_object* v___x_2665_; 
v___x_2663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2663_, 0, v_a_2659_);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 0, v___x_2663_);
v___x_2665_ = v___x_2655_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v___x_2663_);
lean_ctor_set(v_reuseFailAlloc_2669_, 1, v_snd_2653_);
v___x_2665_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
lean_object* v___x_2667_; 
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 0, v___x_2665_);
v___x_2667_ = v___x_2661_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v___x_2665_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
else
{
lean_object* v_a_2670_; lean_object* v___x_2671_; lean_object* v___x_2673_; 
lean_del_object(v___x_2661_);
lean_dec(v_snd_2653_);
v_a_2670_ = lean_ctor_get(v_a_2659_, 0);
lean_inc(v_a_2670_);
lean_dec_ref_known(v_a_2659_, 1);
v___x_2671_ = lean_box(0);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 1, v_a_2670_);
lean_ctor_set(v___x_2655_, 0, v___x_2671_);
v___x_2673_ = v___x_2655_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2671_);
lean_ctor_set(v_reuseFailAlloc_2677_, 1, v_a_2670_);
v___x_2673_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
size_t v___x_2674_; size_t v___x_2675_; 
v___x_2674_ = ((size_t)1ULL);
v___x_2675_ = lean_usize_add(v_i_2648_, v___x_2674_);
v_i_2648_ = v___x_2675_;
v_b_2649_ = v___x_2673_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2686_; 
lean_del_object(v___x_2655_);
lean_dec(v_snd_2653_);
v_a_2679_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2681_ = v___x_2658_;
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2658_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2684_; 
if (v_isShared_2682_ == 0)
{
v___x_2684_ = v___x_2681_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_a_2679_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13___boxed(lean_object* v_init_2689_, lean_object* v_as_2690_, lean_object* v_sz_2691_, lean_object* v_i_2692_, lean_object* v_b_2693_, lean_object* v___y_2694_){
_start:
{
size_t v_sz_boxed_2695_; size_t v_i_boxed_2696_; lean_object* v_res_2697_; 
v_sz_boxed_2695_ = lean_unbox_usize(v_sz_2691_);
lean_dec(v_sz_2691_);
v_i_boxed_2696_ = lean_unbox_usize(v_i_2692_);
lean_dec(v_i_2692_);
v_res_2697_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_init_2689_, v_as_2690_, v_sz_boxed_2695_, v_i_boxed_2696_, v_b_2693_);
lean_dec_ref(v_as_2690_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10___boxed(lean_object* v_init_2698_, lean_object* v_n_2699_, lean_object* v_b_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2698_, v_n_2699_, v_b_2700_);
lean_dec_ref(v_n_2699_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(lean_object* v_as_2703_, size_t v_sz_2704_, size_t v_i_2705_, lean_object* v_b_2706_){
_start:
{
uint8_t v___x_2708_; 
v___x_2708_ = lean_usize_dec_lt(v_i_2705_, v_sz_2704_);
if (v___x_2708_ == 0)
{
lean_object* v___x_2709_; 
v___x_2709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2709_, 0, v_b_2706_);
return v___x_2709_;
}
else
{
uint8_t v___x_2710_; lean_object* v_a_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
lean_dec_ref(v_b_2706_);
v___x_2710_ = 0;
v_a_2711_ = lean_array_uget_borrowed(v_as_2703_, v_i_2705_);
lean_inc(v_a_2711_);
v___x_2712_ = l_Lean_Message_toString(v_a_2711_, v___x_2710_);
v___x_2713_ = l_IO_eprintln___at___00main_spec__6(v___x_2712_);
if (lean_obj_tag(v___x_2713_) == 0)
{
lean_object* v___x_2714_; size_t v___x_2715_; size_t v___x_2716_; 
lean_dec_ref_known(v___x_2713_, 1);
v___x_2714_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_2715_ = ((size_t)1ULL);
v___x_2716_ = lean_usize_add(v_i_2705_, v___x_2715_);
v_i_2705_ = v___x_2716_;
v_b_2706_ = v___x_2714_;
goto _start;
}
else
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2725_; 
v_a_2718_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2720_ = v___x_2713_;
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2713_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2723_; 
if (v_isShared_2721_ == 0)
{
v___x_2723_ = v___x_2720_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_a_2718_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16___boxed(lean_object* v_as_2726_, lean_object* v_sz_2727_, lean_object* v_i_2728_, lean_object* v_b_2729_, lean_object* v___y_2730_){
_start:
{
size_t v_sz_boxed_2731_; size_t v_i_boxed_2732_; lean_object* v_res_2733_; 
v_sz_boxed_2731_ = lean_unbox_usize(v_sz_2727_);
lean_dec(v_sz_2727_);
v_i_boxed_2732_ = lean_unbox_usize(v_i_2728_);
lean_dec(v_i_2728_);
v_res_2733_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(v_as_2726_, v_sz_boxed_2731_, v_i_boxed_2732_, v_b_2729_);
lean_dec_ref(v_as_2726_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(lean_object* v_as_2734_, size_t v_sz_2735_, size_t v_i_2736_, lean_object* v_b_2737_){
_start:
{
uint8_t v___x_2739_; 
v___x_2739_ = lean_usize_dec_lt(v_i_2736_, v_sz_2735_);
if (v___x_2739_ == 0)
{
lean_object* v___x_2740_; 
v___x_2740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2740_, 0, v_b_2737_);
return v___x_2740_;
}
else
{
uint8_t v___x_2741_; lean_object* v_a_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; 
lean_dec_ref(v_b_2737_);
v___x_2741_ = 0;
v_a_2742_ = lean_array_uget_borrowed(v_as_2734_, v_i_2736_);
lean_inc(v_a_2742_);
v___x_2743_ = l_Lean_Message_toString(v_a_2742_, v___x_2741_);
v___x_2744_ = l_IO_eprintln___at___00main_spec__6(v___x_2743_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v___x_2745_; size_t v___x_2746_; size_t v___x_2747_; lean_object* v___x_2748_; 
lean_dec_ref_known(v___x_2744_, 1);
v___x_2745_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_2746_ = ((size_t)1ULL);
v___x_2747_ = lean_usize_add(v_i_2736_, v___x_2746_);
v___x_2748_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(v_as_2734_, v_sz_2735_, v___x_2747_, v___x_2745_);
return v___x_2748_;
}
else
{
lean_object* v_a_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2756_; 
v_a_2749_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2751_ = v___x_2744_;
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_a_2749_);
lean_dec(v___x_2744_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11___boxed(lean_object* v_as_2757_, lean_object* v_sz_2758_, lean_object* v_i_2759_, lean_object* v_b_2760_, lean_object* v___y_2761_){
_start:
{
size_t v_sz_boxed_2762_; size_t v_i_boxed_2763_; lean_object* v_res_2764_; 
v_sz_boxed_2762_ = lean_unbox_usize(v_sz_2758_);
lean_dec(v_sz_2758_);
v_i_boxed_2763_ = lean_unbox_usize(v_i_2759_);
lean_dec(v_i_2759_);
v_res_2764_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_as_2757_, v_sz_boxed_2762_, v_i_boxed_2763_, v_b_2760_);
lean_dec_ref(v_as_2757_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7(lean_object* v_t_2765_, lean_object* v_init_2766_){
_start:
{
lean_object* v_root_2768_; lean_object* v_tail_2769_; lean_object* v___x_2770_; 
v_root_2768_ = lean_ctor_get(v_t_2765_, 0);
v_tail_2769_ = lean_ctor_get(v_t_2765_, 1);
v___x_2770_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2766_, v_root_2768_, v_init_2766_);
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2807_; 
v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2773_ = v___x_2770_;
v_isShared_2774_ = v_isSharedCheck_2807_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2770_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2807_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
if (lean_obj_tag(v_a_2771_) == 0)
{
lean_object* v_a_2775_; lean_object* v___x_2777_; 
v_a_2775_ = lean_ctor_get(v_a_2771_, 0);
lean_inc(v_a_2775_);
lean_dec_ref_known(v_a_2771_, 1);
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 0, v_a_2775_);
v___x_2777_ = v___x_2773_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2775_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
else
{
lean_object* v_a_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; size_t v_sz_2782_; size_t v___x_2783_; lean_object* v___x_2784_; 
lean_del_object(v___x_2773_);
v_a_2779_ = lean_ctor_get(v_a_2771_, 0);
lean_inc(v_a_2779_);
lean_dec_ref_known(v_a_2771_, 1);
v___x_2780_ = lean_box(0);
v___x_2781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2781_, 0, v___x_2780_);
lean_ctor_set(v___x_2781_, 1, v_a_2779_);
v_sz_2782_ = lean_array_size(v_tail_2769_);
v___x_2783_ = ((size_t)0ULL);
v___x_2784_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_tail_2769_, v_sz_2782_, v___x_2783_, v___x_2781_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2798_; 
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2787_ = v___x_2784_;
v_isShared_2788_ = v_isSharedCheck_2798_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2784_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2798_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v_fst_2789_; 
v_fst_2789_ = lean_ctor_get(v_a_2785_, 0);
if (lean_obj_tag(v_fst_2789_) == 0)
{
lean_object* v_snd_2790_; lean_object* v___x_2792_; 
v_snd_2790_ = lean_ctor_get(v_a_2785_, 1);
lean_inc(v_snd_2790_);
lean_dec(v_a_2785_);
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 0, v_snd_2790_);
v___x_2792_ = v___x_2787_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_snd_2790_);
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
lean_object* v_val_2794_; lean_object* v___x_2796_; 
lean_inc_ref(v_fst_2789_);
lean_dec(v_a_2785_);
v_val_2794_ = lean_ctor_get(v_fst_2789_, 0);
lean_inc(v_val_2794_);
lean_dec_ref_known(v_fst_2789_, 1);
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 0, v_val_2794_);
v___x_2796_ = v___x_2787_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_val_2794_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
else
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2806_; 
v_a_2799_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2801_ = v___x_2784_;
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___x_2784_);
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
}
else
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2815_; 
v_a_2808_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v___x_2770_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2770_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2813_; 
if (v_isShared_2811_ == 0)
{
v___x_2813_ = v___x_2810_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_a_2808_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7___boxed(lean_object* v_t_2816_, lean_object* v_init_2817_, lean_object* v___y_2818_){
_start:
{
lean_object* v_res_2819_; 
v_res_2819_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_t_2816_, v_init_2817_);
lean_dec_ref(v_t_2816_);
return v_res_2819_;
}
}
static lean_object* _init_l_main___closed__3(void){
_start:
{
lean_object* v___x_2823_; 
v___x_2823_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(lean_box(0), lean_box(0), lean_box(0));
return v___x_2823_;
}
}
static lean_object* _init_l_main___closed__4(void){
_start:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2824_ = l_Lean_instInhabitedClassState_default;
v___x_2825_ = lean_box(0);
v___x_2826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2825_);
lean_ctor_set(v___x_2826_, 1, v___x_2824_);
return v___x_2826_;
}
}
static lean_object* _init_l_main___closed__5(void){
_start:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2827_ = l_Lean_Meta_Match_Extension_instInhabitedState;
v___x_2828_ = lean_box(0);
v___x_2829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2828_);
lean_ctor_set(v___x_2829_, 1, v___x_2827_);
return v___x_2829_;
}
}
static lean_object* _init_l_main___closed__6(void){
_start:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2830_ = ((lean_object*)(l_main___closed__2));
v___x_2831_ = ((lean_object*)(l_main___closed__1));
v___x_2832_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_2831_, v___x_2830_);
return v___x_2832_;
}
}
static lean_object* _init_l_main___closed__7(void){
_start:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2833_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_2834_ = lean_box(0);
v___x_2835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2834_);
lean_ctor_set(v___x_2835_, 1, v___x_2833_);
return v___x_2835_;
}
}
static lean_object* _init_l_main___closed__8(void){
_start:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2836_ = lean_obj_once(&l_main___closed__7, &l_main___closed__7_once, _init_l_main___closed__7);
v___x_2837_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2836_);
return v___x_2837_;
}
}
static lean_object* _init_l_main___closed__9(void){
_start:
{
lean_object* v___x_2838_; 
v___x_2838_ = l_Array_instInhabited(lean_box(0));
return v___x_2838_;
}
}
static lean_object* _init_l_main___closed__15(void){
_start:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; 
v___x_2847_ = l_Lean_Options_empty;
v___x_2848_ = l_Lean_Core_getMaxHeartbeats(v___x_2847_);
return v___x_2848_;
}
}
static lean_object* _init_l_main___closed__20(void){
_start:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2853_ = ((lean_object*)(l_main___closed__19));
v___x_2854_ = lean_unsigned_to_nat(27u);
v___x_2855_ = lean_unsigned_to_nat(149u);
v___x_2856_ = ((lean_object*)(l_main___closed__18));
v___x_2857_ = ((lean_object*)(l_main___closed__17));
v___x_2858_ = l_mkPanicMessageWithDecl(v___x_2857_, v___x_2856_, v___x_2855_, v___x_2854_, v___x_2853_);
return v___x_2858_;
}
}
static lean_object* _init_l_main___closed__22(void){
_start:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2860_ = ((lean_object*)(l_main___closed__19));
v___x_2861_ = lean_unsigned_to_nat(51u);
v___x_2862_ = lean_unsigned_to_nat(122u);
v___x_2863_ = ((lean_object*)(l_main___closed__18));
v___x_2864_ = ((lean_object*)(l_main___closed__17));
v___x_2865_ = l_mkPanicMessageWithDecl(v___x_2864_, v___x_2863_, v___x_2862_, v___x_2861_, v___x_2860_);
return v___x_2865_;
}
}
static lean_object* _init_l_main___closed__23(void){
_start:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2866_ = lean_unsigned_to_nat(1u);
v___x_2867_ = l_Lean_firstFrontendMacroScope;
v___x_2868_ = lean_nat_add(v___x_2867_, v___x_2866_);
return v___x_2868_;
}
}
static lean_object* _init_l_main___closed__27(void){
_start:
{
lean_object* v___x_2875_; uint64_t v___x_2876_; lean_object* v___x_2877_; 
v___x_2875_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2876_ = 0ULL;
v___x_2877_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2877_, 0, v___x_2875_);
lean_ctor_set_uint64(v___x_2877_, sizeof(void*)*1, v___x_2876_);
return v___x_2877_;
}
}
static lean_object* _init_l_main___closed__28(void){
_start:
{
lean_object* v___x_2878_; 
v___x_2878_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2878_;
}
}
static lean_object* _init_l_main___closed__29(void){
_start:
{
lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2879_ = lean_obj_once(&l_main___closed__28, &l_main___closed__28_once, _init_l_main___closed__28);
v___x_2880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2879_);
return v___x_2880_;
}
}
static lean_object* _init_l_main___closed__30(void){
_start:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2881_ = lean_obj_once(&l_main___closed__29, &l_main___closed__29_once, _init_l_main___closed__29);
v___x_2882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2881_);
lean_ctor_set(v___x_2882_, 1, v___x_2881_);
return v___x_2882_;
}
}
static lean_object* _init_l_main___closed__31(void){
_start:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2883_ = l_Lean_NameSet_empty;
v___x_2884_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2885_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2884_);
lean_ctor_set(v___x_2885_, 1, v___x_2884_);
lean_ctor_set(v___x_2885_, 2, v___x_2883_);
return v___x_2885_;
}
}
static lean_object* _init_l_main___closed__32(void){
_start:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; uint8_t v___x_2888_; lean_object* v___x_2889_; 
v___x_2886_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2887_ = lean_obj_once(&l_main___closed__29, &l_main___closed__29_once, _init_l_main___closed__29);
v___x_2888_ = 1;
v___x_2889_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2889_, 0, v___x_2887_);
lean_ctor_set(v___x_2889_, 1, v___x_2887_);
lean_ctor_set(v___x_2889_, 2, v___x_2886_);
lean_ctor_set_uint8(v___x_2889_, sizeof(void*)*3, v___x_2888_);
return v___x_2889_;
}
}
static uint8_t _init_l_main___closed__37(void){
_start:
{
uint8_t v___x_2896_; uint8_t v___x_2897_; uint8_t v___x_2898_; 
v___x_2896_ = 2;
v___x_2897_ = 0;
v___x_2898_ = l_Lean_instOrdOLeanLevel_ord(v___x_2897_, v___x_2896_);
return v___x_2898_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_2899_; lean_object* v___x_2900_; 
v___x_2899_ = 1;
v___x_2900_ = lean_box_uint32(v___x_2899_);
return v___x_2900_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_2901_; lean_object* v___x_2902_; 
v___x_2901_ = 0;
v___x_2902_ = lean_box_uint32(v___x_2901_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_2903_){
_start:
{
if (lean_obj_tag(v_args_2903_) == 1)
{
lean_object* v_tail_2928_; 
v_tail_2928_ = lean_ctor_get(v_args_2903_, 1);
lean_inc(v_tail_2928_);
if (lean_obj_tag(v_tail_2928_) == 1)
{
lean_object* v_tail_2929_; 
v_tail_2929_ = lean_ctor_get(v_tail_2928_, 1);
lean_inc(v_tail_2929_);
if (lean_obj_tag(v_tail_2929_) == 1)
{
lean_object* v_head_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_3572_; 
v_head_2930_ = lean_ctor_get(v_args_2903_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v_args_2903_);
if (v_isSharedCheck_3572_ == 0)
{
lean_object* v_unused_3573_; 
v_unused_3573_ = lean_ctor_get(v_args_2903_, 1);
lean_dec(v_unused_3573_);
v___x_2932_ = v_args_2903_;
v_isShared_2933_ = v_isSharedCheck_3572_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_head_2930_);
lean_dec(v_args_2903_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_3572_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v_head_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_3570_; 
v_head_2934_ = lean_ctor_get(v_tail_2928_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v_tail_2928_);
if (v_isSharedCheck_3570_ == 0)
{
lean_object* v_unused_3571_; 
v_unused_3571_ = lean_ctor_get(v_tail_2928_, 1);
lean_dec(v_unused_3571_);
v___x_2936_ = v_tail_2928_;
v_isShared_2937_ = v_isSharedCheck_3570_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_head_2934_);
lean_dec(v_tail_2928_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_3570_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v_head_2938_; lean_object* v_tail_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_3569_; 
v_head_2938_ = lean_ctor_get(v_tail_2929_, 0);
v_tail_2939_ = lean_ctor_get(v_tail_2929_, 1);
v_isSharedCheck_3569_ = !lean_is_exclusive(v_tail_2929_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_2941_ = v_tail_2929_;
v_isShared_2942_ = v_isSharedCheck_3569_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_tail_2939_);
lean_inc(v_head_2938_);
lean_dec(v_tail_2929_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_3569_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2943_; 
v___x_2943_ = l_Lean_ModuleSetup_load(v_head_2930_);
lean_dec(v_head_2930_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v_a_2944_; lean_object* v_name_2945_; lean_object* v_importArts_2946_; lean_object* v_options_2947_; uint8_t v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2952_; 
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
lean_inc(v_a_2944_);
lean_dec_ref_known(v___x_2943_, 1);
v_name_2945_ = lean_ctor_get(v_a_2944_, 0);
lean_inc(v_name_2945_);
v_importArts_2946_ = lean_ctor_get(v_a_2944_, 3);
lean_inc(v_importArts_2946_);
v_options_2947_ = lean_ctor_get(v_a_2944_, 6);
lean_inc(v_options_2947_);
lean_dec(v_a_2944_);
v___x_2948_ = 0;
v___x_2949_ = l_Lean_LeanOptions_toOptions(v_options_2947_);
v___x_2950_ = lean_box(v___x_2948_);
if (v_isShared_2942_ == 0)
{
lean_ctor_set_tag(v___x_2941_, 0);
lean_ctor_set(v___x_2941_, 1, v___x_2949_);
lean_ctor_set(v___x_2941_, 0, v___x_2950_);
v___x_2952_ = v___x_2941_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v___x_2950_);
lean_ctor_set(v_reuseFailAlloc_3560_, 1, v___x_2949_);
v___x_2952_ = v_reuseFailAlloc_3560_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
lean_object* v___x_2953_; 
v___x_2953_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_tail_2939_, v___x_2952_);
lean_dec(v_tail_2939_);
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_object* v_a_2954_; lean_object* v___x_2955_; 
v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
lean_inc(v_a_2954_);
lean_dec_ref_known(v___x_2953_, 1);
v___x_2955_ = lean_init_search_path();
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_fst_2956_; lean_object* v_snd_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_3543_; 
lean_dec_ref_known(v___x_2955_, 1);
v_fst_2956_ = lean_ctor_get(v_a_2954_, 0);
v_snd_2957_ = lean_ctor_get(v_a_2954_, 1);
v_isSharedCheck_3543_ = !lean_is_exclusive(v_a_2954_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_2959_ = v_a_2954_;
v_isShared_2960_ = v_isSharedCheck_3543_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_snd_2957_);
lean_inc(v_fst_2956_);
lean_dec(v_a_2954_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_3543_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; uint8_t v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___y_2977_; lean_object* v___y_2978_; uint8_t v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_3130_; lean_object* v___y_3131_; uint8_t v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v_nextMacroScope_3148_; lean_object* v_ngen_3149_; lean_object* v_auxDeclNGen_3150_; lean_object* v_traceState_3151_; lean_object* v_messages_3152_; lean_object* v_infoState_3153_; lean_object* v_snapshotTasks_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3173_; lean_object* v___y_3174_; uint8_t v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; uint8_t v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3240_; lean_object* v___y_3241_; uint8_t v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; uint8_t v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; uint8_t v___y_3263_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; uint8_t v___x_3288_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v___y_3435_; lean_object* v___y_3436_; uint8_t v___x_3446_; uint8_t v___y_3448_; uint8_t v___x_3542_; 
v___x_2961_ = lean_obj_once(&l_main___closed__3, &l_main___closed__3_once, _init_l_main___closed__3);
v___x_2962_ = lean_box(0);
v___x_2963_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_2964_ = lean_obj_once(&l_main___closed__5, &l_main___closed__5_once, _init_l_main___closed__5);
v___x_2965_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_2966_ = lean_obj_once(&l_main___closed__8, &l_main___closed__8_once, _init_l_main___closed__8);
v___x_2967_ = lean_obj_once(&l_main___closed__9, &l_main___closed__9_once, _init_l_main___closed__9);
v___x_2968_ = lean_box(1);
v___x_2969_ = ((lean_object*)(l_main___closed__10));
v___x_2970_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_2971_ = 1;
v___x_2972_ = l_Lean_Option_set___at___00Lean_Environment_realizeConst_spec__0(v_snd_2957_, v___x_2970_, v___x_2971_);
v___x_2973_ = l_Lean_maxHeartbeats;
v___x_2974_ = lean_unsigned_to_nat(0u);
v___x_2975_ = l_Lean_Option_set___at___00main_spec__3(v___x_2972_, v___x_2973_, v___x_2974_);
v___x_3283_ = ((lean_object*)(l_main___closed__21));
lean_inc(v_name_2945_);
v___x_3284_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_3284_, 0, v_name_2945_);
lean_ctor_set_uint8(v___x_3284_, sizeof(void*)*1, v___x_2971_);
lean_ctor_set_uint8(v___x_3284_, sizeof(void*)*1 + 1, v___x_2971_);
lean_ctor_set_uint8(v___x_3284_, sizeof(void*)*1 + 2, v___x_2948_);
v___x_3285_ = lean_unsigned_to_nat(1u);
v___x_3286_ = lean_mk_empty_array_with_capacity(v___x_3285_);
v___x_3287_ = lean_array_push(v___x_3286_, v___x_3284_);
v___x_3288_ = 0;
v___x_3446_ = 2;
v___x_3542_ = lean_uint8_once(&l_main___closed__37, &l_main___closed__37_once, _init_l_main___closed__37);
if (v___x_3542_ == 0)
{
v___y_3448_ = v___x_2971_;
goto v___jp_3447_;
}
else
{
v___y_3448_ = v___x_2948_;
goto v___jp_3447_;
}
v___jp_2976_:
{
lean_object* v___x_2996_; lean_object* v_messages_2997_; lean_object* v_env_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3121_; 
v___x_2996_ = lean_st_ref_get(v___y_2993_);
lean_dec(v___y_2993_);
v_messages_2997_ = lean_ctor_get(v___x_2996_, 6);
v_env_2998_ = lean_ctor_get(v___x_2996_, 0);
v_isSharedCheck_3121_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3121_ == 0)
{
lean_object* v_unused_3122_; lean_object* v_unused_3123_; lean_object* v_unused_3124_; lean_object* v_unused_3125_; lean_object* v_unused_3126_; lean_object* v_unused_3127_; lean_object* v_unused_3128_; 
v_unused_3122_ = lean_ctor_get(v___x_2996_, 8);
lean_dec(v_unused_3122_);
v_unused_3123_ = lean_ctor_get(v___x_2996_, 7);
lean_dec(v_unused_3123_);
v_unused_3124_ = lean_ctor_get(v___x_2996_, 5);
lean_dec(v_unused_3124_);
v_unused_3125_ = lean_ctor_get(v___x_2996_, 4);
lean_dec(v_unused_3125_);
v_unused_3126_ = lean_ctor_get(v___x_2996_, 3);
lean_dec(v_unused_3126_);
v_unused_3127_ = lean_ctor_get(v___x_2996_, 2);
lean_dec(v_unused_3127_);
v_unused_3128_ = lean_ctor_get(v___x_2996_, 1);
lean_dec(v_unused_3128_);
v___x_3000_ = v___x_2996_;
v_isShared_3001_ = v_isSharedCheck_3121_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_messages_2997_);
lean_inc(v_env_2998_);
lean_dec(v___x_2996_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3121_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v_unreported_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v_unreported_3002_ = lean_ctor_get(v_messages_2997_, 1);
v___x_3003_ = lean_box(0);
v___x_3004_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_unreported_3002_, v___x_3003_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3111_; 
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3111_ == 0)
{
lean_object* v_unused_3112_; 
v_unused_3112_ = lean_ctor_get(v___x_3004_, 0);
lean_dec(v_unused_3112_);
v___x_3006_ = v___x_3004_;
v_isShared_3007_ = v_isSharedCheck_3111_;
goto v_resetjp_3005_;
}
else
{
lean_dec(v___x_3004_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3111_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
uint8_t v___x_3008_; 
v___x_3008_ = l_Lean_MessageLog_hasErrors(v_messages_2997_);
lean_dec_ref(v_messages_2997_);
if (v___x_3008_ == 0)
{
lean_object* v___x_3009_; 
lean_del_object(v___x_3006_);
lean_inc_ref(v_env_2998_);
v___x_3009_ = l___private_LeanIR_0__mkIRSigData(v_env_2998_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; lean_object* v___x_3011_; 
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_a_3010_);
lean_dec_ref_known(v___x_3009_, 1);
lean_inc_ref(v_env_2998_);
v___x_3011_ = l___private_LeanIR_0__mkIRData(v_env_2998_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v_a_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3019_; 
v_a_3012_ = lean_ctor_get(v___x_3011_, 0);
lean_inc(v_a_3012_);
lean_dec_ref_known(v___x_3011_, 1);
v___x_3013_ = ((lean_object*)(l_main___closed__11));
lean_inc(v_head_2934_);
v___x_3014_ = l_System_FilePath_addExtension(v_head_2934_, v___x_3013_);
v___x_3015_ = l_Lean_Environment_mainModule(v_env_2998_);
v___x_3016_ = ((lean_object*)(l_main___closed__13));
v___x_3017_ = l_Lean_Name_append(v___x_3015_, v___x_3016_);
if (v_isShared_2960_ == 0)
{
lean_ctor_set(v___x_2959_, 1, v_a_3010_);
lean_ctor_set(v___x_2959_, 0, v___x_3014_);
v___x_3019_ = v___x_2959_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v___x_3014_);
lean_ctor_set(v_reuseFailAlloc_3090_, 1, v_a_3010_);
v___x_3019_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
lean_object* v___x_3021_; 
lean_inc(v_head_2934_);
if (v_isShared_2937_ == 0)
{
lean_ctor_set_tag(v___x_2936_, 0);
lean_ctor_set(v___x_2936_, 1, v_a_3012_);
v___x_3021_ = v___x_2936_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_head_2934_);
lean_ctor_set(v_reuseFailAlloc_3089_, 1, v_a_3012_);
v___x_3021_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3022_ = lean_unsigned_to_nat(2u);
v___x_3023_ = lean_mk_empty_array_with_capacity(v___x_3022_);
v___x_3024_ = lean_array_push(v___x_3023_, v___x_3019_);
v___x_3025_ = lean_array_push(v___x_3024_, v___x_3021_);
v___x_3026_ = l_Lean_saveModuleDataParts(v___x_3017_, v___x_3025_);
lean_dec_ref(v___x_3025_);
lean_dec(v___x_3017_);
if (lean_obj_tag(v___x_3026_) == 0)
{
uint8_t v___x_3027_; lean_object* v___x_3028_; 
lean_dec_ref_known(v___x_3026_, 1);
v___x_3027_ = 1;
v___x_3028_ = lean_io_prim_handle_mk(v_head_2938_, v___x_3027_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_object* v_a_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3034_; 
lean_dec(v_head_2938_);
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
lean_inc(v_a_3029_);
lean_dec_ref_known(v___x_3028_, 1);
v___x_3030_ = ((lean_object*)(l_main___closed__14));
v___x_3031_ = l_Lean_Options_empty;
v___x_3032_ = lean_obj_once(&l_main___closed__15, &l_main___closed__15_once, _init_l_main___closed__15);
lean_inc_ref(v___y_2991_);
lean_inc_ref(v___y_2987_);
lean_inc_ref(v___y_2992_);
lean_inc_ref(v___y_2990_);
lean_inc_ref(v___y_2986_);
lean_inc_ref(v___y_2994_);
lean_inc(v___y_2989_);
lean_inc_ref(v_env_2998_);
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 8, v___y_2991_);
lean_ctor_set(v___x_3000_, 7, v___y_2987_);
lean_ctor_set(v___x_3000_, 6, v___y_2992_);
lean_ctor_set(v___x_3000_, 5, v___y_2990_);
lean_ctor_set(v___x_3000_, 4, v___y_2986_);
lean_ctor_set(v___x_3000_, 3, v___y_2988_);
lean_ctor_set(v___x_3000_, 2, v___y_2994_);
lean_ctor_set(v___x_3000_, 1, v___y_2989_);
v___x_3034_ = v___x_3000_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_env_2998_);
lean_ctor_set(v_reuseFailAlloc_3058_, 1, v___y_2989_);
lean_ctor_set(v_reuseFailAlloc_3058_, 2, v___y_2994_);
lean_ctor_set(v_reuseFailAlloc_3058_, 3, v___y_2988_);
lean_ctor_set(v_reuseFailAlloc_3058_, 4, v___y_2986_);
lean_ctor_set(v_reuseFailAlloc_3058_, 5, v___y_2990_);
lean_ctor_set(v_reuseFailAlloc_3058_, 6, v___y_2992_);
lean_ctor_set(v_reuseFailAlloc_3058_, 7, v___y_2987_);
lean_ctor_set(v_reuseFailAlloc_3058_, 8, v___y_2991_);
v___x_3034_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___f_3037_; lean_object* v___x_3038_; 
v___x_3035_ = lean_box(v___y_2979_);
v___x_3036_ = lean_box(v___x_2948_);
lean_inc(v___y_2981_);
lean_inc(v___y_2982_);
lean_inc(v___y_2983_);
lean_inc_ref(v___y_2978_);
lean_inc(v___y_2980_);
lean_inc_ref(v___y_2977_);
lean_inc(v___y_2985_);
v___f_3037_ = lean_alloc_closure((void*)(l_main___lam__1___boxed), 18, 17);
lean_closure_set(v___f_3037_, 0, v___x_3034_);
lean_closure_set(v___f_3037_, 1, v___y_2985_);
lean_closure_set(v___f_3037_, 2, v_head_2934_);
lean_closure_set(v___f_3037_, 3, v___y_2977_);
lean_closure_set(v___f_3037_, 4, v___y_2984_);
lean_closure_set(v___f_3037_, 5, v___y_2980_);
lean_closure_set(v___f_3037_, 6, v___x_3031_);
lean_closure_set(v___f_3037_, 7, v_name_2945_);
lean_closure_set(v___f_3037_, 8, v_a_3029_);
lean_closure_set(v___f_3037_, 9, v___x_3035_);
lean_closure_set(v___f_3037_, 10, v___y_2978_);
lean_closure_set(v___f_3037_, 11, v___x_2974_);
lean_closure_set(v___f_3037_, 12, v___y_2983_);
lean_closure_set(v___f_3037_, 13, v___y_2982_);
lean_closure_set(v___f_3037_, 14, v___x_3032_);
lean_closure_set(v___f_3037_, 15, v___y_2981_);
lean_closure_set(v___f_3037_, 16, v___x_3036_);
v___x_3038_ = l_Lean_profileitIOUnsafe___redArg(v___x_3030_, v___x_2975_, v___f_3037_, v___y_2995_);
lean_dec_ref(v___x_2975_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v___x_3039_; uint8_t v___x_3040_; 
lean_dec_ref_known(v___x_3038_, 1);
v___x_3039_ = lean_display_cumulative_profiling_times();
v___x_3040_ = lean_unbox(v_fst_2956_);
lean_dec(v_fst_2956_);
if (v___x_3040_ == 0)
{
lean_dec_ref(v_env_2998_);
goto v___jp_2925_;
}
else
{
lean_object* v___x_3041_; 
v___x_3041_ = l_Lean_Environment_displayStats(v_env_2998_);
if (lean_obj_tag(v___x_3041_) == 0)
{
lean_dec_ref_known(v___x_3041_, 1);
goto v___jp_2925_;
}
else
{
lean_object* v_a_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3049_; 
v_a_3042_ = lean_ctor_get(v___x_3041_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3044_ = v___x_3041_;
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_dec(v___x_3041_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3047_; 
if (v_isShared_3045_ == 0)
{
v___x_3047_ = v___x_3044_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_a_3042_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
}
}
else
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3057_; 
lean_dec_ref(v_env_2998_);
lean_dec(v_fst_2956_);
v_a_3050_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3052_ = v___x_3038_;
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_3038_);
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
}
else
{
lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
lean_dec_ref_known(v___x_3028_, 1);
lean_del_object(v___x_3000_);
lean_dec_ref(v_env_2998_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2988_);
lean_dec(v___y_2984_);
lean_dec_ref(v___x_2975_);
lean_dec(v_fst_2956_);
lean_dec(v_name_2945_);
lean_dec(v_head_2934_);
v___x_3059_ = ((lean_object*)(l_main___closed__16));
v___x_3060_ = lean_string_append(v___x_3059_, v_head_2938_);
lean_dec(v_head_2938_);
v___x_3061_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__1));
v___x_3062_ = lean_string_append(v___x_3060_, v___x_3061_);
v___x_3063_ = l_IO_eprintln___at___00main_spec__6(v___x_3062_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3071_; 
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3071_ == 0)
{
lean_object* v_unused_3072_; 
v_unused_3072_ = lean_ctor_get(v___x_3063_, 0);
lean_dec(v_unused_3072_);
v___x_3065_ = v___x_3063_;
v_isShared_3066_ = v_isSharedCheck_3071_;
goto v_resetjp_3064_;
}
else
{
lean_dec(v___x_3063_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3071_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3067_; lean_object* v___x_3069_; 
v___x_3067_ = l_main___boxed__const__1;
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 0, v___x_3067_);
v___x_3069_ = v___x_3065_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v___x_3067_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
else
{
lean_object* v_a_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3080_; 
v_a_3073_ = lean_ctor_get(v___x_3063_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3075_ = v___x_3063_;
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_a_3073_);
lean_dec(v___x_3063_);
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
}
else
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3088_; 
lean_del_object(v___x_3000_);
lean_dec_ref(v_env_2998_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2988_);
lean_dec(v___y_2984_);
lean_dec_ref(v___x_2975_);
lean_dec(v_fst_2956_);
lean_dec(v_name_2945_);
lean_dec(v_head_2938_);
lean_dec(v_head_2934_);
v_a_3081_ = lean_ctor_get(v___x_3026_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3083_ = v___x_3026_;
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3026_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3086_; 
if (v_isShared_3084_ == 0)
{
v___x_3086_ = v___x_3083_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_a_3081_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
}
}
}
}
}
}
else
{
lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3098_; 
lean_dec(v_a_3010_);
lean_del_object(v___x_3000_);
lean_dec_ref(v_env_2998_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2988_);
lean_dec(v___y_2984_);
lean_dec_ref(v___x_2975_);
lean_del_object(v___x_2959_);
lean_dec(v_fst_2956_);
lean_dec(v_name_2945_);
lean_dec(v_head_2938_);
lean_del_object(v___x_2936_);
lean_dec(v_head_2934_);
v_a_3091_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3093_ = v___x_3011_;
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_3011_);
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
else
{
lean_object* v_a_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3106_; 
lean_del_object(v___x_3000_);
lean_dec_ref(v_env_2998_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2988_);
lean_dec(v___y_2984_);
lean_dec_ref(v___x_2975_);
lean_del_object(v___x_2959_);
lean_dec(v_fst_2956_);
lean_dec(v_name_2945_);
lean_dec(v_head_2938_);
lean_del_object(v___x_2936_);
lean_dec(v_head_2934_);
v_a_3099_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3101_ = v___x_3009_;
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_a_3099_);
lean_dec(v___x_3009_);
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
else
{
lean_object* v___x_3107_; lean_object* v___x_3109_; 
lean_del_object(v___x_3000_);
lean_dec_ref(v_env_2998_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2988_);
lean_dec(v___y_2984_);
lean_dec_ref(v___x_2975_);
lean_del_object(v___x_2959_);
lean_dec(v_fst_2956_);
lean_dec(v_name_2945_);
lean_dec(v_head_2938_);
lean_del_object(v___x_2936_);
lean_dec(v_head_2934_);
v___x_3107_ = l_main___boxed__const__1;
if (v_isShared_3007_ == 0)
{
lean_ctor_set(v___x_3006_, 0, v___x_3107_);
v___x_3109_ = v___x_3006_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v___x_3107_);
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
lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3120_; 
lean_del_object(v___x_3000_);
lean_dec_ref(v_env_2998_);
lean_dec_ref(v_messages_2997_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2988_);
lean_dec(v___y_2984_);
lean_dec_ref(v___x_2975_);
lean_del_object(v___x_2959_);
lean_dec(v_fst_2956_);
lean_dec(v_name_2945_);
lean_dec(v_head_2938_);
lean_del_object(v___x_2936_);
lean_dec(v_head_2934_);
v_a_3113_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3115_ = v___x_3004_;
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3004_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3118_; 
if (v_isShared_3116_ == 0)
{
v___x_3118_ = v___x_3115_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_a_3113_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
}
}
v___jp_3129_:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; size_t v_sz_3163_; size_t v___x_3164_; lean_object* v___x_3165_; 
lean_inc_ref(v___y_3147_);
v___x_3160_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3160_, 0, v___y_3159_);
lean_ctor_set(v___x_3160_, 1, v_nextMacroScope_3148_);
lean_ctor_set(v___x_3160_, 2, v_ngen_3149_);
lean_ctor_set(v___x_3160_, 3, v_auxDeclNGen_3150_);
lean_ctor_set(v___x_3160_, 4, v_traceState_3151_);
lean_ctor_set(v___x_3160_, 5, v___y_3147_);
lean_ctor_set(v___x_3160_, 6, v_messages_3152_);
lean_ctor_set(v___x_3160_, 7, v_infoState_3153_);
lean_ctor_set(v___x_3160_, 8, v_snapshotTasks_3154_);
v___x_3161_ = lean_st_ref_put(v___y_3144_, v___x_3160_);
v___x_3162_ = lean_box(0);
v_sz_3163_ = lean_array_size(v___y_3142_);
v___x_3164_ = ((size_t)0ULL);
v___x_3165_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(v___y_3142_, v_sz_3163_, v___x_3164_, v___x_3162_, v___y_3140_, v___y_3144_);
lean_dec_ref(v___y_3142_);
if (lean_obj_tag(v___x_3165_) == 0)
{
lean_dec_ref_known(v___x_3165_, 1);
lean_dec(v___y_3144_);
lean_dec_ref(v___y_3140_);
v___y_2977_ = v___y_3130_;
v___y_2978_ = v___y_3131_;
v___y_2979_ = v___y_3132_;
v___y_2980_ = v___y_3133_;
v___y_2981_ = v___y_3134_;
v___y_2982_ = v___y_3135_;
v___y_2983_ = v___y_3138_;
v___y_2984_ = v___y_3137_;
v___y_2985_ = v___y_3136_;
v___y_2986_ = v___y_3143_;
v___y_2987_ = v___y_3139_;
v___y_2988_ = v___y_3145_;
v___y_2989_ = v___y_3146_;
v___y_2990_ = v___y_3147_;
v___y_2991_ = v___y_3155_;
v___y_2992_ = v___y_3156_;
v___y_2993_ = v___y_3157_;
v___y_2994_ = v___y_3141_;
v___y_2995_ = v___y_3158_;
goto v___jp_2976_;
}
else
{
if (lean_obj_tag(v___x_3165_) == 0)
{
lean_dec_ref_known(v___x_3165_, 1);
lean_dec(v___y_3144_);
lean_dec_ref(v___y_3140_);
v___y_2977_ = v___y_3130_;
v___y_2978_ = v___y_3131_;
v___y_2979_ = v___y_3132_;
v___y_2980_ = v___y_3133_;
v___y_2981_ = v___y_3134_;
v___y_2982_ = v___y_3135_;
v___y_2983_ = v___y_3138_;
v___y_2984_ = v___y_3137_;
v___y_2985_ = v___y_3136_;
v___y_2986_ = v___y_3143_;
v___y_2987_ = v___y_3139_;
v___y_2988_ = v___y_3145_;
v___y_2989_ = v___y_3146_;
v___y_2990_ = v___y_3147_;
v___y_2991_ = v___y_3155_;
v___y_2992_ = v___y_3156_;
v___y_2993_ = v___y_3157_;
v___y_2994_ = v___y_3141_;
v___y_2995_ = v___y_3158_;
goto v___jp_2976_;
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
v___x_3169_ = l_Lean_logError___at___00main_spec__14(v___x_3168_, v___y_3140_, v___y_3144_);
lean_dec(v___y_3144_);
lean_dec_ref(v___y_3140_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_dec_ref_known(v___x_3169_, 1);
v___y_2977_ = v___y_3130_;
v___y_2978_ = v___y_3131_;
v___y_2979_ = v___y_3132_;
v___y_2980_ = v___y_3133_;
v___y_2981_ = v___y_3134_;
v___y_2982_ = v___y_3135_;
v___y_2983_ = v___y_3138_;
v___y_2984_ = v___y_3137_;
v___y_2985_ = v___y_3136_;
v___y_2986_ = v___y_3143_;
v___y_2987_ = v___y_3139_;
v___y_2988_ = v___y_3145_;
v___y_2989_ = v___y_3146_;
v___y_2990_ = v___y_3147_;
v___y_2991_ = v___y_3155_;
v___y_2992_ = v___y_3156_;
v___y_2993_ = v___y_3157_;
v___y_2994_ = v___y_3141_;
v___y_2995_ = v___y_3158_;
goto v___jp_2976_;
}
else
{
lean_object* v___x_3170_; lean_object* v___x_3171_; 
lean_dec_ref_known(v___x_3169_, 1);
lean_dec(v___y_3158_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3145_);
lean_dec(v___y_3137_);
lean_dec_ref(v___x_2975_);
lean_del_object(v___x_2959_);
lean_dec(v_fst_2956_);
lean_dec(v_name_2945_);
lean_dec(v_head_2938_);
lean_del_object(v___x_2936_);
lean_dec(v_head_2934_);
v___x_3170_ = lean_obj_once(&l_main___closed__20, &l_main___closed__20_once, _init_l_main___closed__20);
v___x_3171_ = l_panic___at___00main_spec__5(v___x_3170_);
return v___x_3171_;
}
}
else
{
lean_dec(v_a_3166_);
lean_dec(v___y_3144_);
lean_dec_ref(v___y_3140_);
v___y_2977_ = v___y_3130_;
v___y_2978_ = v___y_3131_;
v___y_2979_ = v___y_3132_;
v___y_2980_ = v___y_3133_;
v___y_2981_ = v___y_3134_;
v___y_2982_ = v___y_3135_;
v___y_2983_ = v___y_3138_;
v___y_2984_ = v___y_3137_;
v___y_2985_ = v___y_3136_;
v___y_2986_ = v___y_3143_;
v___y_2987_ = v___y_3139_;
v___y_2988_ = v___y_3145_;
v___y_2989_ = v___y_3146_;
v___y_2990_ = v___y_3147_;
v___y_2991_ = v___y_3155_;
v___y_2992_ = v___y_3156_;
v___y_2993_ = v___y_3157_;
v___y_2994_ = v___y_3141_;
v___y_2995_ = v___y_3158_;
goto v___jp_2976_;
}
}
}
}
v___jp_3172_:
{
lean_object* v___x_3197_; lean_object* v_toCold_3198_; lean_object* v_currRecDepth_3199_; lean_object* v_ref_3200_; lean_object* v_currNamespace_3201_; lean_object* v_openDecls_3202_; lean_object* v_initHeartbeats_3203_; lean_object* v_maxHeartbeats_3204_; lean_object* v_currMacroScope_3205_; uint8_t v_suppressElabErrors_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3236_; 
v___x_3197_ = lean_st_ref_take(v___y_3196_);
v_toCold_3198_ = lean_ctor_get(v___y_3195_, 0);
v_currRecDepth_3199_ = lean_ctor_get(v___y_3195_, 2);
v_ref_3200_ = lean_ctor_get(v___y_3195_, 4);
v_currNamespace_3201_ = lean_ctor_get(v___y_3195_, 5);
v_openDecls_3202_ = lean_ctor_get(v___y_3195_, 6);
v_initHeartbeats_3203_ = lean_ctor_get(v___y_3195_, 7);
v_maxHeartbeats_3204_ = lean_ctor_get(v___y_3195_, 8);
v_currMacroScope_3205_ = lean_ctor_get(v___y_3195_, 9);
v_suppressElabErrors_3206_ = lean_ctor_get_uint8(v___y_3195_, sizeof(void*)*10 + 1);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___y_3195_);
if (v_isSharedCheck_3236_ == 0)
{
lean_object* v_unused_3237_; lean_object* v_unused_3238_; 
v_unused_3237_ = lean_ctor_get(v___y_3195_, 3);
lean_dec(v_unused_3237_);
v_unused_3238_ = lean_ctor_get(v___y_3195_, 1);
lean_dec(v_unused_3238_);
v___x_3208_ = v___y_3195_;
v_isShared_3209_ = v_isSharedCheck_3236_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_currMacroScope_3205_);
lean_inc(v_maxHeartbeats_3204_);
lean_inc(v_initHeartbeats_3203_);
lean_inc(v_openDecls_3202_);
lean_inc(v_currNamespace_3201_);
lean_inc(v_ref_3200_);
lean_inc(v_currRecDepth_3199_);
lean_inc(v_toCold_3198_);
lean_dec(v___y_3195_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3236_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v_env_3210_; lean_object* v_nextMacroScope_3211_; lean_object* v_ngen_3212_; lean_object* v_auxDeclNGen_3213_; lean_object* v_traceState_3214_; lean_object* v_messages_3215_; lean_object* v_infoState_3216_; lean_object* v_snapshotTasks_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3221_; 
v_env_3210_ = lean_ctor_get(v___x_3197_, 0);
lean_inc_ref(v_env_3210_);
v_nextMacroScope_3211_ = lean_ctor_get(v___x_3197_, 1);
lean_inc(v_nextMacroScope_3211_);
v_ngen_3212_ = lean_ctor_get(v___x_3197_, 2);
lean_inc_ref(v_ngen_3212_);
v_auxDeclNGen_3213_ = lean_ctor_get(v___x_3197_, 3);
lean_inc_ref(v_auxDeclNGen_3213_);
v_traceState_3214_ = lean_ctor_get(v___x_3197_, 4);
lean_inc_ref(v_traceState_3214_);
v_messages_3215_ = lean_ctor_get(v___x_3197_, 6);
lean_inc_ref(v_messages_3215_);
v_infoState_3216_ = lean_ctor_get(v___x_3197_, 7);
lean_inc_ref(v_infoState_3216_);
v_snapshotTasks_3217_ = lean_ctor_get(v___x_3197_, 8);
lean_inc_ref(v_snapshotTasks_3217_);
lean_dec(v___x_3197_);
v___x_3218_ = l_Lean_maxRecDepth;
v___x_3219_ = l_Lean_Option_get___at___00main_spec__9(v___x_2975_, v___x_3218_);
lean_inc_ref(v___x_2975_);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 3, v___x_3219_);
lean_ctor_set(v___x_3208_, 1, v___x_2975_);
v___x_3221_ = v___x_3208_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_toCold_3198_);
lean_ctor_set(v_reuseFailAlloc_3235_, 1, v___x_2975_);
lean_ctor_set(v_reuseFailAlloc_3235_, 2, v_currRecDepth_3199_);
lean_ctor_set(v_reuseFailAlloc_3235_, 3, v___x_3219_);
lean_ctor_set(v_reuseFailAlloc_3235_, 4, v_ref_3200_);
lean_ctor_set(v_reuseFailAlloc_3235_, 5, v_currNamespace_3201_);
lean_ctor_set(v_reuseFailAlloc_3235_, 6, v_openDecls_3202_);
lean_ctor_set(v_reuseFailAlloc_3235_, 7, v_initHeartbeats_3203_);
lean_ctor_set(v_reuseFailAlloc_3235_, 8, v_maxHeartbeats_3204_);
lean_ctor_set(v_reuseFailAlloc_3235_, 9, v_currMacroScope_3205_);
lean_ctor_set_uint8(v_reuseFailAlloc_3235_, sizeof(void*)*10 + 1, v_suppressElabErrors_3206_);
v___x_3221_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
lean_object* v___x_3222_; uint8_t v___x_3223_; 
lean_ctor_set_uint8(v___x_3221_, sizeof(void*)*10, v___y_3183_);
v___x_3222_ = lean_array_get_size(v___y_3185_);
v___x_3223_ = lean_nat_dec_lt(v___x_2974_, v___x_3222_);
if (v___x_3223_ == 0)
{
lean_object* v___x_3224_; 
lean_inc_ref(v___y_3190_);
v___x_3224_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3190_, v_env_3210_, v___x_2968_);
v___y_3130_ = v___y_3173_;
v___y_3131_ = v___y_3174_;
v___y_3132_ = v___y_3175_;
v___y_3133_ = v___y_3176_;
v___y_3134_ = v___y_3177_;
v___y_3135_ = v___y_3178_;
v___y_3136_ = v___y_3181_;
v___y_3137_ = v___y_3180_;
v___y_3138_ = v___y_3179_;
v___y_3139_ = v___y_3182_;
v___y_3140_ = v___x_3221_;
v___y_3141_ = v___y_3184_;
v___y_3142_ = v___y_3185_;
v___y_3143_ = v___y_3186_;
v___y_3144_ = v___y_3196_;
v___y_3145_ = v___y_3187_;
v___y_3146_ = v___y_3188_;
v___y_3147_ = v___y_3189_;
v_nextMacroScope_3148_ = v_nextMacroScope_3211_;
v_ngen_3149_ = v_ngen_3212_;
v_auxDeclNGen_3150_ = v_auxDeclNGen_3213_;
v_traceState_3151_ = v_traceState_3214_;
v_messages_3152_ = v_messages_3215_;
v_infoState_3153_ = v_infoState_3216_;
v_snapshotTasks_3154_ = v_snapshotTasks_3217_;
v___y_3155_ = v___y_3191_;
v___y_3156_ = v___y_3192_;
v___y_3157_ = v___y_3193_;
v___y_3158_ = v___y_3194_;
v___y_3159_ = v___x_3224_;
goto v___jp_3129_;
}
else
{
uint8_t v___x_3225_; 
v___x_3225_ = lean_nat_dec_le(v___x_3222_, v___x_3222_);
if (v___x_3225_ == 0)
{
if (v___x_3223_ == 0)
{
lean_object* v___x_3226_; 
lean_inc_ref(v___y_3190_);
v___x_3226_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3190_, v_env_3210_, v___x_2968_);
v___y_3130_ = v___y_3173_;
v___y_3131_ = v___y_3174_;
v___y_3132_ = v___y_3175_;
v___y_3133_ = v___y_3176_;
v___y_3134_ = v___y_3177_;
v___y_3135_ = v___y_3178_;
v___y_3136_ = v___y_3181_;
v___y_3137_ = v___y_3180_;
v___y_3138_ = v___y_3179_;
v___y_3139_ = v___y_3182_;
v___y_3140_ = v___x_3221_;
v___y_3141_ = v___y_3184_;
v___y_3142_ = v___y_3185_;
v___y_3143_ = v___y_3186_;
v___y_3144_ = v___y_3196_;
v___y_3145_ = v___y_3187_;
v___y_3146_ = v___y_3188_;
v___y_3147_ = v___y_3189_;
v_nextMacroScope_3148_ = v_nextMacroScope_3211_;
v_ngen_3149_ = v_ngen_3212_;
v_auxDeclNGen_3150_ = v_auxDeclNGen_3213_;
v_traceState_3151_ = v_traceState_3214_;
v_messages_3152_ = v_messages_3215_;
v_infoState_3153_ = v_infoState_3216_;
v_snapshotTasks_3154_ = v_snapshotTasks_3217_;
v___y_3155_ = v___y_3191_;
v___y_3156_ = v___y_3192_;
v___y_3157_ = v___y_3193_;
v___y_3158_ = v___y_3194_;
v___y_3159_ = v___x_3226_;
goto v___jp_3129_;
}
else
{
size_t v___x_3227_; size_t v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; 
v___x_3227_ = ((size_t)0ULL);
v___x_3228_ = lean_usize_of_nat(v___x_3222_);
v___x_3229_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3185_, v___x_3227_, v___x_3228_, v___x_2968_);
lean_inc_ref(v___y_3190_);
v___x_3230_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3190_, v_env_3210_, v___x_3229_);
v___y_3130_ = v___y_3173_;
v___y_3131_ = v___y_3174_;
v___y_3132_ = v___y_3175_;
v___y_3133_ = v___y_3176_;
v___y_3134_ = v___y_3177_;
v___y_3135_ = v___y_3178_;
v___y_3136_ = v___y_3181_;
v___y_3137_ = v___y_3180_;
v___y_3138_ = v___y_3179_;
v___y_3139_ = v___y_3182_;
v___y_3140_ = v___x_3221_;
v___y_3141_ = v___y_3184_;
v___y_3142_ = v___y_3185_;
v___y_3143_ = v___y_3186_;
v___y_3144_ = v___y_3196_;
v___y_3145_ = v___y_3187_;
v___y_3146_ = v___y_3188_;
v___y_3147_ = v___y_3189_;
v_nextMacroScope_3148_ = v_nextMacroScope_3211_;
v_ngen_3149_ = v_ngen_3212_;
v_auxDeclNGen_3150_ = v_auxDeclNGen_3213_;
v_traceState_3151_ = v_traceState_3214_;
v_messages_3152_ = v_messages_3215_;
v_infoState_3153_ = v_infoState_3216_;
v_snapshotTasks_3154_ = v_snapshotTasks_3217_;
v___y_3155_ = v___y_3191_;
v___y_3156_ = v___y_3192_;
v___y_3157_ = v___y_3193_;
v___y_3158_ = v___y_3194_;
v___y_3159_ = v___x_3230_;
goto v___jp_3129_;
}
}
else
{
size_t v___x_3231_; size_t v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3231_ = ((size_t)0ULL);
v___x_3232_ = lean_usize_of_nat(v___x_3222_);
v___x_3233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3185_, v___x_3231_, v___x_3232_, v___x_2968_);
lean_inc_ref(v___y_3190_);
v___x_3234_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3190_, v_env_3210_, v___x_3233_);
v___y_3130_ = v___y_3173_;
v___y_3131_ = v___y_3174_;
v___y_3132_ = v___y_3175_;
v___y_3133_ = v___y_3176_;
v___y_3134_ = v___y_3177_;
v___y_3135_ = v___y_3178_;
v___y_3136_ = v___y_3181_;
v___y_3137_ = v___y_3180_;
v___y_3138_ = v___y_3179_;
v___y_3139_ = v___y_3182_;
v___y_3140_ = v___x_3221_;
v___y_3141_ = v___y_3184_;
v___y_3142_ = v___y_3185_;
v___y_3143_ = v___y_3186_;
v___y_3144_ = v___y_3196_;
v___y_3145_ = v___y_3187_;
v___y_3146_ = v___y_3188_;
v___y_3147_ = v___y_3189_;
v_nextMacroScope_3148_ = v_nextMacroScope_3211_;
v_ngen_3149_ = v_ngen_3212_;
v_auxDeclNGen_3150_ = v_auxDeclNGen_3213_;
v_traceState_3151_ = v_traceState_3214_;
v_messages_3152_ = v_messages_3215_;
v_infoState_3153_ = v_infoState_3216_;
v_snapshotTasks_3154_ = v_snapshotTasks_3217_;
v___y_3155_ = v___y_3191_;
v___y_3156_ = v___y_3192_;
v___y_3157_ = v___y_3193_;
v___y_3158_ = v___y_3194_;
v___y_3159_ = v___x_3234_;
goto v___jp_3129_;
}
}
}
}
}
v___jp_3239_:
{
if (v___y_3263_ == 0)
{
lean_object* v___x_3264_; lean_object* v_env_3265_; lean_object* v_nextMacroScope_3266_; lean_object* v_ngen_3267_; lean_object* v_auxDeclNGen_3268_; lean_object* v_traceState_3269_; lean_object* v_messages_3270_; lean_object* v_infoState_3271_; lean_object* v_snapshotTasks_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3281_; 
v___x_3264_ = lean_st_ref_take(v___y_3261_);
v_env_3265_ = lean_ctor_get(v___x_3264_, 0);
v_nextMacroScope_3266_ = lean_ctor_get(v___x_3264_, 1);
v_ngen_3267_ = lean_ctor_get(v___x_3264_, 2);
v_auxDeclNGen_3268_ = lean_ctor_get(v___x_3264_, 3);
v_traceState_3269_ = lean_ctor_get(v___x_3264_, 4);
v_messages_3270_ = lean_ctor_get(v___x_3264_, 6);
v_infoState_3271_ = lean_ctor_get(v___x_3264_, 7);
v_snapshotTasks_3272_ = lean_ctor_get(v___x_3264_, 8);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3264_);
if (v_isSharedCheck_3281_ == 0)
{
lean_object* v_unused_3282_; 
v_unused_3282_ = lean_ctor_get(v___x_3264_, 5);
lean_dec(v_unused_3282_);
v___x_3274_ = v___x_3264_;
v_isShared_3275_ = v_isSharedCheck_3281_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_snapshotTasks_3272_);
lean_inc(v_infoState_3271_);
lean_inc(v_messages_3270_);
lean_inc(v_traceState_3269_);
lean_inc(v_auxDeclNGen_3268_);
lean_inc(v_ngen_3267_);
lean_inc(v_nextMacroScope_3266_);
lean_inc(v_env_3265_);
lean_dec(v___x_3264_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3281_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3276_; lean_object* v___x_3278_; 
v___x_3276_ = l_Lean_Kernel_enableDiag(v_env_3265_, v___y_3250_);
lean_inc_ref(v___y_3257_);
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 5, v___y_3257_);
lean_ctor_set(v___x_3274_, 0, v___x_3276_);
v___x_3278_ = v___x_3274_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v___x_3276_);
lean_ctor_set(v_reuseFailAlloc_3280_, 1, v_nextMacroScope_3266_);
lean_ctor_set(v_reuseFailAlloc_3280_, 2, v_ngen_3267_);
lean_ctor_set(v_reuseFailAlloc_3280_, 3, v_auxDeclNGen_3268_);
lean_ctor_set(v_reuseFailAlloc_3280_, 4, v_traceState_3269_);
lean_ctor_set(v_reuseFailAlloc_3280_, 5, v___y_3257_);
lean_ctor_set(v_reuseFailAlloc_3280_, 6, v_messages_3270_);
lean_ctor_set(v_reuseFailAlloc_3280_, 7, v_infoState_3271_);
lean_ctor_set(v_reuseFailAlloc_3280_, 8, v_snapshotTasks_3272_);
v___x_3278_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
lean_object* v___x_3279_; 
v___x_3279_ = lean_st_ref_put(v___y_3261_, v___x_3278_);
lean_inc(v___y_3261_);
v___y_3173_ = v___y_3240_;
v___y_3174_ = v___y_3241_;
v___y_3175_ = v___y_3242_;
v___y_3176_ = v___y_3243_;
v___y_3177_ = v___y_3244_;
v___y_3178_ = v___y_3245_;
v___y_3179_ = v___y_3248_;
v___y_3180_ = v___y_3247_;
v___y_3181_ = v___y_3246_;
v___y_3182_ = v___y_3249_;
v___y_3183_ = v___y_3250_;
v___y_3184_ = v___y_3251_;
v___y_3185_ = v___y_3252_;
v___y_3186_ = v___y_3253_;
v___y_3187_ = v___y_3254_;
v___y_3188_ = v___y_3256_;
v___y_3189_ = v___y_3257_;
v___y_3190_ = v___y_3258_;
v___y_3191_ = v___y_3259_;
v___y_3192_ = v___y_3260_;
v___y_3193_ = v___y_3261_;
v___y_3194_ = v___y_3262_;
v___y_3195_ = v___y_3255_;
v___y_3196_ = v___y_3261_;
goto v___jp_3172_;
}
}
}
else
{
lean_inc(v___y_3261_);
v___y_3173_ = v___y_3240_;
v___y_3174_ = v___y_3241_;
v___y_3175_ = v___y_3242_;
v___y_3176_ = v___y_3243_;
v___y_3177_ = v___y_3244_;
v___y_3178_ = v___y_3245_;
v___y_3179_ = v___y_3248_;
v___y_3180_ = v___y_3247_;
v___y_3181_ = v___y_3246_;
v___y_3182_ = v___y_3249_;
v___y_3183_ = v___y_3250_;
v___y_3184_ = v___y_3251_;
v___y_3185_ = v___y_3252_;
v___y_3186_ = v___y_3253_;
v___y_3187_ = v___y_3254_;
v___y_3188_ = v___y_3256_;
v___y_3189_ = v___y_3257_;
v___y_3190_ = v___y_3258_;
v___y_3191_ = v___y_3259_;
v___y_3192_ = v___y_3260_;
v___y_3193_ = v___y_3261_;
v___y_3194_ = v___y_3262_;
v___y_3195_ = v___y_3255_;
v___y_3196_ = v___y_3261_;
goto v___jp_3172_;
}
}
v___jp_3289_:
{
lean_object* v___x_3298_; 
if (v_isShared_2933_ == 0)
{
lean_ctor_set_tag(v___x_2932_, 0);
lean_ctor_set(v___x_2932_, 1, v___y_3296_);
lean_ctor_set(v___x_2932_, 0, v___y_3291_);
v___x_3298_ = v___x_2932_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v___y_3291_);
lean_ctor_set(v_reuseFailAlloc_3394_, 1, v___y_3296_);
v___x_3298_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v_moduleData_3302_; lean_object* v___x_3303_; uint8_t v___x_3304_; 
v___x_3299_ = lean_box(0);
lean_inc_ref(v___y_3295_);
v___x_3300_ = l_Lean_EnvExtension_setState___redArg(v___y_3295_, v___y_3292_, v___x_3298_, v___x_3299_);
v___x_3301_ = l_Lean_Environment_header(v___x_3300_);
v_moduleData_3302_ = lean_ctor_get(v___x_3301_, 6);
lean_inc_ref(v_moduleData_3302_);
lean_dec_ref(v___x_3301_);
v___x_3303_ = lean_array_get_size(v_moduleData_3302_);
v___x_3304_ = lean_nat_dec_lt(v___y_3294_, v___x_3303_);
if (v___x_3304_ == 0)
{
lean_object* v___x_3305_; lean_object* v___x_3306_; 
lean_dec_ref(v_moduleData_3302_);
lean_dec_ref(v___x_3300_);
lean_dec(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec(v___y_3290_);
lean_dec_ref(v___x_2975_);
lean_del_object(v___x_2959_);
lean_dec(v_fst_2956_);
lean_dec(v_name_2945_);
lean_dec(v_head_2938_);
lean_del_object(v___x_2936_);
lean_dec(v_head_2934_);
v___x_3305_ = lean_obj_once(&l_main___closed__22, &l_main___closed__22_once, _init_l_main___closed__22);
v___x_3306_ = l_panic___at___00main_spec__5(v___x_3305_);
return v___x_3306_;
}
else
{
lean_object* v_base_3307_; lean_object* v_private_3308_; lean_object* v_header_3309_; lean_object* v_serverBaseExts_3310_; lean_object* v_checked_3311_; lean_object* v_asyncConstsMap_3312_; lean_object* v_asyncCtx_x3f_3313_; lean_object* v_importRealizationCtx_x3f_3314_; lean_object* v_localRealizationCtxMap_3315_; lean_object* v_allRealizations_3316_; uint8_t v_isExporting_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3392_; 
v_base_3307_ = lean_ctor_get(v___x_3300_, 0);
lean_inc_ref(v_base_3307_);
v_private_3308_ = lean_ctor_get(v_base_3307_, 0);
lean_inc(v_private_3308_);
v_header_3309_ = lean_ctor_get(v_private_3308_, 5);
lean_inc_ref(v_header_3309_);
v_serverBaseExts_3310_ = lean_ctor_get(v___x_3300_, 1);
v_checked_3311_ = lean_ctor_get(v___x_3300_, 2);
v_asyncConstsMap_3312_ = lean_ctor_get(v___x_3300_, 3);
v_asyncCtx_x3f_3313_ = lean_ctor_get(v___x_3300_, 4);
v_importRealizationCtx_x3f_3314_ = lean_ctor_get(v___x_3300_, 5);
v_localRealizationCtxMap_3315_ = lean_ctor_get(v___x_3300_, 6);
v_allRealizations_3316_ = lean_ctor_get(v___x_3300_, 7);
v_isExporting_3317_ = lean_ctor_get_uint8(v___x_3300_, sizeof(void*)*8);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3392_ == 0)
{
lean_object* v_unused_3393_; 
v_unused_3393_ = lean_ctor_get(v___x_3300_, 0);
lean_dec(v_unused_3393_);
v___x_3319_ = v___x_3300_;
v_isShared_3320_ = v_isSharedCheck_3392_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_allRealizations_3316_);
lean_inc(v_localRealizationCtxMap_3315_);
lean_inc(v_importRealizationCtx_x3f_3314_);
lean_inc(v_asyncCtx_x3f_3313_);
lean_inc(v_asyncConstsMap_3312_);
lean_inc(v_checked_3311_);
lean_inc(v_serverBaseExts_3310_);
lean_dec(v___x_3300_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3392_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v_public_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3390_; 
v_public_3321_ = lean_ctor_get(v_base_3307_, 1);
v_isSharedCheck_3390_ = !lean_is_exclusive(v_base_3307_);
if (v_isSharedCheck_3390_ == 0)
{
lean_object* v_unused_3391_; 
v_unused_3391_ = lean_ctor_get(v_base_3307_, 0);
lean_dec(v_unused_3391_);
v___x_3323_ = v_base_3307_;
v_isShared_3324_ = v_isSharedCheck_3390_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_public_3321_);
lean_dec(v_base_3307_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3390_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v_constants_3325_; uint8_t v_quotInit_3326_; lean_object* v_diagnostics_3327_; lean_object* v_const2ModIdx_3328_; lean_object* v_extensions_3329_; lean_object* v_irBaseExts_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3388_; 
v_constants_3325_ = lean_ctor_get(v_private_3308_, 0);
v_quotInit_3326_ = lean_ctor_get_uint8(v_private_3308_, sizeof(void*)*6);
v_diagnostics_3327_ = lean_ctor_get(v_private_3308_, 1);
v_const2ModIdx_3328_ = lean_ctor_get(v_private_3308_, 2);
v_extensions_3329_ = lean_ctor_get(v_private_3308_, 3);
v_irBaseExts_3330_ = lean_ctor_get(v_private_3308_, 4);
v_isSharedCheck_3388_ = !lean_is_exclusive(v_private_3308_);
if (v_isSharedCheck_3388_ == 0)
{
lean_object* v_unused_3389_; 
v_unused_3389_ = lean_ctor_get(v_private_3308_, 5);
lean_dec(v_unused_3389_);
v___x_3332_ = v_private_3308_;
v_isShared_3333_ = v_isSharedCheck_3388_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_irBaseExts_3330_);
lean_inc(v_extensions_3329_);
lean_inc(v_const2ModIdx_3328_);
lean_inc(v_diagnostics_3327_);
lean_inc(v_constants_3325_);
lean_dec(v_private_3308_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3388_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
uint32_t v_trustLevel_3334_; lean_object* v_mainModule_3335_; uint8_t v_isModule_3336_; lean_object* v_regions_3337_; lean_object* v_modules_3338_; lean_object* v_moduleName2Idx_3339_; lean_object* v_importAllModules_3340_; lean_object* v_moduleData_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3386_; 
v_trustLevel_3334_ = lean_ctor_get_uint32(v_header_3309_, sizeof(void*)*7);
v_mainModule_3335_ = lean_ctor_get(v_header_3309_, 0);
v_isModule_3336_ = lean_ctor_get_uint8(v_header_3309_, sizeof(void*)*7 + 4);
v_regions_3337_ = lean_ctor_get(v_header_3309_, 2);
v_modules_3338_ = lean_ctor_get(v_header_3309_, 3);
v_moduleName2Idx_3339_ = lean_ctor_get(v_header_3309_, 4);
v_importAllModules_3340_ = lean_ctor_get(v_header_3309_, 5);
v_moduleData_3341_ = lean_ctor_get(v_header_3309_, 6);
v_isSharedCheck_3386_ = !lean_is_exclusive(v_header_3309_);
if (v_isSharedCheck_3386_ == 0)
{
lean_object* v_unused_3387_; 
v_unused_3387_ = lean_ctor_get(v_header_3309_, 1);
lean_dec(v_unused_3387_);
v___x_3343_ = v_header_3309_;
v_isShared_3344_ = v_isSharedCheck_3386_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_moduleData_3341_);
lean_inc(v_importAllModules_3340_);
lean_inc(v_moduleName2Idx_3339_);
lean_inc(v_modules_3338_);
lean_inc(v_regions_3337_);
lean_inc(v_mainModule_3335_);
lean_dec(v_header_3309_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3386_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v___x_3345_; lean_object* v_imports_3346_; lean_object* v___x_3348_; 
v___x_3345_ = lean_array_fget(v_moduleData_3302_, v___y_3294_);
lean_dec_ref(v_moduleData_3302_);
v_imports_3346_ = lean_ctor_get(v___x_3345_, 0);
lean_inc_ref(v_imports_3346_);
lean_dec(v___x_3345_);
if (v_isShared_3344_ == 0)
{
lean_ctor_set(v___x_3343_, 1, v_imports_3346_);
v___x_3348_ = v___x_3343_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(0, 7, 5);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_mainModule_3335_);
lean_ctor_set(v_reuseFailAlloc_3385_, 1, v_imports_3346_);
lean_ctor_set(v_reuseFailAlloc_3385_, 2, v_regions_3337_);
lean_ctor_set(v_reuseFailAlloc_3385_, 3, v_modules_3338_);
lean_ctor_set(v_reuseFailAlloc_3385_, 4, v_moduleName2Idx_3339_);
lean_ctor_set(v_reuseFailAlloc_3385_, 5, v_importAllModules_3340_);
lean_ctor_set(v_reuseFailAlloc_3385_, 6, v_moduleData_3341_);
lean_ctor_set_uint32(v_reuseFailAlloc_3385_, sizeof(void*)*7, v_trustLevel_3334_);
lean_ctor_set_uint8(v_reuseFailAlloc_3385_, sizeof(void*)*7 + 4, v_isModule_3336_);
v___x_3348_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
lean_object* v___x_3350_; 
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 5, v___x_3348_);
v___x_3350_ = v___x_3332_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v_constants_3325_);
lean_ctor_set(v_reuseFailAlloc_3384_, 1, v_diagnostics_3327_);
lean_ctor_set(v_reuseFailAlloc_3384_, 2, v_const2ModIdx_3328_);
lean_ctor_set(v_reuseFailAlloc_3384_, 3, v_extensions_3329_);
lean_ctor_set(v_reuseFailAlloc_3384_, 4, v_irBaseExts_3330_);
lean_ctor_set(v_reuseFailAlloc_3384_, 5, v___x_3348_);
lean_ctor_set_uint8(v_reuseFailAlloc_3384_, sizeof(void*)*6, v_quotInit_3326_);
v___x_3350_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
lean_object* v___x_3352_; 
if (v_isShared_3324_ == 0)
{
lean_ctor_set(v___x_3323_, 0, v___x_3350_);
v___x_3352_ = v___x_3323_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v___x_3350_);
lean_ctor_set(v_reuseFailAlloc_3383_, 1, v_public_3321_);
v___x_3352_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
lean_object* v___x_3354_; 
if (v_isShared_3320_ == 0)
{
lean_ctor_set(v___x_3319_, 0, v___x_3352_);
v___x_3354_ = v___x_3319_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v___x_3352_);
lean_ctor_set(v_reuseFailAlloc_3382_, 1, v_serverBaseExts_3310_);
lean_ctor_set(v_reuseFailAlloc_3382_, 2, v_checked_3311_);
lean_ctor_set(v_reuseFailAlloc_3382_, 3, v_asyncConstsMap_3312_);
lean_ctor_set(v_reuseFailAlloc_3382_, 4, v_asyncCtx_x3f_3313_);
lean_ctor_set(v_reuseFailAlloc_3382_, 5, v_importRealizationCtx_x3f_3314_);
lean_ctor_set(v_reuseFailAlloc_3382_, 6, v_localRealizationCtxMap_3315_);
lean_ctor_set(v_reuseFailAlloc_3382_, 7, v_allRealizations_3316_);
lean_ctor_set_uint8(v_reuseFailAlloc_3382_, sizeof(void*)*8, v_isExporting_3317_);
v___x_3354_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v_env_3378_; lean_object* v___x_3379_; uint8_t v___x_3380_; uint8_t v___x_3381_; 
v___x_3355_ = l_Lean_Compiler_LCNF_postponedCompileDeclsExt;
v___x_3356_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2969_, v___x_3355_, v___x_3354_, v___y_3294_, v___x_3288_);
lean_dec(v___y_3294_);
v___x_3357_ = l_Lean_firstFrontendMacroScope;
v___x_3358_ = lean_obj_once(&l_main___closed__23, &l_main___closed__23_once, _init_l_main___closed__23);
v___x_3359_ = ((lean_object*)(l_main___closed__26));
lean_inc_n(v___y_3293_, 3);
v___x_3360_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3360_, 0, v___y_3293_);
lean_ctor_set(v___x_3360_, 1, v___x_3285_);
lean_ctor_set(v___x_3360_, 2, v___x_2962_);
v___x_3361_ = lean_obj_once(&l_main___closed__27, &l_main___closed__27_once, _init_l_main___closed__27);
v___x_3362_ = lean_obj_once(&l_main___closed__30, &l_main___closed__30_once, _init_l_main___closed__30);
v___x_3363_ = lean_obj_once(&l_main___closed__31, &l_main___closed__31_once, _init_l_main___closed__31);
v___x_3364_ = lean_obj_once(&l_main___closed__32, &l_main___closed__32_once, _init_l_main___closed__32);
v___x_3365_ = ((lean_object*)(l_main___closed__33));
lean_inc_ref(v___x_3360_);
v___x_3366_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3354_);
lean_ctor_set(v___x_3366_, 1, v___x_3358_);
lean_ctor_set(v___x_3366_, 2, v___x_3359_);
lean_ctor_set(v___x_3366_, 3, v___x_3360_);
lean_ctor_set(v___x_3366_, 4, v___x_3361_);
lean_ctor_set(v___x_3366_, 5, v___x_3362_);
lean_ctor_set(v___x_3366_, 6, v___x_3363_);
lean_ctor_set(v___x_3366_, 7, v___x_3364_);
lean_ctor_set(v___x_3366_, 8, v___x_3365_);
v___x_3367_ = lean_st_mk_ref(v___x_3366_);
v___x_3368_ = l_Lean_inheritedTraceOptions;
v___x_3369_ = lean_st_ref_get(v___x_3368_);
v___x_3370_ = lean_st_ref_get(v___x_3367_);
v___x_3371_ = l_Lean_instInhabitedFileMap_default;
v___x_3372_ = lean_box(0);
v___x_3373_ = lean_unsigned_to_nat(1000u);
v___x_3374_ = lean_box(0);
v___x_3375_ = l_Lean_Core_getMaxHeartbeats(v___x_2975_);
lean_inc(v_head_2934_);
v___x_3376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3376_, 0, v_head_2934_);
lean_ctor_set(v___x_3376_, 1, v___x_3371_);
lean_ctor_set(v___x_3376_, 2, v___y_3293_);
lean_ctor_set(v___x_3376_, 3, v___x_3372_);
lean_ctor_set(v___x_3376_, 4, v___x_3369_);
lean_inc_ref(v___x_2975_);
v___x_3377_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_3377_, 0, v___x_3376_);
lean_ctor_set(v___x_3377_, 1, v___x_2975_);
lean_ctor_set(v___x_3377_, 2, v___x_2974_);
lean_ctor_set(v___x_3377_, 3, v___x_3373_);
lean_ctor_set(v___x_3377_, 4, v___x_3374_);
lean_ctor_set(v___x_3377_, 5, v___y_3293_);
lean_ctor_set(v___x_3377_, 6, v___x_2962_);
lean_ctor_set(v___x_3377_, 7, v___x_2974_);
lean_ctor_set(v___x_3377_, 8, v___x_3375_);
lean_ctor_set(v___x_3377_, 9, v___x_3357_);
lean_ctor_set_uint8(v___x_3377_, sizeof(void*)*10, v___x_2948_);
lean_ctor_set_uint8(v___x_3377_, sizeof(void*)*10 + 1, v___x_2948_);
v_env_3378_ = lean_ctor_get(v___x_3370_, 0);
lean_inc_ref(v_env_3378_);
lean_dec(v___x_3370_);
v___x_3379_ = l_Lean_diagnostics;
v___x_3380_ = l_Lean_Option_get___at___00main_spec__8(v___x_2975_, v___x_3379_);
v___x_3381_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3378_);
lean_dec_ref(v_env_3378_);
if (v___x_3380_ == 0)
{
if (v___x_3381_ == 0)
{
v___y_3240_ = v___x_3371_;
v___y_3241_ = v___x_3362_;
v___y_3242_ = v___x_3304_;
v___y_3243_ = v___x_3372_;
v___y_3244_ = v___x_3357_;
v___y_3245_ = v___x_2962_;
v___y_3246_ = v___x_3368_;
v___y_3247_ = v___y_3290_;
v___y_3248_ = v___x_3374_;
v___y_3249_ = v___x_3364_;
v___y_3250_ = v___x_3380_;
v___y_3251_ = v___x_3359_;
v___y_3252_ = v___x_3356_;
v___y_3253_ = v___x_3361_;
v___y_3254_ = v___x_3360_;
v___y_3255_ = v___x_3377_;
v___y_3256_ = v___x_3358_;
v___y_3257_ = v___x_3362_;
v___y_3258_ = v___x_3355_;
v___y_3259_ = v___x_3365_;
v___y_3260_ = v___x_3363_;
v___y_3261_ = v___x_3367_;
v___y_3262_ = v___y_3293_;
v___y_3263_ = v___x_3304_;
goto v___jp_3239_;
}
else
{
v___y_3240_ = v___x_3371_;
v___y_3241_ = v___x_3362_;
v___y_3242_ = v___x_3304_;
v___y_3243_ = v___x_3372_;
v___y_3244_ = v___x_3357_;
v___y_3245_ = v___x_2962_;
v___y_3246_ = v___x_3368_;
v___y_3247_ = v___y_3290_;
v___y_3248_ = v___x_3374_;
v___y_3249_ = v___x_3364_;
v___y_3250_ = v___x_3380_;
v___y_3251_ = v___x_3359_;
v___y_3252_ = v___x_3356_;
v___y_3253_ = v___x_3361_;
v___y_3254_ = v___x_3360_;
v___y_3255_ = v___x_3377_;
v___y_3256_ = v___x_3358_;
v___y_3257_ = v___x_3362_;
v___y_3258_ = v___x_3355_;
v___y_3259_ = v___x_3365_;
v___y_3260_ = v___x_3363_;
v___y_3261_ = v___x_3367_;
v___y_3262_ = v___y_3293_;
v___y_3263_ = v___x_3380_;
goto v___jp_3239_;
}
}
else
{
v___y_3240_ = v___x_3371_;
v___y_3241_ = v___x_3362_;
v___y_3242_ = v___x_3304_;
v___y_3243_ = v___x_3372_;
v___y_3244_ = v___x_3357_;
v___y_3245_ = v___x_2962_;
v___y_3246_ = v___x_3368_;
v___y_3247_ = v___y_3290_;
v___y_3248_ = v___x_3374_;
v___y_3249_ = v___x_3364_;
v___y_3250_ = v___x_3380_;
v___y_3251_ = v___x_3359_;
v___y_3252_ = v___x_3356_;
v___y_3253_ = v___x_3361_;
v___y_3254_ = v___x_3360_;
v___y_3255_ = v___x_3377_;
v___y_3256_ = v___x_3358_;
v___y_3257_ = v___x_3362_;
v___y_3258_ = v___x_3355_;
v___y_3259_ = v___x_3365_;
v___y_3260_ = v___x_3363_;
v___y_3261_ = v___x_3367_;
v___y_3262_ = v___y_3293_;
v___y_3263_ = v___x_3381_;
goto v___jp_3239_;
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
v___jp_3395_:
{
lean_object* v___x_3400_; lean_object* v_toEnvExtension_3401_; lean_object* v_asyncMode_3402_; lean_object* v___x_3403_; lean_object* v_importedEntries_3404_; lean_object* v_state_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; uint8_t v___x_3408_; 
v___x_3400_ = l_Lean_IR_declMapExt;
v_toEnvExtension_3401_ = lean_ctor_get(v___x_3400_, 0);
v_asyncMode_3402_ = lean_ctor_get(v_toEnvExtension_3401_, 2);
lean_inc(v___y_3398_);
lean_inc_ref(v___y_3399_);
v___x_3403_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2966_, v_toEnvExtension_3401_, v___y_3399_, v_asyncMode_3402_, v___y_3398_);
v_importedEntries_3404_ = lean_ctor_get(v___x_3403_, 0);
lean_inc_ref(v_importedEntries_3404_);
v_state_3405_ = lean_ctor_get(v___x_3403_, 1);
lean_inc(v_state_3405_);
lean_dec(v___x_3403_);
v___x_3406_ = lean_array_get_borrowed(v___x_2967_, v_importedEntries_3404_, v___y_3397_);
v___x_3407_ = lean_array_get_size(v___x_3406_);
v___x_3408_ = lean_nat_dec_lt(v___x_2974_, v___x_3407_);
if (v___x_3408_ == 0)
{
v___y_3290_ = v___y_3396_;
v___y_3291_ = v_importedEntries_3404_;
v___y_3292_ = v___y_3399_;
v___y_3293_ = v___y_3398_;
v___y_3294_ = v___y_3397_;
v___y_3295_ = v_toEnvExtension_3401_;
v___y_3296_ = v_state_3405_;
goto v___jp_3289_;
}
else
{
uint8_t v___x_3409_; 
v___x_3409_ = lean_nat_dec_le(v___x_3407_, v___x_3407_);
if (v___x_3409_ == 0)
{
if (v___x_3408_ == 0)
{
v___y_3290_ = v___y_3396_;
v___y_3291_ = v_importedEntries_3404_;
v___y_3292_ = v___y_3399_;
v___y_3293_ = v___y_3398_;
v___y_3294_ = v___y_3397_;
v___y_3295_ = v_toEnvExtension_3401_;
v___y_3296_ = v_state_3405_;
goto v___jp_3289_;
}
else
{
size_t v___x_3410_; size_t v___x_3411_; lean_object* v___x_3412_; 
v___x_3410_ = ((size_t)0ULL);
v___x_3411_ = lean_usize_of_nat(v___x_3407_);
lean_inc_ref(v___y_3399_);
v___x_3412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3399_, v___x_3406_, v___x_3410_, v___x_3411_, v_state_3405_);
v___y_3290_ = v___y_3396_;
v___y_3291_ = v_importedEntries_3404_;
v___y_3292_ = v___y_3399_;
v___y_3293_ = v___y_3398_;
v___y_3294_ = v___y_3397_;
v___y_3295_ = v_toEnvExtension_3401_;
v___y_3296_ = v___x_3412_;
goto v___jp_3289_;
}
}
else
{
size_t v___x_3413_; size_t v___x_3414_; lean_object* v___x_3415_; 
v___x_3413_ = ((size_t)0ULL);
v___x_3414_ = lean_usize_of_nat(v___x_3407_);
lean_inc_ref(v___y_3399_);
v___x_3415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3399_, v___x_3406_, v___x_3413_, v___x_3414_, v_state_3405_);
v___y_3290_ = v___y_3396_;
v___y_3291_ = v_importedEntries_3404_;
v___y_3292_ = v___y_3399_;
v___y_3293_ = v___y_3398_;
v___y_3294_ = v___y_3397_;
v___y_3295_ = v_toEnvExtension_3401_;
v___y_3296_ = v___x_3415_;
goto v___jp_3289_;
}
}
}
v___jp_3416_:
{
uint8_t v___x_3423_; 
v___x_3423_ = lean_nat_dec_lt(v___x_2974_, v___y_3418_);
if (v___x_3423_ == 0)
{
lean_dec_ref(v___y_3419_);
lean_dec(v___y_3418_);
v___y_3396_ = v___y_3417_;
v___y_3397_ = v___y_3421_;
v___y_3398_ = v___y_3420_;
v___y_3399_ = v___y_3422_;
goto v___jp_3395_;
}
else
{
uint8_t v___x_3424_; 
v___x_3424_ = lean_nat_dec_le(v___y_3418_, v___y_3418_);
if (v___x_3424_ == 0)
{
if (v___x_3423_ == 0)
{
lean_dec_ref(v___y_3419_);
lean_dec(v___y_3418_);
v___y_3396_ = v___y_3417_;
v___y_3397_ = v___y_3421_;
v___y_3398_ = v___y_3420_;
v___y_3399_ = v___y_3422_;
goto v___jp_3395_;
}
else
{
size_t v___x_3425_; size_t v___x_3426_; lean_object* v___x_3427_; 
v___x_3425_ = ((size_t)0ULL);
v___x_3426_ = lean_usize_of_nat(v___y_3418_);
lean_dec(v___y_3418_);
v___x_3427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3419_, v___x_3425_, v___x_3426_, v___y_3422_);
lean_dec_ref(v___y_3419_);
v___y_3396_ = v___y_3417_;
v___y_3397_ = v___y_3421_;
v___y_3398_ = v___y_3420_;
v___y_3399_ = v___x_3427_;
goto v___jp_3395_;
}
}
else
{
size_t v___x_3428_; size_t v___x_3429_; lean_object* v___x_3430_; 
v___x_3428_ = ((size_t)0ULL);
v___x_3429_ = lean_usize_of_nat(v___y_3418_);
lean_dec(v___y_3418_);
v___x_3430_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3419_, v___x_3428_, v___x_3429_, v___y_3422_);
lean_dec_ref(v___y_3419_);
v___y_3396_ = v___y_3417_;
v___y_3397_ = v___y_3421_;
v___y_3398_ = v___y_3420_;
v___y_3399_ = v___x_3430_;
goto v___jp_3395_;
}
}
}
v___jp_3431_:
{
lean_object* v___x_3437_; uint8_t v___x_3438_; 
v___x_3437_ = lean_array_get_size(v___y_3436_);
v___x_3438_ = lean_nat_dec_lt(v___x_2974_, v___x_3437_);
if (v___x_3438_ == 0)
{
v___y_3417_ = v___y_3432_;
v___y_3418_ = v___x_3437_;
v___y_3419_ = v___y_3436_;
v___y_3420_ = v___y_3435_;
v___y_3421_ = v___y_3433_;
v___y_3422_ = v___y_3434_;
goto v___jp_3416_;
}
else
{
uint8_t v___x_3439_; 
v___x_3439_ = lean_nat_dec_le(v___x_3437_, v___x_3437_);
if (v___x_3439_ == 0)
{
if (v___x_3438_ == 0)
{
v___y_3417_ = v___y_3432_;
v___y_3418_ = v___x_3437_;
v___y_3419_ = v___y_3436_;
v___y_3420_ = v___y_3435_;
v___y_3421_ = v___y_3433_;
v___y_3422_ = v___y_3434_;
goto v___jp_3416_;
}
else
{
size_t v___x_3440_; size_t v___x_3441_; lean_object* v___x_3442_; 
v___x_3440_ = ((size_t)0ULL);
v___x_3441_ = lean_usize_of_nat(v___x_3437_);
v___x_3442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v___y_3436_, v___x_3440_, v___x_3441_, v___y_3434_);
v___y_3417_ = v___y_3432_;
v___y_3418_ = v___x_3437_;
v___y_3419_ = v___y_3436_;
v___y_3420_ = v___y_3435_;
v___y_3421_ = v___y_3433_;
v___y_3422_ = v___x_3442_;
goto v___jp_3416_;
}
}
else
{
size_t v___x_3443_; size_t v___x_3444_; lean_object* v___x_3445_; 
v___x_3443_ = ((size_t)0ULL);
v___x_3444_ = lean_usize_of_nat(v___x_3437_);
v___x_3445_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v___y_3436_, v___x_3443_, v___x_3444_, v___y_3434_);
v___y_3417_ = v___y_3432_;
v___y_3418_ = v___x_3437_;
v___y_3419_ = v___y_3436_;
v___y_3420_ = v___y_3435_;
v___y_3421_ = v___y_3433_;
v___y_3422_ = v___x_3445_;
goto v___jp_3416_;
}
}
}
v___jp_3447_:
{
lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___f_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
v___x_3449_ = l_Lean_instInhabitedImportState_default;
v___x_3450_ = lean_box(v___x_3288_);
v___x_3451_ = lean_box(v___y_3448_);
v___x_3452_ = lean_box(v___x_2971_);
v___x_3453_ = lean_box(v___x_3446_);
v___x_3454_ = lean_box(v___x_2948_);
lean_inc_ref(v___x_2975_);
lean_inc(v_name_2945_);
v___f_3455_ = lean_alloc_closure((void*)(l_main___lam__0___boxed), 11, 10);
lean_closure_set(v___f_3455_, 0, v___x_3449_);
lean_closure_set(v___f_3455_, 1, v___x_3287_);
lean_closure_set(v___f_3455_, 2, v___x_3450_);
lean_closure_set(v___f_3455_, 3, v_importArts_2946_);
lean_closure_set(v___f_3455_, 4, v___x_3451_);
lean_closure_set(v___f_3455_, 5, v___x_3452_);
lean_closure_set(v___f_3455_, 6, v_name_2945_);
lean_closure_set(v___f_3455_, 7, v___x_3453_);
lean_closure_set(v___f_3455_, 8, v___x_2975_);
lean_closure_set(v___f_3455_, 9, v___x_3454_);
v___x_3456_ = lean_alloc_closure((void*)(l_Lean_withImporting___boxed), 3, 2);
lean_closure_set(v___x_3456_, 0, lean_box(0));
lean_closure_set(v___x_3456_, 1, v___f_3455_);
v___x_3457_ = lean_box(0);
v___x_3458_ = l_Lean_profileitIOUnsafe___redArg(v___x_3283_, v___x_2975_, v___x_3456_, v___x_3457_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v_a_3459_; lean_object* v___x_3460_; lean_object* v_ext_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; 
v_a_3459_ = lean_ctor_get(v___x_3458_, 0);
lean_inc(v_a_3459_);
lean_dec_ref_known(v___x_3458_, 1);
v___x_3460_ = l_Lean_Compiler_CSimp_ext;
v_ext_3461_ = lean_ctor_get(v___x_3460_, 1);
lean_inc(v_name_2945_);
v___x_3462_ = l_Lean_Environment_setMainModule(v_a_3459_, v_name_2945_);
lean_inc_ref(v_ext_3461_);
v___x_3463_ = l_main___elam__0___redArg(v___x_3457_, v___x_2961_, v_ext_3461_, v___x_3462_);
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_object* v_a_3464_; lean_object* v___x_3465_; lean_object* v_ext_3466_; lean_object* v___x_3467_; 
v_a_3464_ = lean_ctor_get(v___x_3463_, 0);
lean_inc(v_a_3464_);
lean_dec_ref_known(v___x_3463_, 1);
v___x_3465_ = l_Lean_Meta_instanceExtension;
v_ext_3466_ = lean_ctor_get(v___x_3465_, 1);
lean_inc_ref(v_ext_3466_);
v___x_3467_ = l_main___elam__0___redArg(v___x_3457_, v___x_2961_, v_ext_3466_, v_a_3464_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v_a_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v_a_3468_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_a_3468_);
lean_dec_ref_known(v___x_3467_, 1);
v___x_3469_ = l_Lean_classExtension;
v___x_3470_ = l_main___elam__0___redArg(v___x_3457_, v___x_2963_, v___x_3469_, v_a_3468_);
if (lean_obj_tag(v___x_3470_) == 0)
{
lean_object* v_a_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; 
v_a_3471_ = lean_ctor_get(v___x_3470_, 0);
lean_inc(v_a_3471_);
lean_dec_ref_known(v___x_3470_, 1);
v___x_3472_ = l_Lean_Meta_Match_Extension_extension;
v___x_3473_ = l_main___elam__0___redArg(v___x_3457_, v___x_2964_, v___x_3472_, v_a_3471_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3501_; 
v_a_3474_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3476_ = v___x_3473_;
v_isShared_3477_ = v_isSharedCheck_3501_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___x_3473_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3501_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___x_3478_; 
v___x_3478_ = l_Lean_Environment_getModuleIdx_x3f(v_a_3474_, v_name_2945_);
if (lean_obj_tag(v___x_3478_) == 1)
{
lean_object* v_val_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; uint8_t v___x_3484_; 
lean_del_object(v___x_3476_);
v_val_3479_ = lean_ctor_get(v___x_3478_, 0);
lean_inc(v_val_3479_);
lean_dec_ref_known(v___x_3478_, 1);
v___x_3480_ = l_Lean_Compiler_LCNF_impureSigExt;
v___x_3481_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2965_, v___x_3480_, v_a_3474_, v_val_3479_, v___x_3288_);
v___x_3482_ = lean_array_get_size(v___x_3481_);
v___x_3483_ = ((lean_object*)(l_main___closed__34));
v___x_3484_ = lean_nat_dec_lt(v___x_2974_, v___x_3482_);
if (v___x_3484_ == 0)
{
lean_dec_ref(v___x_3481_);
v___y_3432_ = v___x_3457_;
v___y_3433_ = v_val_3479_;
v___y_3434_ = v_a_3474_;
v___y_3435_ = v___x_3457_;
v___y_3436_ = v___x_3483_;
goto v___jp_3431_;
}
else
{
uint8_t v___x_3485_; 
v___x_3485_ = lean_nat_dec_le(v___x_3482_, v___x_3482_);
if (v___x_3485_ == 0)
{
if (v___x_3484_ == 0)
{
lean_dec_ref(v___x_3481_);
v___y_3432_ = v___x_3457_;
v___y_3433_ = v_val_3479_;
v___y_3434_ = v_a_3474_;
v___y_3435_ = v___x_3457_;
v___y_3436_ = v___x_3483_;
goto v___jp_3431_;
}
else
{
size_t v___x_3486_; size_t v___x_3487_; lean_object* v___x_3488_; 
v___x_3486_ = ((size_t)0ULL);
v___x_3487_ = lean_usize_of_nat(v___x_3482_);
lean_inc(v_a_3474_);
v___x_3488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_3474_, v___x_3481_, v___x_3486_, v___x_3487_, v___x_3483_);
lean_dec_ref(v___x_3481_);
v___y_3432_ = v___x_3457_;
v___y_3433_ = v_val_3479_;
v___y_3434_ = v_a_3474_;
v___y_3435_ = v___x_3457_;
v___y_3436_ = v___x_3488_;
goto v___jp_3431_;
}
}
else
{
size_t v___x_3489_; size_t v___x_3490_; lean_object* v___x_3491_; 
v___x_3489_ = ((size_t)0ULL);
v___x_3490_ = lean_usize_of_nat(v___x_3482_);
lean_inc(v_a_3474_);
v___x_3491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_3474_, v___x_3481_, v___x_3489_, v___x_3490_, v___x_3483_);
lean_dec_ref(v___x_3481_);
v___y_3432_ = v___x_3457_;
v___y_3433_ = v_val_3479_;
v___y_3434_ = v_a_3474_;
v___y_3435_ = v___x_3457_;
v___y_3436_ = v___x_3491_;
goto v___jp_3431_;
}
}
}
else
{
lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3499_; 
lean_dec(v___x_3478_);
lean_dec(v_a_3474_);
lean_dec_ref(v___x_2975_);
lean_del_object(v___x_2959_);
lean_dec(v_fst_2956_);
lean_dec(v_head_2938_);
lean_del_object(v___x_2936_);
lean_dec(v_head_2934_);
lean_del_object(v___x_2932_);
v___x_3492_ = ((lean_object*)(l_main___closed__35));
v___x_3493_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2945_, v___x_2971_);
v___x_3494_ = lean_string_append(v___x_3492_, v___x_3493_);
lean_dec_ref(v___x_3493_);
v___x_3495_ = ((lean_object*)(l_main___closed__36));
v___x_3496_ = lean_string_append(v___x_3494_, v___x_3495_);
v___x_3497_ = lean_mk_io_user_error(v___x_3496_);
if (v_isShared_3477_ == 0)
{
lean_ctor_set_tag(v___x_3476_, 1);
lean_ctor_set(v___x_3476_, 0, v___x_3497_);
v___x_3499_ = v___x_3476_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v___x_3497_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
return v___x_3499_;
}
}
}
}
else
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3509_; 
lean_dec_ref(v___x_2975_);
lean_del_object(v___x_2959_);
lean_dec(v_fst_2956_);
lean_dec(v_name_2945_);
lean_dec(v_head_2938_);
lean_del_object(v___x_2936_);
lean_dec(v_head_2934_);
lean_del_object(v___x_2932_);
v_a_3502_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3504_ = v___x_3473_;
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3473_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3507_; 
if (v_isShared_3505_ == 0)
{
v___x_3507_ = v___x_3504_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_a_3502_);
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
lean_dec_ref(v___x_2975_);
lean_del_object(v___x_2959_);
lean_dec(v_fst_2956_);
lean_dec(v_name_2945_);
lean_dec(v_head_2938_);
lean_del_object(v___x_2936_);
lean_dec(v_head_2934_);
lean_del_object(v___x_2932_);
v_a_3510_ = lean_ctor_get(v___x_3470_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3470_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3512_ = v___x_3470_;
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3470_);
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
lean_dec_ref(v___x_2975_);
lean_del_object(v___x_2959_);
lean_dec(v_fst_2956_);
lean_dec(v_name_2945_);
lean_dec(v_head_2938_);
lean_del_object(v___x_2936_);
lean_dec(v_head_2934_);
lean_del_object(v___x_2932_);
v_a_3518_ = lean_ctor_get(v___x_3467_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3520_ = v___x_3467_;
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3467_);
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
lean_dec_ref(v___x_2975_);
lean_del_object(v___x_2959_);
lean_dec(v_fst_2956_);
lean_dec(v_name_2945_);
lean_dec(v_head_2938_);
lean_del_object(v___x_2936_);
lean_dec(v_head_2934_);
lean_del_object(v___x_2932_);
v_a_3526_ = lean_ctor_get(v___x_3463_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3528_ = v___x_3463_;
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v___x_3463_);
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
lean_dec_ref(v___x_2975_);
lean_del_object(v___x_2959_);
lean_dec(v_fst_2956_);
lean_dec(v_name_2945_);
lean_dec(v_head_2938_);
lean_del_object(v___x_2936_);
lean_dec(v_head_2934_);
lean_del_object(v___x_2932_);
v_a_3534_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3536_ = v___x_3458_;
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_a_3534_);
lean_dec(v___x_3458_);
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
}
}
else
{
lean_object* v_a_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3551_; 
lean_dec(v_a_2954_);
lean_dec(v_importArts_2946_);
lean_dec(v_name_2945_);
lean_dec(v_head_2938_);
lean_del_object(v___x_2936_);
lean_dec(v_head_2934_);
lean_del_object(v___x_2932_);
v_a_3544_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_3551_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_3551_ == 0)
{
v___x_3546_ = v___x_2955_;
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_a_3544_);
lean_dec(v___x_2955_);
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
else
{
lean_object* v_a_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3559_; 
lean_dec(v_importArts_2946_);
lean_dec(v_name_2945_);
lean_dec(v_head_2938_);
lean_del_object(v___x_2936_);
lean_dec(v_head_2934_);
lean_del_object(v___x_2932_);
v_a_3552_ = lean_ctor_get(v___x_2953_, 0);
v_isSharedCheck_3559_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_3559_ == 0)
{
v___x_3554_ = v___x_2953_;
v_isShared_3555_ = v_isSharedCheck_3559_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_a_3552_);
lean_dec(v___x_2953_);
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
}
else
{
lean_object* v_a_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3568_; 
lean_del_object(v___x_2941_);
lean_dec(v_tail_2939_);
lean_dec(v_head_2938_);
lean_del_object(v___x_2936_);
lean_dec(v_head_2934_);
lean_del_object(v___x_2932_);
v_a_3561_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3563_ = v___x_2943_;
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_a_3561_);
lean_dec(v___x_2943_);
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
}
}
else
{
lean_dec(v_tail_2929_);
lean_dec_ref_known(v_tail_2928_, 2);
lean_dec_ref_known(v_args_2903_, 2);
goto v___jp_2905_;
}
}
else
{
lean_dec_ref_known(v_args_2903_, 2);
lean_dec(v_tail_2928_);
goto v___jp_2905_;
}
}
else
{
lean_dec(v_args_2903_);
goto v___jp_2905_;
}
v___jp_2905_:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; 
v___x_2906_ = ((lean_object*)(l_main___closed__0));
v___x_2907_ = l_IO_println___at___00Lean_Environment_displayStats_spec__1(v___x_2906_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2915_; 
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2915_ == 0)
{
lean_object* v_unused_2916_; 
v_unused_2916_ = lean_ctor_get(v___x_2907_, 0);
lean_dec(v_unused_2916_);
v___x_2909_ = v___x_2907_;
v_isShared_2910_ = v_isSharedCheck_2915_;
goto v_resetjp_2908_;
}
else
{
lean_dec(v___x_2907_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2915_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2911_; lean_object* v___x_2913_; 
v___x_2911_ = l_main___boxed__const__1;
if (v_isShared_2910_ == 0)
{
lean_ctor_set(v___x_2909_, 0, v___x_2911_);
v___x_2913_ = v___x_2909_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v___x_2911_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
else
{
lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
v_a_2917_ = lean_ctor_get(v___x_2907_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2919_ = v___x_2907_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_dec(v___x_2907_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2920_ == 0)
{
v___x_2922_ = v___x_2919_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2917_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
v___jp_2925_:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2926_ = l_main___boxed__const__2;
v___x_2927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2926_);
return v___x_2927_;
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_3574_, lean_object* v_a_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = _lean_main(v_args_3574_);
return v_res_3576_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1(lean_object* v_as_3577_, lean_object* v_as_x27_3578_, lean_object* v_b_3579_, lean_object* v_a_3580_){
_start:
{
lean_object* v___x_3582_; 
v___x_3582_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_3578_, v_b_3579_);
return v___x_3582_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___boxed(lean_object* v_as_3583_, lean_object* v_as_x27_3584_, lean_object* v_b_3585_, lean_object* v_a_3586_, lean_object* v___y_3587_){
_start:
{
lean_object* v_res_3588_; 
v_res_3588_ = l_List_forIn_x27_loop___at___00main_spec__1(v_as_3583_, v_as_x27_3584_, v_b_3585_, v_a_3586_);
lean_dec(v_as_x27_3584_);
lean_dec(v_as_3583_);
return v_res_3588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16(lean_object* v___y_3589_, lean_object* v___y_3590_){
_start:
{
lean_object* v___x_3592_; 
v___x_3592_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_3590_);
return v___x_3592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___boxed(lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_){
_start:
{
lean_object* v_res_3596_; 
v_res_3596_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16(v___y_3593_, v___y_3594_);
lean_dec(v___y_3594_);
lean_dec_ref(v___y_3593_);
return v_res_3596_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17(lean_object* v_00_u03b2_3597_, lean_object* v_m_3598_, lean_object* v_a_3599_, lean_object* v_fallback_3600_){
_start:
{
lean_object* v___x_3601_; 
v___x_3601_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_m_3598_, v_a_3599_, v_fallback_3600_);
return v___x_3601_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___boxed(lean_object* v_00_u03b2_3602_, lean_object* v_m_3603_, lean_object* v_a_3604_, lean_object* v_fallback_3605_){
_start:
{
lean_object* v_res_3606_; 
v_res_3606_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17(v_00_u03b2_3602_, v_m_3603_, v_a_3604_, v_fallback_3605_);
lean_dec(v_fallback_3605_);
lean_dec_ref(v_a_3604_);
lean_dec_ref(v_m_3603_);
return v_res_3606_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18(lean_object* v_00_u03b2_3607_, lean_object* v_m_3608_, lean_object* v_a_3609_, lean_object* v_b_3610_){
_start:
{
lean_object* v___x_3611_; 
v___x_3611_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_m_3608_, v_a_3609_, v_b_3610_);
return v___x_3611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21(lean_object* v_n_3612_, lean_object* v_as_3613_, lean_object* v_lo_3614_, lean_object* v_hi_3615_, lean_object* v_w_3616_, lean_object* v_hlo_3617_, lean_object* v_hhi_3618_){
_start:
{
lean_object* v___x_3619_; 
v___x_3619_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_3612_, v_as_3613_, v_lo_3614_, v_hi_3615_);
return v___x_3619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___boxed(lean_object* v_n_3620_, lean_object* v_as_3621_, lean_object* v_lo_3622_, lean_object* v_hi_3623_, lean_object* v_w_3624_, lean_object* v_hlo_3625_, lean_object* v_hhi_3626_){
_start:
{
lean_object* v_res_3627_; 
v_res_3627_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21(v_n_3620_, v_as_3621_, v_lo_3622_, v_hi_3623_, v_w_3624_, v_hlo_3625_, v_hhi_3626_);
lean_dec(v_hi_3623_);
lean_dec(v_n_3620_);
return v_res_3627_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21(lean_object* v_00_u03b2_3628_, lean_object* v_a_3629_, lean_object* v_fallback_3630_, lean_object* v_x_3631_){
_start:
{
lean_object* v___x_3632_; 
v___x_3632_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_3629_, v_fallback_3630_, v_x_3631_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___boxed(lean_object* v_00_u03b2_3633_, lean_object* v_a_3634_, lean_object* v_fallback_3635_, lean_object* v_x_3636_){
_start:
{
lean_object* v_res_3637_; 
v_res_3637_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21(v_00_u03b2_3633_, v_a_3634_, v_fallback_3635_, v_x_3636_);
lean_dec(v_x_3636_);
lean_dec(v_fallback_3635_);
lean_dec_ref(v_a_3634_);
return v_res_3637_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23(lean_object* v_00_u03b2_3638_, lean_object* v_a_3639_, lean_object* v_x_3640_){
_start:
{
uint8_t v___x_3641_; 
v___x_3641_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_3639_, v_x_3640_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___boxed(lean_object* v_00_u03b2_3642_, lean_object* v_a_3643_, lean_object* v_x_3644_){
_start:
{
uint8_t v_res_3645_; lean_object* v_r_3646_; 
v_res_3645_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23(v_00_u03b2_3642_, v_a_3643_, v_x_3644_);
lean_dec(v_x_3644_);
lean_dec_ref(v_a_3643_);
v_r_3646_ = lean_box(v_res_3645_);
return v_r_3646_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24(lean_object* v_00_u03b2_3647_, lean_object* v_data_3648_){
_start:
{
lean_object* v___x_3649_; 
v___x_3649_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(v_data_3648_);
return v___x_3649_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25(lean_object* v_00_u03b2_3650_, lean_object* v_a_3651_, lean_object* v_b_3652_, lean_object* v_x_3653_){
_start:
{
lean_object* v___x_3654_; 
v___x_3654_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_3651_, v_b_3652_, v_x_3653_);
return v___x_3654_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31(lean_object* v_n_3655_, lean_object* v_lo_3656_, lean_object* v_hi_3657_, lean_object* v_hhi_3658_, lean_object* v_pivot_3659_, lean_object* v_as_3660_, lean_object* v_i_3661_, lean_object* v_k_3662_, lean_object* v_ilo_3663_, lean_object* v_ik_3664_, lean_object* v_w_3665_){
_start:
{
lean_object* v___x_3666_; 
v___x_3666_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_3657_, v_pivot_3659_, v_as_3660_, v_i_3661_, v_k_3662_);
return v___x_3666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___boxed(lean_object* v_n_3667_, lean_object* v_lo_3668_, lean_object* v_hi_3669_, lean_object* v_hhi_3670_, lean_object* v_pivot_3671_, lean_object* v_as_3672_, lean_object* v_i_3673_, lean_object* v_k_3674_, lean_object* v_ilo_3675_, lean_object* v_ik_3676_, lean_object* v_w_3677_){
_start:
{
lean_object* v_res_3678_; 
v_res_3678_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31(v_n_3667_, v_lo_3668_, v_hi_3669_, v_hhi_3670_, v_pivot_3671_, v_as_3672_, v_i_3673_, v_k_3674_, v_ilo_3675_, v_ik_3676_, v_w_3677_);
lean_dec_ref(v_pivot_3671_);
lean_dec(v_hi_3669_);
lean_dec(v_lo_3668_);
lean_dec(v_n_3667_);
return v_res_3678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40(lean_object* v_as_3679_, size_t v_sz_3680_, size_t v_i_3681_, lean_object* v_b_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_){
_start:
{
lean_object* v___x_3686_; 
v___x_3686_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_3679_, v_sz_3680_, v_i_3681_, v_b_3682_, v___y_3683_);
return v___x_3686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___boxed(lean_object* v_as_3687_, lean_object* v_sz_3688_, lean_object* v_i_3689_, lean_object* v_b_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_){
_start:
{
size_t v_sz_boxed_3694_; size_t v_i_boxed_3695_; lean_object* v_res_3696_; 
v_sz_boxed_3694_ = lean_unbox_usize(v_sz_3688_);
lean_dec(v_sz_3688_);
v_i_boxed_3695_ = lean_unbox_usize(v_i_3689_);
lean_dec(v_i_3689_);
v_res_3696_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40(v_as_3687_, v_sz_boxed_3694_, v_i_boxed_3695_, v_b_3690_, v___y_3691_, v___y_3692_);
lean_dec(v___y_3692_);
lean_dec_ref(v___y_3691_);
lean_dec_ref(v_as_3687_);
return v_res_3696_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35(lean_object* v_00_u03b2_3697_, lean_object* v_i_3698_, lean_object* v_source_3699_, lean_object* v_target_3700_){
_start:
{
lean_object* v___x_3701_; 
v___x_3701_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(v_i_3698_, v_source_3699_, v_target_3700_);
return v___x_3701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42(uint8_t v___x_3702_, lean_object* v_as_3703_, size_t v_sz_3704_, size_t v_i_3705_, lean_object* v_b_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_){
_start:
{
lean_object* v___x_3710_; 
v___x_3710_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_3702_, v_as_3703_, v_sz_3704_, v_i_3705_, v_b_3706_, v___y_3707_);
return v___x_3710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___boxed(lean_object* v___x_3711_, lean_object* v_as_3712_, lean_object* v_sz_3713_, lean_object* v_i_3714_, lean_object* v_b_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_){
_start:
{
uint8_t v___x_40158__boxed_3719_; size_t v_sz_boxed_3720_; size_t v_i_boxed_3721_; lean_object* v_res_3722_; 
v___x_40158__boxed_3719_ = lean_unbox(v___x_3711_);
v_sz_boxed_3720_ = lean_unbox_usize(v_sz_3713_);
lean_dec(v_sz_3713_);
v_i_boxed_3721_ = lean_unbox_usize(v_i_3714_);
lean_dec(v_i_3714_);
v_res_3722_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42(v___x_40158__boxed_3719_, v_as_3712_, v_sz_boxed_3720_, v_i_boxed_3721_, v_b_3715_, v___y_3716_, v___y_3717_);
lean_dec(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec_ref(v_as_3712_);
return v_res_3722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51(lean_object* v_as_3723_, size_t v_sz_3724_, size_t v_i_3725_, lean_object* v_b_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_){
_start:
{
lean_object* v___x_3730_; 
v___x_3730_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_3723_, v_sz_3724_, v_i_3725_, v_b_3726_, v___y_3727_);
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___boxed(lean_object* v_as_3731_, lean_object* v_sz_3732_, lean_object* v_i_3733_, lean_object* v_b_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_){
_start:
{
size_t v_sz_boxed_3738_; size_t v_i_boxed_3739_; lean_object* v_res_3740_; 
v_sz_boxed_3738_ = lean_unbox_usize(v_sz_3732_);
lean_dec(v_sz_3732_);
v_i_boxed_3739_ = lean_unbox_usize(v_i_3733_);
lean_dec(v_i_3733_);
v_res_3740_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51(v_as_3731_, v_sz_boxed_3738_, v_i_boxed_3739_, v_b_3734_, v___y_3735_, v___y_3736_);
lean_dec(v___y_3736_);
lean_dec_ref(v___y_3735_);
lean_dec_ref(v_as_3731_);
return v_res_3740_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44(lean_object* v_00_u03b2_3741_, lean_object* v_x_3742_, lean_object* v_x_3743_){
_start:
{
lean_object* v___x_3744_; 
v___x_3744_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(v_x_3742_, v_x_3743_);
return v___x_3744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49(uint8_t v___x_3745_, lean_object* v_as_3746_, size_t v_sz_3747_, size_t v_i_3748_, lean_object* v_b_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_){
_start:
{
lean_object* v___x_3753_; 
v___x_3753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_3745_, v_as_3746_, v_sz_3747_, v_i_3748_, v_b_3749_, v___y_3750_);
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___boxed(lean_object* v___x_3754_, lean_object* v_as_3755_, lean_object* v_sz_3756_, lean_object* v_i_3757_, lean_object* v_b_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_){
_start:
{
uint8_t v___x_40189__boxed_3762_; size_t v_sz_boxed_3763_; size_t v_i_boxed_3764_; lean_object* v_res_3765_; 
v___x_40189__boxed_3762_ = lean_unbox(v___x_3754_);
v_sz_boxed_3763_ = lean_unbox_usize(v_sz_3756_);
lean_dec(v_sz_3756_);
v_i_boxed_3764_ = lean_unbox_usize(v_i_3757_);
lean_dec(v_i_3757_);
v_res_3765_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49(v___x_40189__boxed_3762_, v_as_3755_, v_sz_boxed_3763_, v_i_boxed_3764_, v_b_3758_, v___y_3759_, v___y_3760_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec_ref(v_as_3755_);
return v_res_3765_;
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
