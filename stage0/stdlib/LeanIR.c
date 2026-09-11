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
uint8_t v___x_35413__boxed_512_; uint8_t v___y_35414__boxed_513_; uint8_t v___x_35415__boxed_514_; uint8_t v___x_35416__boxed_515_; uint8_t v___x_35418__boxed_516_; lean_object* v_res_517_; 
v___x_35413__boxed_512_ = lean_unbox(v___x_503_);
v___y_35414__boxed_513_ = lean_unbox(v___y_505_);
v___x_35415__boxed_514_ = lean_unbox(v___x_506_);
v___x_35416__boxed_515_ = lean_unbox(v___x_508_);
v___x_35418__boxed_516_ = lean_unbox(v___x_510_);
v_res_517_ = l_main___lam__0(v___x_501_, v___x_502_, v___x_35413__boxed_512_, v_importArts_504_, v___y_35414__boxed_513_, v___x_35415__boxed_514_, v_name_507_, v___x_35416__boxed_515_, v___x_509_, v___x_35418__boxed_516_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_main___lam__1(lean_object* v___x_521_, lean_object* v___x_522_, lean_object* v___x_523_, lean_object* v_name_524_, lean_object* v_a_525_, uint8_t v___x_526_, lean_object* v___x_527_, lean_object* v_head_528_, lean_object* v___x_529_, lean_object* v___x_530_, lean_object* v___x_531_, lean_object* v___x_532_, lean_object* v___x_533_, lean_object* v___x_534_, lean_object* v___x_535_, lean_object* v___x_536_, uint8_t v___x_537_){
_start:
{
lean_object* v_a_540_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v_env_547_; lean_object* v___x_548_; uint8_t v___x_549_; lean_object* v_fileName_551_; lean_object* v_fileMap_552_; lean_object* v_currNamespace_553_; lean_object* v_openDecls_554_; lean_object* v_initHeartbeats_555_; lean_object* v_maxHeartbeats_556_; lean_object* v_quotContext_557_; lean_object* v_currMacroScope_558_; lean_object* v_cancelTk_x3f_559_; lean_object* v_inheritedTraceOptions_560_; lean_object* v_currRecDepth_561_; lean_object* v_ref_562_; uint8_t v_suppressElabErrors_563_; lean_object* v___y_564_; uint8_t v___y_597_; uint8_t v___x_617_; 
v___x_543_ = lean_io_get_num_heartbeats();
v___x_544_ = lean_st_mk_ref(v___x_521_);
v___x_545_ = lean_st_ref_get(v___x_522_);
v___x_546_ = lean_st_ref_get(v___x_544_);
v_env_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc_ref(v_env_547_);
lean_dec(v___x_546_);
v___x_548_ = l_Lean_diagnostics;
v___x_549_ = l_Lean_Option_get___at___00main_spec__8(v___x_523_, v___x_548_);
v___x_617_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_547_);
lean_dec_ref(v_env_547_);
if (v___x_549_ == 0)
{
if (v___x_617_ == 0)
{
v___y_597_ = v___x_526_;
goto v___jp_596_;
}
else
{
v___y_597_ = v___x_549_;
goto v___jp_596_;
}
}
else
{
v___y_597_ = v___x_617_;
goto v___jp_596_;
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
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_565_ = l_Lean_maxRecDepth;
v___x_566_ = l_Lean_Option_get___at___00main_spec__9(v___x_523_, v___x_565_);
v___x_567_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_567_, 0, v_fileName_551_);
lean_ctor_set(v___x_567_, 1, v_fileMap_552_);
lean_ctor_set(v___x_567_, 2, v___x_523_);
lean_ctor_set(v___x_567_, 3, v___x_566_);
lean_ctor_set(v___x_567_, 4, v_currNamespace_553_);
lean_ctor_set(v___x_567_, 5, v_openDecls_554_);
lean_ctor_set(v___x_567_, 6, v_initHeartbeats_555_);
lean_ctor_set(v___x_567_, 7, v_maxHeartbeats_556_);
lean_ctor_set(v___x_567_, 8, v_quotContext_557_);
lean_ctor_set(v___x_567_, 9, v_currMacroScope_558_);
lean_ctor_set(v___x_567_, 10, v_cancelTk_x3f_559_);
lean_ctor_set(v___x_567_, 11, v_inheritedTraceOptions_560_);
v___x_568_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_568_, 0, v___x_567_);
lean_ctor_set(v___x_568_, 1, v_currRecDepth_561_);
lean_ctor_set(v___x_568_, 2, v_ref_562_);
lean_ctor_set_uint8(v___x_568_, sizeof(void*)*3, v___x_549_);
lean_ctor_set_uint8(v___x_568_, sizeof(void*)*3 + 1, v_suppressElabErrors_563_);
v___x_569_ = l_Lean_Compiler_LCNF_emitC(v_name_524_, v___x_568_, v___y_564_);
lean_dec(v___y_564_);
lean_dec_ref_known(v___x_568_, 3);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_a_570_);
lean_dec_ref_known(v___x_569_, 1);
v___x_571_ = lean_st_ref_get(v___x_544_);
lean_dec(v___x_544_);
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
lean_dec(v___x_544_);
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
v_a_540_ = v___x_589_;
goto v___jp_539_;
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
v_a_540_ = v___x_594_;
goto v___jp_539_;
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
v___x_598_ = lean_st_ref_take(v___x_544_);
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
v___x_610_ = l_Lean_Kernel_enableDiag(v_env_599_, v___x_549_);
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
v___x_613_ = lean_st_ref_put(v___x_544_, v___x_612_);
lean_inc(v___x_544_);
lean_inc(v___x_530_);
v_fileName_551_ = v_head_528_;
v_fileMap_552_ = v___x_529_;
v_currNamespace_553_ = v___x_530_;
v_openDecls_554_ = v___x_531_;
v_initHeartbeats_555_ = v___x_543_;
v_maxHeartbeats_556_ = v___x_532_;
v_quotContext_557_ = v___x_530_;
v_currMacroScope_558_ = v___x_533_;
v_cancelTk_x3f_559_ = v___x_534_;
v_inheritedTraceOptions_560_ = v___x_545_;
v_currRecDepth_561_ = v___x_535_;
v_ref_562_ = v___x_536_;
v_suppressElabErrors_563_ = v___x_537_;
v___y_564_ = v___x_544_;
goto v___jp_550_;
}
}
}
else
{
lean_dec_ref(v___x_527_);
lean_inc(v___x_544_);
lean_inc(v___x_530_);
v_fileName_551_ = v_head_528_;
v_fileMap_552_ = v___x_529_;
v_currNamespace_553_ = v___x_530_;
v_openDecls_554_ = v___x_531_;
v_initHeartbeats_555_ = v___x_543_;
v_maxHeartbeats_556_ = v___x_532_;
v_quotContext_557_ = v___x_530_;
v_currMacroScope_558_ = v___x_533_;
v_cancelTk_x3f_559_ = v___x_534_;
v_inheritedTraceOptions_560_ = v___x_545_;
v_currRecDepth_561_ = v___x_535_;
v_ref_562_ = v___x_536_;
v_suppressElabErrors_563_ = v___x_537_;
v___y_564_ = v___x_544_;
goto v___jp_550_;
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
lean_object* v___y_635_ = _args[17];
_start:
{
uint8_t v___x_35499__boxed_636_; uint8_t v___x_35510__boxed_637_; lean_object* v_res_638_; 
v___x_35499__boxed_636_ = lean_unbox(v___x_623_);
v___x_35510__boxed_637_ = lean_unbox(v___x_634_);
v_res_638_ = l_main___lam__1(v___x_618_, v___x_619_, v___x_620_, v_name_621_, v_a_622_, v___x_35499__boxed_636_, v___x_624_, v_head_625_, v___x_626_, v___x_627_, v___x_628_, v___x_629_, v___x_630_, v___x_631_, v___x_632_, v___x_633_, v___x_35510__boxed_637_);
lean_dec(v_a_622_);
lean_dec(v___x_619_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(lean_object* v_s_639_){
_start:
{
lean_object* v___x_641_; lean_object* v_putStr_642_; lean_object* v___x_643_; 
v___x_641_ = lean_get_stderr();
v_putStr_642_ = lean_ctor_get(v___x_641_, 4);
lean_inc_ref(v_putStr_642_);
lean_dec_ref(v___x_641_);
v___x_643_ = lean_apply_2(v_putStr_642_, v_s_639_, lean_box(0));
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8___boxed(lean_object* v_s_644_, lean_object* v_a_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v_s_644_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6(lean_object* v_s_647_){
_start:
{
uint32_t v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_649_ = 10;
v___x_650_ = lean_string_push(v_s_647_, v___x_649_);
v___x_651_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v___x_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6___boxed(lean_object* v_s_652_, lean_object* v_a_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_IO_eprintln___at___00main_spec__6(v_s_652_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(lean_object* v_o_658_, lean_object* v_k_659_, lean_object* v_v_660_){
_start:
{
lean_object* v_map_661_; uint8_t v_hasTrace_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_676_; 
v_map_661_ = lean_ctor_get(v_o_658_, 0);
v_hasTrace_662_ = lean_ctor_get_uint8(v_o_658_, sizeof(void*)*1);
v_isSharedCheck_676_ = !lean_is_exclusive(v_o_658_);
if (v_isSharedCheck_676_ == 0)
{
v___x_664_ = v_o_658_;
v_isShared_665_ = v_isSharedCheck_676_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_map_661_);
lean_dec(v_o_658_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_676_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_666_, 0, v_v_660_);
lean_inc(v_k_659_);
v___x_667_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_659_, v___x_666_, v_map_661_);
if (v_hasTrace_662_ == 0)
{
lean_object* v___x_668_; uint8_t v___x_669_; lean_object* v___x_671_; 
v___x_668_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_669_ = l_Lean_Name_isPrefixOf(v___x_668_, v_k_659_);
lean_dec(v_k_659_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v___x_667_);
v___x_671_ = v___x_664_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_667_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_ctor_set_uint8(v___x_671_, sizeof(void*)*1, v___x_669_);
return v___x_671_;
}
}
else
{
lean_object* v___x_674_; 
lean_dec(v_k_659_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v___x_667_);
v___x_674_ = v___x_664_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_667_);
lean_ctor_set_uint8(v_reuseFailAlloc_675_, sizeof(void*)*1, v_hasTrace_662_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00main_spec__3(lean_object* v_opts_677_, lean_object* v_opt_678_, lean_object* v_val_679_){
_start:
{
lean_object* v_name_680_; lean_object* v___x_681_; 
v_name_680_ = lean_ctor_get(v_opt_678_, 0);
lean_inc(v_name_680_);
lean_dec_ref(v_opt_678_);
v___x_681_ = l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(v_opts_677_, v_name_680_, v_val_679_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(lean_object* v___y_683_, lean_object* v_as_684_, size_t v_i_685_, size_t v_stop_686_, lean_object* v_b_687_){
_start:
{
lean_object* v___y_689_; uint8_t v___x_693_; 
v___x_693_ = lean_usize_dec_eq(v_i_685_, v_stop_686_);
if (v___x_693_ == 0)
{
lean_object* v_fst_694_; lean_object* v_snd_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___y_699_; 
v_fst_694_ = lean_ctor_get(v_b_687_, 0);
v_snd_695_ = lean_ctor_get(v_b_687_, 1);
v___x_696_ = lean_array_uget_borrowed(v_as_684_, v_i_685_);
v___x_697_ = l_Lean_IR_Decl_name(v___x_696_);
if (lean_obj_tag(v___x_697_) == 1)
{
lean_object* v_pre_712_; lean_object* v_str_713_; lean_object* v___x_714_; uint8_t v___x_715_; 
v_pre_712_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_pre_712_);
v_str_713_ = lean_ctor_get(v___x_697_, 1);
lean_inc_ref(v_str_713_);
v___x_714_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___closed__0));
v___x_715_ = lean_string_dec_eq(v_str_713_, v___x_714_);
lean_dec_ref(v_str_713_);
if (v___x_715_ == 0)
{
lean_dec(v_pre_712_);
lean_inc_ref(v___x_697_);
v___y_699_ = v___x_697_;
goto v___jp_698_;
}
else
{
v___y_699_ = v_pre_712_;
goto v___jp_698_;
}
}
else
{
lean_inc(v___x_697_);
v___y_699_ = v___x_697_;
goto v___jp_698_;
}
v___jp_698_:
{
uint8_t v___x_700_; 
lean_inc_ref(v___y_683_);
v___x_700_ = l_Lean_isExtern(v___y_683_, v___y_699_);
if (v___x_700_ == 0)
{
lean_dec(v___x_697_);
v___y_689_ = v_b_687_;
goto v___jp_688_;
}
else
{
lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_709_; 
lean_inc(v_snd_695_);
lean_inc(v_fst_694_);
v_isSharedCheck_709_ = !lean_is_exclusive(v_b_687_);
if (v_isSharedCheck_709_ == 0)
{
lean_object* v_unused_710_; lean_object* v_unused_711_; 
v_unused_710_ = lean_ctor_get(v_b_687_, 1);
lean_dec(v_unused_710_);
v_unused_711_ = lean_ctor_get(v_b_687_, 0);
lean_dec(v_unused_711_);
v___x_702_ = v_b_687_;
v_isShared_703_ = v_isSharedCheck_709_;
goto v_resetjp_701_;
}
else
{
lean_dec(v_b_687_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_709_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_707_; 
lean_inc_n(v___x_696_, 2);
v___x_704_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_696_);
lean_ctor_set(v___x_704_, 1, v_fst_694_);
v___x_705_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(v_snd_695_, v___x_697_, v___x_696_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 1, v___x_705_);
lean_ctor_set(v___x_702_, 0, v___x_704_);
v___x_707_ = v___x_702_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_704_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v___x_705_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
v___y_689_ = v___x_707_;
goto v___jp_688_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_683_);
return v_b_687_;
}
v___jp_688_:
{
size_t v___x_690_; size_t v___x_691_; 
v___x_690_ = ((size_t)1ULL);
v___x_691_ = lean_usize_add(v_i_685_, v___x_690_);
v_i_685_ = v___x_691_;
v_b_687_ = v___y_689_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___boxed(lean_object* v___y_716_, lean_object* v_as_717_, lean_object* v_i_718_, lean_object* v_stop_719_, lean_object* v_b_720_){
_start:
{
size_t v_i_boxed_721_; size_t v_stop_boxed_722_; lean_object* v_res_723_; 
v_i_boxed_721_ = lean_unbox_usize(v_i_718_);
lean_dec(v_i_718_);
v_stop_boxed_722_ = lean_unbox_usize(v_stop_719_);
lean_dec(v_stop_719_);
v_res_723_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_716_, v_as_717_, v_i_boxed_721_, v_stop_boxed_722_, v_b_720_);
lean_dec_ref(v_as_717_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg(lean_object* v_as_x27_725_, lean_object* v_b_726_){
_start:
{
if (lean_obj_tag(v_as_x27_725_) == 0)
{
lean_object* v___x_728_; 
v___x_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_728_, 0, v_b_726_);
return v___x_728_;
}
else
{
lean_object* v_head_729_; lean_object* v_tail_730_; lean_object* v_fst_731_; lean_object* v_snd_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_757_; 
v_head_729_ = lean_ctor_get(v_as_x27_725_, 0);
v_tail_730_ = lean_ctor_get(v_as_x27_725_, 1);
v_fst_731_ = lean_ctor_get(v_b_726_, 0);
v_snd_732_ = lean_ctor_get(v_b_726_, 1);
v_isSharedCheck_757_ = !lean_is_exclusive(v_b_726_);
if (v_isSharedCheck_757_ == 0)
{
v___x_734_ = v_b_726_;
v_isShared_735_ = v_isSharedCheck_757_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_snd_732_);
lean_inc(v_fst_731_);
lean_dec(v_b_726_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_757_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_736_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0));
v___x_737_ = lean_string_dec_eq(v_head_729_, v___x_736_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; 
lean_inc(v_head_729_);
v___x_738_ = l___private_LeanIR_0__setConfigOption(v_snd_732_, v_head_729_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_741_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
lean_dec_ref_known(v___x_738_, 1);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 1, v_a_739_);
v___x_741_ = v___x_734_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_fst_731_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_a_739_);
v___x_741_ = v_reuseFailAlloc_743_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
v_as_x27_725_ = v_tail_730_;
v_b_726_ = v___x_741_;
goto _start;
}
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_del_object(v___x_734_);
lean_dec(v_fst_731_);
v_a_744_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_738_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_738_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
else
{
lean_object* v___x_752_; lean_object* v___x_754_; 
lean_dec(v_fst_731_);
v___x_752_ = lean_box(v___x_737_);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 0, v___x_752_);
v___x_754_ = v___x_734_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v_snd_732_);
v___x_754_ = v_reuseFailAlloc_756_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
v_as_x27_725_ = v_tail_730_;
v_b_726_ = v___x_754_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg___boxed(lean_object* v_as_x27_758_, lean_object* v_b_759_, lean_object* v___y_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_758_, v_b_759_);
lean_dec(v_as_x27_758_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(lean_object* v_as_762_, size_t v_i_763_, size_t v_stop_764_, lean_object* v_b_765_){
_start:
{
uint8_t v___x_766_; 
v___x_766_ = lean_usize_dec_eq(v_i_763_, v_stop_764_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; lean_object* v_toEnvExtension_768_; lean_object* v_asyncMode_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; size_t v___x_773_; size_t v___x_774_; 
v___x_767_ = l_Lean_Compiler_LCNF_impureSigExt;
v_toEnvExtension_768_ = lean_ctor_get(v___x_767_, 0);
v_asyncMode_769_ = lean_ctor_get(v_toEnvExtension_768_, 2);
v___x_770_ = lean_box(0);
v___x_771_ = lean_array_uget_borrowed(v_as_762_, v_i_763_);
lean_inc(v___x_771_);
v___x_772_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_767_, v_b_765_, v___x_771_, v_asyncMode_769_, v___x_770_);
v___x_773_ = ((size_t)1ULL);
v___x_774_ = lean_usize_add(v_i_763_, v___x_773_);
v_i_763_ = v___x_774_;
v_b_765_ = v___x_772_;
goto _start;
}
else
{
return v_b_765_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18___boxed(lean_object* v_as_776_, lean_object* v_i_777_, lean_object* v_stop_778_, lean_object* v_b_779_){
_start:
{
size_t v_i_boxed_780_; size_t v_stop_boxed_781_; lean_object* v_res_782_; 
v_i_boxed_780_ = lean_unbox_usize(v_i_777_);
lean_dec(v_i_777_);
v_stop_boxed_781_ = lean_unbox_usize(v_stop_778_);
lean_dec(v_stop_778_);
v_res_782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_as_776_, v_i_boxed_780_, v_stop_boxed_781_, v_b_779_);
lean_dec_ref(v_as_776_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(lean_object* v_as_786_, size_t v_sz_787_, size_t v_i_788_, lean_object* v_b_789_, lean_object* v___y_790_){
_start:
{
uint8_t v___x_792_; 
v___x_792_ = lean_usize_dec_lt(v_i_788_, v_sz_787_);
if (v___x_792_ == 0)
{
lean_object* v___x_793_; 
v___x_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_793_, 0, v_b_789_);
return v___x_793_;
}
else
{
uint8_t v___x_794_; lean_object* v_a_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
lean_dec_ref(v_b_789_);
v___x_794_ = 0;
v_a_795_ = lean_array_uget_borrowed(v_as_786_, v_i_788_);
lean_inc(v_a_795_);
v___x_796_ = l_Lean_Message_toString(v_a_795_, v___x_794_);
v___x_797_ = l_IO_eprintln___at___00main_spec__6(v___x_796_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v___x_798_; size_t v___x_799_; size_t v___x_800_; 
lean_dec_ref_known(v___x_797_, 1);
v___x_798_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_799_ = ((size_t)1ULL);
v___x_800_ = lean_usize_add(v_i_788_, v___x_799_);
v_i_788_ = v___x_800_;
v_b_789_ = v___x_798_;
goto _start;
}
else
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_814_; 
v_a_802_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_814_ == 0)
{
v___x_804_ = v___x_797_;
v_isShared_805_ = v_isSharedCheck_814_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_797_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_814_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v_ref_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_812_; 
v_ref_806_ = lean_ctor_get(v___y_790_, 2);
v___x_807_ = lean_io_error_to_string(v_a_802_);
v___x_808_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
v___x_809_ = l_Lean_MessageData_ofFormat(v___x_808_);
lean_inc(v_ref_806_);
v___x_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_810_, 0, v_ref_806_);
lean_ctor_set(v___x_810_, 1, v___x_809_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v___x_810_);
v___x_812_ = v___x_804_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_810_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___boxed(lean_object* v_as_815_, lean_object* v_sz_816_, lean_object* v_i_817_, lean_object* v_b_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
size_t v_sz_boxed_821_; size_t v_i_boxed_822_; lean_object* v_res_823_; 
v_sz_boxed_821_ = lean_unbox_usize(v_sz_816_);
lean_dec(v_sz_816_);
v_i_boxed_822_ = lean_unbox_usize(v_i_817_);
lean_dec(v_i_817_);
v_res_823_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_815_, v_sz_boxed_821_, v_i_boxed_822_, v_b_818_, v___y_819_);
lean_dec_ref(v___y_819_);
lean_dec_ref(v_as_815_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(lean_object* v_as_824_, size_t v_sz_825_, size_t v_i_826_, lean_object* v_b_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
uint8_t v___x_831_; 
v___x_831_ = lean_usize_dec_lt(v_i_826_, v_sz_825_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; 
v___x_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_832_, 0, v_b_827_);
return v___x_832_;
}
else
{
uint8_t v___x_833_; lean_object* v_a_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
lean_dec_ref(v_b_827_);
v___x_833_ = 0;
v_a_834_ = lean_array_uget_borrowed(v_as_824_, v_i_826_);
lean_inc(v_a_834_);
v___x_835_ = l_Lean_Message_toString(v_a_834_, v___x_833_);
v___x_836_ = l_IO_eprintln___at___00main_spec__6(v___x_835_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v___x_837_; size_t v___x_838_; size_t v___x_839_; lean_object* v___x_840_; 
lean_dec_ref_known(v___x_836_, 1);
v___x_837_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_838_ = ((size_t)1ULL);
v___x_839_ = lean_usize_add(v_i_826_, v___x_838_);
v___x_840_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_824_, v_sz_825_, v___x_839_, v___x_837_, v___y_828_);
return v___x_840_;
}
else
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_853_; 
v_a_841_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_853_ == 0)
{
v___x_843_ = v___x_836_;
v_isShared_844_ = v_isSharedCheck_853_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_836_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_853_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v_ref_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_851_; 
v_ref_845_ = lean_ctor_get(v___y_828_, 2);
v___x_846_ = lean_io_error_to_string(v_a_841_);
v___x_847_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
v___x_848_ = l_Lean_MessageData_ofFormat(v___x_847_);
lean_inc(v_ref_845_);
v___x_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_849_, 0, v_ref_845_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 0, v___x_849_);
v___x_851_ = v___x_843_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27___boxed(lean_object* v_as_854_, lean_object* v_sz_855_, lean_object* v_i_856_, lean_object* v_b_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
size_t v_sz_boxed_861_; size_t v_i_boxed_862_; lean_object* v_res_863_; 
v_sz_boxed_861_ = lean_unbox_usize(v_sz_855_);
lean_dec(v_sz_855_);
v_i_boxed_862_ = lean_unbox_usize(v_i_856_);
lean_dec(v_i_856_);
v_res_863_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(v_as_854_, v_sz_boxed_861_, v_i_boxed_862_, v_b_857_, v___y_858_, v___y_859_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec_ref(v_as_854_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(lean_object* v_as_867_, size_t v_sz_868_, size_t v_i_869_, lean_object* v_b_870_, lean_object* v___y_871_){
_start:
{
uint8_t v___x_873_; 
v___x_873_ = lean_usize_dec_lt(v_i_869_, v_sz_868_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; 
v___x_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_874_, 0, v_b_870_);
return v___x_874_;
}
else
{
uint8_t v___x_875_; lean_object* v_a_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
lean_dec_ref(v_b_870_);
v___x_875_ = 0;
v_a_876_ = lean_array_uget_borrowed(v_as_867_, v_i_869_);
lean_inc(v_a_876_);
v___x_877_ = l_Lean_Message_toString(v_a_876_, v___x_875_);
v___x_878_ = l_IO_eprintln___at___00main_spec__6(v___x_877_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v___x_879_; size_t v___x_880_; size_t v___x_881_; 
lean_dec_ref_known(v___x_878_, 1);
v___x_879_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_880_ = ((size_t)1ULL);
v___x_881_ = lean_usize_add(v_i_869_, v___x_880_);
v_i_869_ = v___x_881_;
v_b_870_ = v___x_879_;
goto _start;
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_895_; 
v_a_883_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_895_ == 0)
{
v___x_885_ = v___x_878_;
v_isShared_886_ = v_isSharedCheck_895_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_878_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_895_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v_ref_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_893_; 
v_ref_887_ = lean_ctor_get(v___y_871_, 2);
v___x_888_ = lean_io_error_to_string(v_a_883_);
v___x_889_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
v___x_890_ = l_Lean_MessageData_ofFormat(v___x_889_);
lean_inc(v_ref_887_);
v___x_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_891_, 0, v_ref_887_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v___x_891_);
v___x_893_ = v___x_885_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_891_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___boxed(lean_object* v_as_896_, lean_object* v_sz_897_, lean_object* v_i_898_, lean_object* v_b_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
size_t v_sz_boxed_902_; size_t v_i_boxed_903_; lean_object* v_res_904_; 
v_sz_boxed_902_ = lean_unbox_usize(v_sz_897_);
lean_dec(v_sz_897_);
v_i_boxed_903_ = lean_unbox_usize(v_i_898_);
lean_dec(v_i_898_);
v_res_904_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_896_, v_sz_boxed_902_, v_i_boxed_903_, v_b_899_, v___y_900_);
lean_dec_ref(v___y_900_);
lean_dec_ref(v_as_896_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(lean_object* v_as_905_, size_t v_sz_906_, size_t v_i_907_, lean_object* v_b_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
uint8_t v___x_912_; 
v___x_912_ = lean_usize_dec_lt(v_i_907_, v_sz_906_);
if (v___x_912_ == 0)
{
lean_object* v___x_913_; 
v___x_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_913_, 0, v_b_908_);
return v___x_913_;
}
else
{
uint8_t v___x_914_; lean_object* v_a_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
lean_dec_ref(v_b_908_);
v___x_914_ = 0;
v_a_915_ = lean_array_uget_borrowed(v_as_905_, v_i_907_);
lean_inc(v_a_915_);
v___x_916_ = l_Lean_Message_toString(v_a_915_, v___x_914_);
v___x_917_ = l_IO_eprintln___at___00main_spec__6(v___x_916_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v___x_918_; size_t v___x_919_; size_t v___x_920_; lean_object* v___x_921_; 
lean_dec_ref_known(v___x_917_, 1);
v___x_918_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_919_ = ((size_t)1ULL);
v___x_920_ = lean_usize_add(v_i_907_, v___x_919_);
v___x_921_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_905_, v_sz_906_, v___x_920_, v___x_918_, v___y_909_);
return v___x_921_;
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_934_; 
v_a_922_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_934_ == 0)
{
v___x_924_ = v___x_917_;
v_isShared_925_ = v_isSharedCheck_934_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_917_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_934_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v_ref_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_932_; 
v_ref_926_ = lean_ctor_get(v___y_909_, 2);
v___x_927_ = lean_io_error_to_string(v_a_922_);
v___x_928_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
v___x_929_ = l_Lean_MessageData_ofFormat(v___x_928_);
lean_inc(v_ref_926_);
v___x_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_930_, 0, v_ref_926_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v___x_930_);
v___x_932_ = v___x_924_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_930_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38___boxed(lean_object* v_as_935_, lean_object* v_sz_936_, lean_object* v_i_937_, lean_object* v_b_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
size_t v_sz_boxed_942_; size_t v_i_boxed_943_; lean_object* v_res_944_; 
v_sz_boxed_942_ = lean_unbox_usize(v_sz_936_);
lean_dec(v_sz_936_);
v_i_boxed_943_ = lean_unbox_usize(v_i_937_);
lean_dec(v_i_937_);
v_res_944_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(v_as_935_, v_sz_boxed_942_, v_i_boxed_943_, v_b_938_, v___y_939_, v___y_940_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec_ref(v_as_935_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(lean_object* v_init_945_, lean_object* v_n_946_, lean_object* v_b_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
if (lean_obj_tag(v_n_946_) == 0)
{
lean_object* v_cs_951_; lean_object* v___x_952_; lean_object* v___x_953_; size_t v_sz_954_; size_t v___x_955_; lean_object* v___x_956_; 
v_cs_951_ = lean_ctor_get(v_n_946_, 0);
v___x_952_ = lean_box(0);
v___x_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
lean_ctor_set(v___x_953_, 1, v_b_947_);
v_sz_954_ = lean_array_size(v_cs_951_);
v___x_955_ = ((size_t)0ULL);
v___x_956_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(v_init_945_, v_cs_951_, v_sz_954_, v___x_955_, v___x_953_, v___y_948_, v___y_949_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_971_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_971_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_971_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_971_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v_fst_961_; 
v_fst_961_ = lean_ctor_get(v_a_957_, 0);
if (lean_obj_tag(v_fst_961_) == 0)
{
lean_object* v_snd_962_; lean_object* v___x_963_; lean_object* v___x_965_; 
v_snd_962_ = lean_ctor_get(v_a_957_, 1);
lean_inc(v_snd_962_);
lean_dec(v_a_957_);
v___x_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_963_, 0, v_snd_962_);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v___x_963_);
v___x_965_ = v___x_959_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_963_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
else
{
lean_object* v_val_967_; lean_object* v___x_969_; 
lean_inc_ref(v_fst_961_);
lean_dec(v_a_957_);
v_val_967_ = lean_ctor_get(v_fst_961_, 0);
lean_inc(v_val_967_);
lean_dec_ref_known(v_fst_961_, 1);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v_val_967_);
v___x_969_ = v___x_959_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_val_967_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
else
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_979_; 
v_a_972_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_979_ == 0)
{
v___x_974_ = v___x_956_;
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_956_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_975_ == 0)
{
v___x_977_ = v___x_974_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_a_972_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
else
{
lean_object* v_vs_980_; lean_object* v___x_981_; lean_object* v___x_982_; size_t v_sz_983_; size_t v___x_984_; lean_object* v___x_985_; 
v_vs_980_ = lean_ctor_get(v_n_946_, 0);
v___x_981_ = lean_box(0);
v___x_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
lean_ctor_set(v___x_982_, 1, v_b_947_);
v_sz_983_ = lean_array_size(v_vs_980_);
v___x_984_ = ((size_t)0ULL);
v___x_985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(v_vs_980_, v_sz_983_, v___x_984_, v___x_982_, v___y_948_, v___y_949_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1000_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_988_ = v___x_985_;
v_isShared_989_ = v_isSharedCheck_1000_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_985_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1000_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v_fst_990_; 
v_fst_990_ = lean_ctor_get(v_a_986_, 0);
if (lean_obj_tag(v_fst_990_) == 0)
{
lean_object* v_snd_991_; lean_object* v___x_992_; lean_object* v___x_994_; 
v_snd_991_ = lean_ctor_get(v_a_986_, 1);
lean_inc(v_snd_991_);
lean_dec(v_a_986_);
v___x_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_992_, 0, v_snd_991_);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v___x_992_);
v___x_994_ = v___x_988_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_992_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
else
{
lean_object* v_val_996_; lean_object* v___x_998_; 
lean_inc_ref(v_fst_990_);
lean_dec(v_a_986_);
v_val_996_ = lean_ctor_get(v_fst_990_, 0);
lean_inc(v_val_996_);
lean_dec_ref_known(v_fst_990_, 1);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v_val_996_);
v___x_998_ = v___x_988_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_val_996_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
else
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
v_a_1001_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_985_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_985_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(lean_object* v_init_1009_, lean_object* v_as_1010_, size_t v_sz_1011_, size_t v_i_1012_, lean_object* v_b_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
uint8_t v___x_1017_; 
v___x_1017_ = lean_usize_dec_lt(v_i_1012_, v_sz_1011_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1018_, 0, v_b_1013_);
return v___x_1018_;
}
else
{
lean_object* v_snd_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1053_; 
v_snd_1019_ = lean_ctor_get(v_b_1013_, 1);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_b_1013_);
if (v_isSharedCheck_1053_ == 0)
{
lean_object* v_unused_1054_; 
v_unused_1054_ = lean_ctor_get(v_b_1013_, 0);
lean_dec(v_unused_1054_);
v___x_1021_ = v_b_1013_;
v_isShared_1022_ = v_isSharedCheck_1053_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_snd_1019_);
lean_dec(v_b_1013_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1053_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v_a_1023_; lean_object* v___x_1024_; 
v_a_1023_ = lean_array_uget_borrowed(v_as_1010_, v_i_1012_);
lean_inc(v_snd_1019_);
v___x_1024_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_1009_, v_a_1023_, v_snd_1019_, v___y_1014_, v___y_1015_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1044_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1027_ = v___x_1024_;
v_isShared_1028_ = v_isSharedCheck_1044_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1024_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1044_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
if (lean_obj_tag(v_a_1025_) == 0)
{
lean_object* v___x_1029_; lean_object* v___x_1031_; 
v___x_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1029_, 0, v_a_1025_);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 0, v___x_1029_);
v___x_1031_ = v___x_1021_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1029_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v_snd_1019_);
v___x_1031_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
lean_object* v___x_1033_; 
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 0, v___x_1031_);
v___x_1033_ = v___x_1027_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1031_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1037_; lean_object* v___x_1039_; 
lean_del_object(v___x_1027_);
lean_dec(v_snd_1019_);
v_a_1036_ = lean_ctor_get(v_a_1025_, 0);
lean_inc(v_a_1036_);
lean_dec_ref_known(v_a_1025_, 1);
v___x_1037_ = lean_box(0);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 1, v_a_1036_);
lean_ctor_set(v___x_1021_, 0, v___x_1037_);
v___x_1039_ = v___x_1021_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_a_1036_);
v___x_1039_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
size_t v___x_1040_; size_t v___x_1041_; 
v___x_1040_ = ((size_t)1ULL);
v___x_1041_ = lean_usize_add(v_i_1012_, v___x_1040_);
v_i_1012_ = v___x_1041_;
v_b_1013_ = v___x_1039_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
lean_del_object(v___x_1021_);
lean_dec(v_snd_1019_);
v_a_1045_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_1024_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1024_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37___boxed(lean_object* v_init_1055_, lean_object* v_as_1056_, lean_object* v_sz_1057_, lean_object* v_i_1058_, lean_object* v_b_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
size_t v_sz_boxed_1063_; size_t v_i_boxed_1064_; lean_object* v_res_1065_; 
v_sz_boxed_1063_ = lean_unbox_usize(v_sz_1057_);
lean_dec(v_sz_1057_);
v_i_boxed_1064_ = lean_unbox_usize(v_i_1058_);
lean_dec(v_i_1058_);
v_res_1065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(v_init_1055_, v_as_1056_, v_sz_boxed_1063_, v_i_boxed_1064_, v_b_1059_, v___y_1060_, v___y_1061_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec_ref(v_as_1056_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26___boxed(lean_object* v_init_1066_, lean_object* v_n_1067_, lean_object* v_b_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_1066_, v_n_1067_, v_b_1068_, v___y_1069_, v___y_1070_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec_ref(v_n_1067_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__12(lean_object* v_t_1073_, lean_object* v_init_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v_root_1078_; lean_object* v_tail_1079_; lean_object* v___x_1080_; 
v_root_1078_ = lean_ctor_get(v_t_1073_, 0);
v_tail_1079_ = lean_ctor_get(v_t_1073_, 1);
v___x_1080_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_1074_, v_root_1078_, v_init_1074_, v___y_1075_, v___y_1076_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1117_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1083_ = v___x_1080_;
v_isShared_1084_ = v_isSharedCheck_1117_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1080_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1117_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
if (lean_obj_tag(v_a_1081_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1087_; 
v_a_1085_ = lean_ctor_get(v_a_1081_, 0);
lean_inc(v_a_1085_);
lean_dec_ref_known(v_a_1081_, 1);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v_a_1085_);
v___x_1087_ = v___x_1083_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1085_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; size_t v_sz_1092_; size_t v___x_1093_; lean_object* v___x_1094_; 
lean_del_object(v___x_1083_);
v_a_1089_ = lean_ctor_get(v_a_1081_, 0);
lean_inc(v_a_1089_);
lean_dec_ref_known(v_a_1081_, 1);
v___x_1090_ = lean_box(0);
v___x_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
lean_ctor_set(v___x_1091_, 1, v_a_1089_);
v_sz_1092_ = lean_array_size(v_tail_1079_);
v___x_1093_ = ((size_t)0ULL);
v___x_1094_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(v_tail_1079_, v_sz_1092_, v___x_1093_, v___x_1091_, v___y_1075_, v___y_1076_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1108_; 
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1097_ = v___x_1094_;
v_isShared_1098_ = v_isSharedCheck_1108_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1094_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1108_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v_fst_1099_; 
v_fst_1099_ = lean_ctor_get(v_a_1095_, 0);
if (lean_obj_tag(v_fst_1099_) == 0)
{
lean_object* v_snd_1100_; lean_object* v___x_1102_; 
v_snd_1100_ = lean_ctor_get(v_a_1095_, 1);
lean_inc(v_snd_1100_);
lean_dec(v_a_1095_);
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 0, v_snd_1100_);
v___x_1102_ = v___x_1097_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_snd_1100_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
else
{
lean_object* v_val_1104_; lean_object* v___x_1106_; 
lean_inc_ref(v_fst_1099_);
lean_dec(v_a_1095_);
v_val_1104_ = lean_ctor_get(v_fst_1099_, 0);
lean_inc(v_val_1104_);
lean_dec_ref_known(v_fst_1099_, 1);
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 0, v_val_1104_);
v___x_1106_ = v___x_1097_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_val_1104_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
else
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
v_a_1109_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1111_ = v___x_1094_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1094_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
if (v_isShared_1112_ == 0)
{
v___x_1114_ = v___x_1111_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1109_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
}
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
v_a_1118_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1080_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1080_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__12___boxed(lean_object* v_t_1126_, lean_object* v_init_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_PersistentArray_forIn___at___00main_spec__12(v_t_1126_, v_init_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec_ref(v_t_1126_);
return v_res_1131_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0(uint8_t v_suppressElabErrors_1139_, uint8_t v___x_1140_, lean_object* v___x_1141_, lean_object* v_x_1142_){
_start:
{
if (lean_obj_tag(v_x_1142_) == 1)
{
lean_object* v_pre_1143_; 
v_pre_1143_ = lean_ctor_get(v_x_1142_, 0);
switch(lean_obj_tag(v_pre_1143_))
{
case 1:
{
lean_object* v_pre_1144_; 
v_pre_1144_ = lean_ctor_get(v_pre_1143_, 0);
switch(lean_obj_tag(v_pre_1144_))
{
case 0:
{
lean_object* v_str_1145_; lean_object* v_str_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; 
v_str_1145_ = lean_ctor_get(v_x_1142_, 1);
v_str_1146_ = lean_ctor_get(v_pre_1143_, 1);
v___x_1147_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0));
v___x_1148_ = lean_string_dec_eq(v_str_1146_, v___x_1147_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; uint8_t v___x_1150_; 
v___x_1149_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1));
v___x_1150_ = lean_string_dec_eq(v_str_1146_, v___x_1149_);
if (v___x_1150_ == 0)
{
return v___x_1150_;
}
else
{
lean_object* v___x_1151_; uint8_t v___x_1152_; 
v___x_1151_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2));
v___x_1152_ = lean_string_dec_eq(v_str_1145_, v___x_1151_);
if (v___x_1152_ == 0)
{
return v___x_1152_;
}
else
{
return v_suppressElabErrors_1139_;
}
}
}
else
{
lean_object* v___x_1153_; uint8_t v___x_1154_; 
v___x_1153_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3));
v___x_1154_ = lean_string_dec_eq(v_str_1145_, v___x_1153_);
if (v___x_1154_ == 0)
{
return v___x_1154_;
}
else
{
return v_suppressElabErrors_1139_;
}
}
}
case 1:
{
lean_object* v_pre_1155_; 
v_pre_1155_ = lean_ctor_get(v_pre_1144_, 0);
if (lean_obj_tag(v_pre_1155_) == 0)
{
lean_object* v_str_1156_; lean_object* v_str_1157_; lean_object* v_str_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
v_str_1156_ = lean_ctor_get(v_x_1142_, 1);
v_str_1157_ = lean_ctor_get(v_pre_1143_, 1);
v_str_1158_ = lean_ctor_get(v_pre_1144_, 1);
v___x_1159_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4));
v___x_1160_ = lean_string_dec_eq(v_str_1158_, v___x_1159_);
if (v___x_1160_ == 0)
{
return v___x_1160_;
}
else
{
lean_object* v___x_1161_; uint8_t v___x_1162_; 
v___x_1161_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5));
v___x_1162_ = lean_string_dec_eq(v_str_1157_, v___x_1161_);
if (v___x_1162_ == 0)
{
return v___x_1162_;
}
else
{
lean_object* v___x_1163_; uint8_t v___x_1164_; 
v___x_1163_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6));
v___x_1164_ = lean_string_dec_eq(v_str_1156_, v___x_1163_);
if (v___x_1164_ == 0)
{
return v___x_1164_;
}
else
{
return v_suppressElabErrors_1139_;
}
}
}
}
else
{
return v___x_1140_;
}
}
default: 
{
return v___x_1140_;
}
}
}
case 0:
{
lean_object* v_str_1165_; uint8_t v___x_1166_; 
v_str_1165_ = lean_ctor_get(v_x_1142_, 1);
v___x_1166_ = lean_string_dec_eq(v_str_1165_, v___x_1141_);
if (v___x_1166_ == 0)
{
return v___x_1166_;
}
else
{
return v_suppressElabErrors_1139_;
}
}
default: 
{
return v___x_1140_;
}
}
}
else
{
return v___x_1140_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___boxed(lean_object* v_suppressElabErrors_1167_, lean_object* v___x_1168_, lean_object* v___x_1169_, lean_object* v_x_1170_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1171_; uint8_t v___x_36395__boxed_1172_; uint8_t v_res_1173_; lean_object* v_r_1174_; 
v_suppressElabErrors_boxed_1171_ = lean_unbox(v_suppressElabErrors_1167_);
v___x_36395__boxed_1172_ = lean_unbox(v___x_1168_);
v_res_1173_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0(v_suppressElabErrors_boxed_1171_, v___x_36395__boxed_1172_, v___x_1169_, v_x_1170_);
lean_dec(v_x_1170_);
lean_dec_ref(v___x_1169_);
v_r_1174_ = lean_box(v_res_1173_);
return v_r_1174_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0(void){
_start:
{
lean_object* v___x_1175_; double v___x_1176_; 
v___x_1175_ = lean_unsigned_to_nat(0u);
v___x_1176_ = lean_float_of_nat(v___x_1175_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(uint8_t v___x_1178_, lean_object* v_as_1179_, size_t v_sz_1180_, size_t v_i_1181_, lean_object* v_b_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v_a_1187_; uint8_t v___x_1191_; 
v___x_1191_ = lean_usize_dec_lt(v_i_1181_, v_sz_1180_);
if (v___x_1191_ == 0)
{
lean_object* v___x_1192_; 
v___x_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1192_, 0, v_b_1182_);
return v___x_1192_;
}
else
{
lean_object* v_a_1193_; lean_object* v_fst_1194_; lean_object* v_snd_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1273_; 
v_a_1193_ = lean_array_uget(v_as_1179_, v_i_1181_);
v_fst_1194_ = lean_ctor_get(v_a_1193_, 0);
v_snd_1195_ = lean_ctor_get(v_a_1193_, 1);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_a_1193_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1197_ = v_a_1193_;
v_isShared_1198_ = v_isSharedCheck_1273_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_snd_1195_);
lean_inc(v_fst_1194_);
lean_dec(v_a_1193_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1273_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v_fst_1199_; lean_object* v_snd_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1272_; 
v_fst_1199_ = lean_ctor_get(v_fst_1194_, 0);
v_snd_1200_ = lean_ctor_get(v_fst_1194_, 1);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_fst_1194_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1202_ = v_fst_1194_;
v_isShared_1203_ = v_isSharedCheck_1272_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_snd_1200_);
lean_inc(v_fst_1199_);
lean_dec(v_fst_1194_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1272_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; double v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v_toCold_1209_; uint8_t v_suppressElabErrors_1210_; lean_object* v_fileName_1211_; lean_object* v_fileMap_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1219_; 
v___x_1204_ = lean_box(0);
v___x_1205_ = lean_box(0);
v___x_1206_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0);
v___x_1207_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1));
v___x_1208_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1208_, 0, v___x_1204_);
lean_ctor_set(v___x_1208_, 1, v___x_1205_);
lean_ctor_set(v___x_1208_, 2, v___x_1207_);
lean_ctor_set_float(v___x_1208_, sizeof(void*)*3, v___x_1206_);
lean_ctor_set_float(v___x_1208_, sizeof(void*)*3 + 8, v___x_1206_);
lean_ctor_set_uint8(v___x_1208_, sizeof(void*)*3 + 16, v___x_1191_);
v_toCold_1209_ = lean_ctor_get(v___y_1183_, 0);
v_suppressElabErrors_1210_ = lean_ctor_get_uint8(v___y_1183_, sizeof(void*)*3 + 1);
v_fileName_1211_ = lean_ctor_get(v_toCold_1209_, 0);
v_fileMap_1212_ = lean_ctor_get(v_toCold_1209_, 1);
v___x_1213_ = lean_box(0);
v___x_1214_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_1215_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_1216_ = l_Lean_MessageData_nil;
v___x_1217_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1208_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
lean_ctor_set(v___x_1217_, 2, v_snd_1195_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set_tag(v___x_1202_, 8);
lean_ctor_set(v___x_1202_, 1, v___x_1217_);
lean_ctor_set(v___x_1202_, 0, v___x_1215_);
v___x_1219_ = v___x_1202_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1215_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v___x_1217_);
v___x_1219_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
uint8_t v___x_1220_; lean_object* v___x_1221_; lean_object* v___y_1223_; lean_object* v___y_1224_; 
v___x_1220_ = 0;
lean_inc_ref(v_fileMap_1212_);
lean_inc_ref(v_fileName_1211_);
v___x_1221_ = l_Lean_Elab_mkMessageCore(v_fileName_1211_, v_fileMap_1212_, v___x_1219_, v___x_1220_, v_fst_1199_, v_snd_1200_);
lean_dec(v_snd_1200_);
lean_dec(v_fst_1199_);
if (v_suppressElabErrors_1210_ == 0)
{
v___y_1223_ = v___y_1183_;
v___y_1224_ = v___y_1184_;
goto v___jp_1222_;
}
else
{
lean_object* v_data_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___f_1269_; uint8_t v___x_1270_; 
v_data_1266_ = lean_ctor_get(v___x_1221_, 4);
lean_inc(v_data_1266_);
v___x_1267_ = lean_box(v_suppressElabErrors_1210_);
v___x_1268_ = lean_box(v___x_1178_);
v___f_1269_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1269_, 0, v___x_1267_);
lean_closure_set(v___f_1269_, 1, v___x_1268_);
lean_closure_set(v___f_1269_, 2, v___x_1214_);
v___x_1270_ = l_Lean_MessageData_hasTag(v___f_1269_, v_data_1266_);
if (v___x_1270_ == 0)
{
lean_dec_ref(v___x_1221_);
lean_del_object(v___x_1197_);
v_a_1187_ = v___x_1213_;
goto v___jp_1186_;
}
else
{
v___y_1223_ = v___y_1183_;
v___y_1224_ = v___y_1184_;
goto v___jp_1222_;
}
}
v___jp_1222_:
{
lean_object* v___x_1225_; lean_object* v_toCold_1226_; lean_object* v_fileName_1227_; lean_object* v_pos_1228_; lean_object* v_endPos_1229_; uint8_t v_keepFullRange_1230_; uint8_t v_severity_1231_; uint8_t v_isSilent_1232_; lean_object* v_caption_1233_; lean_object* v_data_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1265_; 
v___x_1225_ = lean_st_ref_take(v___y_1224_);
v_toCold_1226_ = lean_ctor_get(v___y_1223_, 0);
v_fileName_1227_ = lean_ctor_get(v___x_1221_, 0);
v_pos_1228_ = lean_ctor_get(v___x_1221_, 1);
v_endPos_1229_ = lean_ctor_get(v___x_1221_, 2);
v_keepFullRange_1230_ = lean_ctor_get_uint8(v___x_1221_, sizeof(void*)*5);
v_severity_1231_ = lean_ctor_get_uint8(v___x_1221_, sizeof(void*)*5 + 1);
v_isSilent_1232_ = lean_ctor_get_uint8(v___x_1221_, sizeof(void*)*5 + 2);
v_caption_1233_ = lean_ctor_get(v___x_1221_, 3);
v_data_1234_ = lean_ctor_get(v___x_1221_, 4);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1236_ = v___x_1221_;
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
lean_dec(v___x_1221_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1265_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v_currNamespace_1238_; lean_object* v_openDecls_1239_; lean_object* v_env_1240_; lean_object* v_nextMacroScope_1241_; lean_object* v_ngen_1242_; lean_object* v_auxDeclNGen_1243_; lean_object* v_traceState_1244_; lean_object* v_cache_1245_; lean_object* v_messages_1246_; lean_object* v_infoState_1247_; lean_object* v_snapshotTasks_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1264_; 
v_currNamespace_1238_ = lean_ctor_get(v_toCold_1226_, 4);
v_openDecls_1239_ = lean_ctor_get(v_toCold_1226_, 5);
v_env_1240_ = lean_ctor_get(v___x_1225_, 0);
v_nextMacroScope_1241_ = lean_ctor_get(v___x_1225_, 1);
v_ngen_1242_ = lean_ctor_get(v___x_1225_, 2);
v_auxDeclNGen_1243_ = lean_ctor_get(v___x_1225_, 3);
v_traceState_1244_ = lean_ctor_get(v___x_1225_, 4);
v_cache_1245_ = lean_ctor_get(v___x_1225_, 5);
v_messages_1246_ = lean_ctor_get(v___x_1225_, 6);
v_infoState_1247_ = lean_ctor_get(v___x_1225_, 7);
v_snapshotTasks_1248_ = lean_ctor_get(v___x_1225_, 8);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1250_ = v___x_1225_;
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
lean_dec(v___x_1225_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1264_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
lean_inc(v_openDecls_1239_);
lean_inc(v_currNamespace_1238_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 1, v_openDecls_1239_);
lean_ctor_set(v___x_1197_, 0, v_currNamespace_1238_);
v___x_1253_ = v___x_1197_;
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
v___x_1260_ = lean_st_ref_put(v___y_1224_, v___x_1259_);
v_a_1187_ = v___x_1213_;
goto v___jp_1186_;
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
v___jp_1186_:
{
size_t v___x_1188_; size_t v___x_1189_; 
v___x_1188_ = ((size_t)1ULL);
v___x_1189_ = lean_usize_add(v_i_1181_, v___x_1188_);
v_i_1181_ = v___x_1189_;
v_b_1182_ = v_a_1187_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___boxed(lean_object* v___x_1274_, lean_object* v_as_1275_, lean_object* v_sz_1276_, lean_object* v_i_1277_, lean_object* v_b_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
uint8_t v___x_36468__boxed_1282_; size_t v_sz_boxed_1283_; size_t v_i_boxed_1284_; lean_object* v_res_1285_; 
v___x_36468__boxed_1282_ = lean_unbox(v___x_1274_);
v_sz_boxed_1283_ = lean_unbox_usize(v_sz_1276_);
lean_dec(v_sz_1276_);
v_i_boxed_1284_ = lean_unbox_usize(v_i_1277_);
lean_dec(v_i_1277_);
v_res_1285_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(v___x_36468__boxed_1282_, v_as_1275_, v_sz_boxed_1283_, v_i_boxed_1284_, v_b_1278_, v___y_1279_, v___y_1280_);
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
lean_object* v_key_1308_; lean_object* v_value_1309_; lean_object* v_tail_1310_; lean_object* v_fst_1311_; lean_object* v_snd_1312_; lean_object* v_fst_1313_; lean_object* v_snd_1314_; uint8_t v_decide_1315_; 
v_key_1308_ = lean_ctor_get(v_x_1307_, 0);
v_value_1309_ = lean_ctor_get(v_x_1307_, 1);
v_tail_1310_ = lean_ctor_get(v_x_1307_, 2);
v_fst_1311_ = lean_ctor_get(v_key_1308_, 0);
v_snd_1312_ = lean_ctor_get(v_key_1308_, 1);
v_fst_1313_ = lean_ctor_get(v_a_1305_, 0);
v_snd_1314_ = lean_ctor_get(v_a_1305_, 1);
v_decide_1315_ = lean_nat_dec_eq(v_fst_1311_, v_fst_1313_);
if (v_decide_1315_ == 0)
{
v_x_1307_ = v_tail_1310_;
goto _start;
}
else
{
uint8_t v_decide_1317_; 
v_decide_1317_ = lean_nat_dec_eq(v_snd_1312_, v_snd_1314_);
if (v_decide_1317_ == 0)
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg___boxed(lean_object* v_a_1319_, lean_object* v_fallback_1320_, lean_object* v_x_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_1319_, v_fallback_1320_, v_x_1321_);
lean_dec(v_x_1321_);
lean_dec(v_fallback_1320_);
lean_dec_ref(v_a_1319_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(lean_object* v_m_1323_, lean_object* v_a_1324_, lean_object* v_fallback_1325_){
_start:
{
lean_object* v_buckets_1326_; lean_object* v_fst_1327_; lean_object* v_snd_1328_; lean_object* v___x_1329_; uint64_t v___x_1330_; uint64_t v___x_1331_; uint64_t v___x_1332_; uint64_t v___x_1333_; uint64_t v___x_1334_; uint64_t v_fold_1335_; uint64_t v___x_1336_; uint64_t v___x_1337_; uint64_t v___x_1338_; size_t v___x_1339_; size_t v___x_1340_; size_t v___x_1341_; size_t v___x_1342_; size_t v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v_buckets_1326_ = lean_ctor_get(v_m_1323_, 1);
v_fst_1327_ = lean_ctor_get(v_a_1324_, 0);
v_snd_1328_ = lean_ctor_get(v_a_1324_, 1);
v___x_1329_ = lean_array_get_size(v_buckets_1326_);
v___x_1330_ = l_String_instHashableRaw_hash(v_fst_1327_);
v___x_1331_ = l_String_instHashableRaw_hash(v_snd_1328_);
v___x_1332_ = lean_uint64_mix_hash(v___x_1330_, v___x_1331_);
v___x_1333_ = 32ULL;
v___x_1334_ = lean_uint64_shift_right(v___x_1332_, v___x_1333_);
v_fold_1335_ = lean_uint64_xor(v___x_1332_, v___x_1334_);
v___x_1336_ = 16ULL;
v___x_1337_ = lean_uint64_shift_right(v_fold_1335_, v___x_1336_);
v___x_1338_ = lean_uint64_xor(v_fold_1335_, v___x_1337_);
v___x_1339_ = lean_uint64_to_usize(v___x_1338_);
v___x_1340_ = lean_usize_of_nat(v___x_1329_);
v___x_1341_ = ((size_t)1ULL);
v___x_1342_ = lean_usize_sub(v___x_1340_, v___x_1341_);
v___x_1343_ = lean_usize_land(v___x_1339_, v___x_1342_);
v___x_1344_ = lean_array_uget_borrowed(v_buckets_1326_, v___x_1343_);
v___x_1345_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_1324_, v_fallback_1325_, v___x_1344_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg___boxed(lean_object* v_m_1346_, lean_object* v_a_1347_, lean_object* v_fallback_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_m_1346_, v_a_1347_, v_fallback_1348_);
lean_dec(v_fallback_1348_);
lean_dec_ref(v_a_1347_);
lean_dec_ref(v_m_1346_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(lean_object* v_x_1350_, lean_object* v_x_1351_){
_start:
{
if (lean_obj_tag(v_x_1351_) == 0)
{
return v_x_1350_;
}
else
{
lean_object* v_key_1352_; lean_object* v_value_1353_; lean_object* v_tail_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1381_; 
v_key_1352_ = lean_ctor_get(v_x_1351_, 0);
v_value_1353_ = lean_ctor_get(v_x_1351_, 1);
v_tail_1354_ = lean_ctor_get(v_x_1351_, 2);
v_isSharedCheck_1381_ = !lean_is_exclusive(v_x_1351_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1356_ = v_x_1351_;
v_isShared_1357_ = v_isSharedCheck_1381_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_tail_1354_);
lean_inc(v_value_1353_);
lean_inc(v_key_1352_);
lean_dec(v_x_1351_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1381_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v_fst_1358_; lean_object* v_snd_1359_; lean_object* v___x_1360_; uint64_t v___x_1361_; uint64_t v___x_1362_; uint64_t v___x_1363_; uint64_t v___x_1364_; uint64_t v___x_1365_; uint64_t v_fold_1366_; uint64_t v___x_1367_; uint64_t v___x_1368_; uint64_t v___x_1369_; size_t v___x_1370_; size_t v___x_1371_; size_t v___x_1372_; size_t v___x_1373_; size_t v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1377_; 
v_fst_1358_ = lean_ctor_get(v_key_1352_, 0);
v_snd_1359_ = lean_ctor_get(v_key_1352_, 1);
v___x_1360_ = lean_array_get_size(v_x_1350_);
v___x_1361_ = l_String_instHashableRaw_hash(v_fst_1358_);
v___x_1362_ = l_String_instHashableRaw_hash(v_snd_1359_);
v___x_1363_ = lean_uint64_mix_hash(v___x_1361_, v___x_1362_);
v___x_1364_ = 32ULL;
v___x_1365_ = lean_uint64_shift_right(v___x_1363_, v___x_1364_);
v_fold_1366_ = lean_uint64_xor(v___x_1363_, v___x_1365_);
v___x_1367_ = 16ULL;
v___x_1368_ = lean_uint64_shift_right(v_fold_1366_, v___x_1367_);
v___x_1369_ = lean_uint64_xor(v_fold_1366_, v___x_1368_);
v___x_1370_ = lean_uint64_to_usize(v___x_1369_);
v___x_1371_ = lean_usize_of_nat(v___x_1360_);
v___x_1372_ = ((size_t)1ULL);
v___x_1373_ = lean_usize_sub(v___x_1371_, v___x_1372_);
v___x_1374_ = lean_usize_land(v___x_1370_, v___x_1373_);
v___x_1375_ = lean_array_uget_borrowed(v_x_1350_, v___x_1374_);
lean_inc(v___x_1375_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 2, v___x_1375_);
v___x_1377_ = v___x_1356_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_key_1352_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v_value_1353_);
lean_ctor_set(v_reuseFailAlloc_1380_, 2, v___x_1375_);
v___x_1377_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
lean_object* v___x_1378_; 
v___x_1378_ = lean_array_uset(v_x_1350_, v___x_1374_, v___x_1377_);
v_x_1350_ = v___x_1378_;
v_x_1351_ = v_tail_1354_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(lean_object* v_i_1382_, lean_object* v_source_1383_, lean_object* v_target_1384_){
_start:
{
lean_object* v___x_1385_; uint8_t v___x_1386_; 
v___x_1385_ = lean_array_get_size(v_source_1383_);
v___x_1386_ = lean_nat_dec_lt(v_i_1382_, v___x_1385_);
if (v___x_1386_ == 0)
{
lean_dec_ref(v_source_1383_);
lean_dec(v_i_1382_);
return v_target_1384_;
}
else
{
lean_object* v_es_1387_; lean_object* v___x_1388_; lean_object* v_source_1389_; lean_object* v_target_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v_es_1387_ = lean_array_fget(v_source_1383_, v_i_1382_);
v___x_1388_ = lean_box(0);
v_source_1389_ = lean_array_fset(v_source_1383_, v_i_1382_, v___x_1388_);
v_target_1390_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(v_target_1384_, v_es_1387_);
v___x_1391_ = lean_unsigned_to_nat(1u);
v___x_1392_ = lean_nat_add(v_i_1382_, v___x_1391_);
lean_dec(v_i_1382_);
v_i_1382_ = v___x_1392_;
v_source_1383_ = v_source_1389_;
v_target_1384_ = v_target_1390_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(lean_object* v_data_1394_){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v_nbuckets_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1395_ = lean_array_get_size(v_data_1394_);
v___x_1396_ = lean_unsigned_to_nat(2u);
v_nbuckets_1397_ = lean_nat_mul(v___x_1395_, v___x_1396_);
v___x_1398_ = lean_unsigned_to_nat(0u);
v___x_1399_ = lean_box(0);
v___x_1400_ = lean_mk_array(v_nbuckets_1397_, v___x_1399_);
v___x_1401_ = lean_array_propagate_mark(v_data_1394_, v___x_1400_);
v___x_1402_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(v___x_1398_, v_data_1394_, v___x_1401_);
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
lean_object* v_key_1406_; lean_object* v_value_1407_; lean_object* v_tail_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1424_; 
v_key_1406_ = lean_ctor_get(v_x_1405_, 0);
v_value_1407_ = lean_ctor_get(v_x_1405_, 1);
v_tail_1408_ = lean_ctor_get(v_x_1405_, 2);
v_isSharedCheck_1424_ = !lean_is_exclusive(v_x_1405_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1410_ = v_x_1405_;
v_isShared_1411_ = v_isSharedCheck_1424_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_tail_1408_);
lean_inc(v_value_1407_);
lean_inc(v_key_1406_);
lean_dec(v_x_1405_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1424_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v_fst_1417_; lean_object* v_snd_1418_; lean_object* v_fst_1419_; lean_object* v_snd_1420_; uint8_t v_decide_1421_; 
v_fst_1417_ = lean_ctor_get(v_key_1406_, 0);
v_snd_1418_ = lean_ctor_get(v_key_1406_, 1);
v_fst_1419_ = lean_ctor_get(v_a_1403_, 0);
v_snd_1420_ = lean_ctor_get(v_a_1403_, 1);
v_decide_1421_ = lean_nat_dec_eq(v_fst_1417_, v_fst_1419_);
if (v_decide_1421_ == 0)
{
goto v___jp_1412_;
}
else
{
uint8_t v_decide_1422_; 
v_decide_1422_ = lean_nat_dec_eq(v_snd_1418_, v_snd_1420_);
if (v_decide_1422_ == 0)
{
goto v___jp_1412_;
}
else
{
lean_object* v___x_1423_; 
lean_del_object(v___x_1410_);
lean_dec(v_value_1407_);
lean_dec(v_key_1406_);
v___x_1423_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1423_, 0, v_a_1403_);
lean_ctor_set(v___x_1423_, 1, v_b_1404_);
lean_ctor_set(v___x_1423_, 2, v_tail_1408_);
return v___x_1423_;
}
}
v___jp_1412_:
{
lean_object* v___x_1413_; lean_object* v___x_1415_; 
v___x_1413_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_1403_, v_b_1404_, v_tail_1408_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 2, v___x_1413_);
v___x_1415_ = v___x_1410_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_key_1406_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_value_1407_);
lean_ctor_set(v_reuseFailAlloc_1416_, 2, v___x_1413_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(lean_object* v_a_1425_, lean_object* v_x_1426_){
_start:
{
if (lean_obj_tag(v_x_1426_) == 0)
{
uint8_t v___x_1427_; 
v___x_1427_ = 0;
return v___x_1427_;
}
else
{
lean_object* v_key_1428_; lean_object* v_tail_1429_; lean_object* v_fst_1430_; lean_object* v_snd_1431_; lean_object* v_fst_1432_; lean_object* v_snd_1433_; uint8_t v_decide_1434_; 
v_key_1428_ = lean_ctor_get(v_x_1426_, 0);
v_tail_1429_ = lean_ctor_get(v_x_1426_, 2);
v_fst_1430_ = lean_ctor_get(v_key_1428_, 0);
v_snd_1431_ = lean_ctor_get(v_key_1428_, 1);
v_fst_1432_ = lean_ctor_get(v_a_1425_, 0);
v_snd_1433_ = lean_ctor_get(v_a_1425_, 1);
v_decide_1434_ = lean_nat_dec_eq(v_fst_1430_, v_fst_1432_);
if (v_decide_1434_ == 0)
{
v_x_1426_ = v_tail_1429_;
goto _start;
}
else
{
uint8_t v_decide_1436_; 
v_decide_1436_ = lean_nat_dec_eq(v_snd_1431_, v_snd_1433_);
if (v_decide_1436_ == 0)
{
v_x_1426_ = v_tail_1429_;
goto _start;
}
else
{
return v_decide_1436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg___boxed(lean_object* v_a_1438_, lean_object* v_x_1439_){
_start:
{
uint8_t v_res_1440_; lean_object* v_r_1441_; 
v_res_1440_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_1438_, v_x_1439_);
lean_dec(v_x_1439_);
lean_dec_ref(v_a_1438_);
v_r_1441_ = lean_box(v_res_1440_);
return v_r_1441_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(lean_object* v_m_1442_, lean_object* v_a_1443_, lean_object* v_b_1444_){
_start:
{
lean_object* v_size_1445_; lean_object* v_buckets_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1493_; 
v_size_1445_ = lean_ctor_get(v_m_1442_, 0);
v_buckets_1446_ = lean_ctor_get(v_m_1442_, 1);
v_isSharedCheck_1493_ = !lean_is_exclusive(v_m_1442_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1448_ = v_m_1442_;
v_isShared_1449_ = v_isSharedCheck_1493_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_buckets_1446_);
lean_inc(v_size_1445_);
lean_dec(v_m_1442_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1493_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v_fst_1450_; lean_object* v_snd_1451_; lean_object* v___x_1452_; uint64_t v___x_1453_; uint64_t v___x_1454_; uint64_t v___x_1455_; uint64_t v___x_1456_; uint64_t v___x_1457_; uint64_t v_fold_1458_; uint64_t v___x_1459_; uint64_t v___x_1460_; uint64_t v___x_1461_; size_t v___x_1462_; size_t v___x_1463_; size_t v___x_1464_; size_t v___x_1465_; size_t v___x_1466_; lean_object* v_bkt_1467_; uint8_t v___x_1468_; 
v_fst_1450_ = lean_ctor_get(v_a_1443_, 0);
v_snd_1451_ = lean_ctor_get(v_a_1443_, 1);
v___x_1452_ = lean_array_get_size(v_buckets_1446_);
v___x_1453_ = l_String_instHashableRaw_hash(v_fst_1450_);
v___x_1454_ = l_String_instHashableRaw_hash(v_snd_1451_);
v___x_1455_ = lean_uint64_mix_hash(v___x_1453_, v___x_1454_);
v___x_1456_ = 32ULL;
v___x_1457_ = lean_uint64_shift_right(v___x_1455_, v___x_1456_);
v_fold_1458_ = lean_uint64_xor(v___x_1455_, v___x_1457_);
v___x_1459_ = 16ULL;
v___x_1460_ = lean_uint64_shift_right(v_fold_1458_, v___x_1459_);
v___x_1461_ = lean_uint64_xor(v_fold_1458_, v___x_1460_);
v___x_1462_ = lean_uint64_to_usize(v___x_1461_);
v___x_1463_ = lean_usize_of_nat(v___x_1452_);
v___x_1464_ = ((size_t)1ULL);
v___x_1465_ = lean_usize_sub(v___x_1463_, v___x_1464_);
v___x_1466_ = lean_usize_land(v___x_1462_, v___x_1465_);
v_bkt_1467_ = lean_array_uget_borrowed(v_buckets_1446_, v___x_1466_);
v___x_1468_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_1443_, v_bkt_1467_);
if (v___x_1468_ == 0)
{
lean_object* v___x_1469_; lean_object* v_size_x27_1470_; lean_object* v___x_1471_; lean_object* v_buckets_x27_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; uint8_t v___x_1478_; 
v___x_1469_ = lean_unsigned_to_nat(1u);
v_size_x27_1470_ = lean_nat_add(v_size_1445_, v___x_1469_);
lean_dec(v_size_1445_);
lean_inc(v_bkt_1467_);
v___x_1471_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1471_, 0, v_a_1443_);
lean_ctor_set(v___x_1471_, 1, v_b_1444_);
lean_ctor_set(v___x_1471_, 2, v_bkt_1467_);
v_buckets_x27_1472_ = lean_array_uset(v_buckets_1446_, v___x_1466_, v___x_1471_);
v___x_1473_ = lean_unsigned_to_nat(4u);
v___x_1474_ = lean_nat_mul(v_size_x27_1470_, v___x_1473_);
v___x_1475_ = lean_unsigned_to_nat(3u);
v___x_1476_ = lean_nat_div(v___x_1474_, v___x_1475_);
lean_dec(v___x_1474_);
v___x_1477_ = lean_array_get_size(v_buckets_x27_1472_);
v___x_1478_ = lean_nat_dec_le(v___x_1476_, v___x_1477_);
lean_dec(v___x_1476_);
if (v___x_1478_ == 0)
{
lean_object* v_val_1479_; lean_object* v___x_1481_; 
v_val_1479_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(v_buckets_x27_1472_);
if (v_isShared_1449_ == 0)
{
lean_ctor_set(v___x_1448_, 1, v_val_1479_);
lean_ctor_set(v___x_1448_, 0, v_size_x27_1470_);
v___x_1481_ = v___x_1448_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_size_x27_1470_);
lean_ctor_set(v_reuseFailAlloc_1482_, 1, v_val_1479_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
else
{
lean_object* v___x_1484_; 
if (v_isShared_1449_ == 0)
{
lean_ctor_set(v___x_1448_, 1, v_buckets_x27_1472_);
lean_ctor_set(v___x_1448_, 0, v_size_x27_1470_);
v___x_1484_ = v___x_1448_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_size_x27_1470_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v_buckets_x27_1472_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
else
{
lean_object* v___x_1486_; lean_object* v_buckets_x27_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1491_; 
lean_inc(v_bkt_1467_);
v___x_1486_ = lean_box(0);
v_buckets_x27_1487_ = lean_array_uset(v_buckets_1446_, v___x_1466_, v___x_1486_);
v___x_1488_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_1443_, v_b_1444_, v_bkt_1467_);
v___x_1489_ = lean_array_uset(v_buckets_x27_1487_, v___x_1466_, v___x_1488_);
if (v_isShared_1449_ == 0)
{
lean_ctor_set(v___x_1448_, 1, v___x_1489_);
v___x_1491_ = v___x_1448_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_size_1445_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v___x_1489_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(uint8_t v___x_1496_, lean_object* v_as_1497_, size_t v_sz_1498_, size_t v_i_1499_, lean_object* v_b_1500_, lean_object* v___y_1501_){
_start:
{
uint8_t v___x_1503_; 
v___x_1503_ = lean_usize_dec_lt(v_i_1499_, v_sz_1498_);
if (v___x_1503_ == 0)
{
lean_object* v___x_1504_; 
v___x_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1504_, 0, v_b_1500_);
return v___x_1504_;
}
else
{
lean_object* v_snd_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1542_; 
v_snd_1505_ = lean_ctor_get(v_b_1500_, 1);
v_isSharedCheck_1542_ = !lean_is_exclusive(v_b_1500_);
if (v_isSharedCheck_1542_ == 0)
{
lean_object* v_unused_1543_; 
v_unused_1543_ = lean_ctor_get(v_b_1500_, 0);
lean_dec(v_unused_1543_);
v___x_1507_ = v_b_1500_;
v_isShared_1508_ = v_isSharedCheck_1542_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_snd_1505_);
lean_dec(v_b_1500_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1542_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v_ref_1509_; lean_object* v_a_1510_; lean_object* v_ref_1511_; lean_object* v_msg_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1541_; 
v_ref_1509_ = lean_ctor_get(v___y_1501_, 2);
v_a_1510_ = lean_array_uget(v_as_1497_, v_i_1499_);
v_ref_1511_ = lean_ctor_get(v_a_1510_, 0);
v_msg_1512_ = lean_ctor_get(v_a_1510_, 1);
v_isSharedCheck_1541_ = !lean_is_exclusive(v_a_1510_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1514_ = v_a_1510_;
v_isShared_1515_ = v_isSharedCheck_1541_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_msg_1512_);
lean_inc(v_ref_1511_);
lean_dec(v_a_1510_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1541_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1516_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v_ref_1533_; lean_object* v___y_1535_; lean_object* v___x_1538_; 
v___x_1516_ = lean_box(0);
v_ref_1533_ = l_Lean_replaceRef(v_ref_1511_, v_ref_1509_);
lean_dec(v_ref_1511_);
v___x_1538_ = l_Lean_Syntax_getPos_x3f(v_ref_1533_, v___x_1496_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v___x_1539_; 
v___x_1539_ = lean_unsigned_to_nat(0u);
v___y_1535_ = v___x_1539_;
goto v___jp_1534_;
}
else
{
lean_object* v_val_1540_; 
v_val_1540_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_val_1540_);
lean_dec_ref_known(v___x_1538_, 1);
v___y_1535_ = v_val_1540_;
goto v___jp_1534_;
}
v___jp_1517_:
{
lean_object* v___x_1521_; 
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 1, v___y_1519_);
lean_ctor_set(v___x_1507_, 0, v___y_1518_);
v___x_1521_ = v___x_1507_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___y_1518_);
lean_ctor_set(v_reuseFailAlloc_1532_, 1, v___y_1519_);
v___x_1521_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v_pos2traces_1525_; lean_object* v___x_1527_; 
v___x_1522_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1523_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1505_, v___x_1521_, v___x_1522_);
v___x_1524_ = lean_array_push(v___x_1523_, v_msg_1512_);
v_pos2traces_1525_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1505_, v___x_1521_, v___x_1524_);
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 1, v_pos2traces_1525_);
lean_ctor_set(v___x_1514_, 0, v___x_1516_);
v___x_1527_ = v___x_1514_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1516_);
lean_ctor_set(v_reuseFailAlloc_1531_, 1, v_pos2traces_1525_);
v___x_1527_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
size_t v___x_1528_; size_t v___x_1529_; 
v___x_1528_ = ((size_t)1ULL);
v___x_1529_ = lean_usize_add(v_i_1499_, v___x_1528_);
v_i_1499_ = v___x_1529_;
v_b_1500_ = v___x_1527_;
goto _start;
}
}
}
v___jp_1534_:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1533_, v___x_1496_);
lean_dec(v_ref_1533_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_inc(v___y_1535_);
v___y_1518_ = v___y_1535_;
v___y_1519_ = v___y_1535_;
goto v___jp_1517_;
}
else
{
lean_object* v_val_1537_; 
v_val_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_val_1537_);
lean_dec_ref_known(v___x_1536_, 1);
v___y_1518_ = v___y_1535_;
v___y_1519_ = v_val_1537_;
goto v___jp_1517_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___boxed(lean_object* v___x_1544_, lean_object* v_as_1545_, lean_object* v_sz_1546_, lean_object* v_i_1547_, lean_object* v_b_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
uint8_t v___x_36939__boxed_1551_; size_t v_sz_boxed_1552_; size_t v_i_boxed_1553_; lean_object* v_res_1554_; 
v___x_36939__boxed_1551_ = lean_unbox(v___x_1544_);
v_sz_boxed_1552_ = lean_unbox_usize(v_sz_1546_);
lean_dec(v_sz_1546_);
v_i_boxed_1553_ = lean_unbox_usize(v_i_1547_);
lean_dec(v_i_1547_);
v_res_1554_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_36939__boxed_1551_, v_as_1545_, v_sz_boxed_1552_, v_i_boxed_1553_, v_b_1548_, v___y_1549_);
lean_dec_ref(v___y_1549_);
lean_dec_ref(v_as_1545_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(uint8_t v___x_1555_, lean_object* v_as_1556_, size_t v_sz_1557_, size_t v_i_1558_, lean_object* v_b_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
uint8_t v___x_1563_; 
v___x_1563_ = lean_usize_dec_lt(v_i_1558_, v_sz_1557_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1564_; 
v___x_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1564_, 0, v_b_1559_);
return v___x_1564_;
}
else
{
lean_object* v_snd_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1602_; 
v_snd_1565_ = lean_ctor_get(v_b_1559_, 1);
v_isSharedCheck_1602_ = !lean_is_exclusive(v_b_1559_);
if (v_isSharedCheck_1602_ == 0)
{
lean_object* v_unused_1603_; 
v_unused_1603_ = lean_ctor_get(v_b_1559_, 0);
lean_dec(v_unused_1603_);
v___x_1567_ = v_b_1559_;
v_isShared_1568_ = v_isSharedCheck_1602_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_snd_1565_);
lean_dec(v_b_1559_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1602_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v_ref_1569_; lean_object* v_a_1570_; lean_object* v_ref_1571_; lean_object* v_msg_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1601_; 
v_ref_1569_ = lean_ctor_get(v___y_1560_, 2);
v_a_1570_ = lean_array_uget(v_as_1556_, v_i_1558_);
v_ref_1571_ = lean_ctor_get(v_a_1570_, 0);
v_msg_1572_ = lean_ctor_get(v_a_1570_, 1);
v_isSharedCheck_1601_ = !lean_is_exclusive(v_a_1570_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1574_ = v_a_1570_;
v_isShared_1575_ = v_isSharedCheck_1601_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_msg_1572_);
lean_inc(v_ref_1571_);
lean_dec(v_a_1570_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1601_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1576_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v_ref_1593_; lean_object* v___y_1595_; lean_object* v___x_1598_; 
v___x_1576_ = lean_box(0);
v_ref_1593_ = l_Lean_replaceRef(v_ref_1571_, v_ref_1569_);
lean_dec(v_ref_1571_);
v___x_1598_ = l_Lean_Syntax_getPos_x3f(v_ref_1593_, v___x_1555_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v___x_1599_; 
v___x_1599_ = lean_unsigned_to_nat(0u);
v___y_1595_ = v___x_1599_;
goto v___jp_1594_;
}
else
{
lean_object* v_val_1600_; 
v_val_1600_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_val_1600_);
lean_dec_ref_known(v___x_1598_, 1);
v___y_1595_ = v_val_1600_;
goto v___jp_1594_;
}
v___jp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 1, v___y_1579_);
lean_ctor_set(v___x_1567_, 0, v___y_1578_);
v___x_1581_ = v___x_1567_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___y_1578_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v___y_1579_);
v___x_1581_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v_pos2traces_1585_; lean_object* v___x_1587_; 
v___x_1582_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1583_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1565_, v___x_1581_, v___x_1582_);
v___x_1584_ = lean_array_push(v___x_1583_, v_msg_1572_);
v_pos2traces_1585_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1565_, v___x_1581_, v___x_1584_);
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 1, v_pos2traces_1585_);
lean_ctor_set(v___x_1574_, 0, v___x_1576_);
v___x_1587_ = v___x_1574_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1576_);
lean_ctor_set(v_reuseFailAlloc_1591_, 1, v_pos2traces_1585_);
v___x_1587_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
size_t v___x_1588_; size_t v___x_1589_; lean_object* v___x_1590_; 
v___x_1588_ = ((size_t)1ULL);
v___x_1589_ = lean_usize_add(v_i_1558_, v___x_1588_);
v___x_1590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_1555_, v_as_1556_, v_sz_1557_, v___x_1589_, v___x_1587_, v___y_1560_);
return v___x_1590_;
}
}
}
v___jp_1594_:
{
lean_object* v___x_1596_; 
v___x_1596_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1593_, v___x_1555_);
lean_dec(v_ref_1593_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_inc(v___y_1595_);
v___y_1578_ = v___y_1595_;
v___y_1579_ = v___y_1595_;
goto v___jp_1577_;
}
else
{
lean_object* v_val_1597_; 
v_val_1597_ = lean_ctor_get(v___x_1596_, 0);
lean_inc(v_val_1597_);
lean_dec_ref_known(v___x_1596_, 1);
v___y_1578_ = v___y_1595_;
v___y_1579_ = v_val_1597_;
goto v___jp_1577_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40___boxed(lean_object* v___x_1604_, lean_object* v_as_1605_, lean_object* v_sz_1606_, lean_object* v_i_1607_, lean_object* v_b_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
uint8_t v___x_37020__boxed_1612_; size_t v_sz_boxed_1613_; size_t v_i_boxed_1614_; lean_object* v_res_1615_; 
v___x_37020__boxed_1612_ = lean_unbox(v___x_1604_);
v_sz_boxed_1613_ = lean_unbox_usize(v_sz_1606_);
lean_dec(v_sz_1606_);
v_i_boxed_1614_ = lean_unbox_usize(v_i_1607_);
lean_dec(v_i_1607_);
v_res_1615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(v___x_37020__boxed_1612_, v_as_1605_, v_sz_boxed_1613_, v_i_boxed_1614_, v_b_1608_, v___y_1609_, v___y_1610_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec_ref(v_as_1605_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(lean_object* v_init_1616_, uint8_t v___x_1617_, lean_object* v_n_1618_, lean_object* v_b_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
if (lean_obj_tag(v_n_1618_) == 0)
{
lean_object* v_cs_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; size_t v_sz_1626_; size_t v___x_1627_; lean_object* v___x_1628_; 
v_cs_1623_ = lean_ctor_get(v_n_1618_, 0);
v___x_1624_ = lean_box(0);
v___x_1625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
lean_ctor_set(v___x_1625_, 1, v_b_1619_);
v_sz_1626_ = lean_array_size(v_cs_1623_);
v___x_1627_ = ((size_t)0ULL);
v___x_1628_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(v_init_1616_, v___x_1617_, v_cs_1623_, v_sz_1626_, v___x_1627_, v___x_1625_, v___y_1620_, v___y_1621_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1643_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1631_ = v___x_1628_;
v_isShared_1632_ = v_isSharedCheck_1643_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1628_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1643_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v_fst_1633_; 
v_fst_1633_ = lean_ctor_get(v_a_1629_, 0);
if (lean_obj_tag(v_fst_1633_) == 0)
{
lean_object* v_snd_1634_; lean_object* v___x_1635_; lean_object* v___x_1637_; 
v_snd_1634_ = lean_ctor_get(v_a_1629_, 1);
lean_inc(v_snd_1634_);
lean_dec(v_a_1629_);
v___x_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1635_, 0, v_snd_1634_);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v___x_1635_);
v___x_1637_ = v___x_1631_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1635_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
else
{
lean_object* v_val_1639_; lean_object* v___x_1641_; 
lean_inc_ref(v_fst_1633_);
lean_dec(v_a_1629_);
v_val_1639_ = lean_ctor_get(v_fst_1633_, 0);
lean_inc(v_val_1639_);
lean_dec_ref_known(v_fst_1633_, 1);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v_val_1639_);
v___x_1641_ = v___x_1631_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_val_1639_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
else
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
v_a_1644_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1646_ = v___x_1628_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1628_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1644_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
else
{
lean_object* v_vs_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; size_t v_sz_1655_; size_t v___x_1656_; lean_object* v___x_1657_; 
v_vs_1652_ = lean_ctor_get(v_n_1618_, 0);
v___x_1653_ = lean_box(0);
v___x_1654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
lean_ctor_set(v___x_1654_, 1, v_b_1619_);
v_sz_1655_ = lean_array_size(v_vs_1652_);
v___x_1656_ = ((size_t)0ULL);
v___x_1657_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(v___x_1617_, v_vs_1652_, v_sz_1655_, v___x_1656_, v___x_1654_, v___y_1620_, v___y_1621_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1672_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1660_ = v___x_1657_;
v_isShared_1661_ = v_isSharedCheck_1672_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1657_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1672_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v_fst_1662_; 
v_fst_1662_ = lean_ctor_get(v_a_1658_, 0);
if (lean_obj_tag(v_fst_1662_) == 0)
{
lean_object* v_snd_1663_; lean_object* v___x_1664_; lean_object* v___x_1666_; 
v_snd_1663_ = lean_ctor_get(v_a_1658_, 1);
lean_inc(v_snd_1663_);
lean_dec(v_a_1658_);
v___x_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1664_, 0, v_snd_1663_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 0, v___x_1664_);
v___x_1666_ = v___x_1660_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1664_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
else
{
lean_object* v_val_1668_; lean_object* v___x_1670_; 
lean_inc_ref(v_fst_1662_);
lean_dec(v_a_1658_);
v_val_1668_ = lean_ctor_get(v_fst_1662_, 0);
lean_inc(v_val_1668_);
lean_dec_ref_known(v_fst_1662_, 1);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 0, v_val_1668_);
v___x_1670_ = v___x_1660_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_val_1668_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
else
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
v_a_1673_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1657_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1657_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1673_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(lean_object* v_init_1681_, uint8_t v___x_1682_, lean_object* v_as_1683_, size_t v_sz_1684_, size_t v_i_1685_, lean_object* v_b_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
uint8_t v___x_1690_; 
v___x_1690_ = lean_usize_dec_lt(v_i_1685_, v_sz_1684_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; 
v___x_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1691_, 0, v_b_1686_);
return v___x_1691_;
}
else
{
lean_object* v_snd_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1726_; 
v_snd_1692_ = lean_ctor_get(v_b_1686_, 1);
v_isSharedCheck_1726_ = !lean_is_exclusive(v_b_1686_);
if (v_isSharedCheck_1726_ == 0)
{
lean_object* v_unused_1727_; 
v_unused_1727_ = lean_ctor_get(v_b_1686_, 0);
lean_dec(v_unused_1727_);
v___x_1694_ = v_b_1686_;
v_isShared_1695_ = v_isSharedCheck_1726_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_snd_1692_);
lean_dec(v_b_1686_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1726_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v_a_1696_; lean_object* v___x_1697_; 
v_a_1696_ = lean_array_uget_borrowed(v_as_1683_, v_i_1685_);
lean_inc(v_snd_1692_);
v___x_1697_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1681_, v___x_1682_, v_a_1696_, v_snd_1692_, v___y_1687_, v___y_1688_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1717_; 
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1700_ = v___x_1697_;
v_isShared_1701_ = v_isSharedCheck_1717_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1697_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1717_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
if (lean_obj_tag(v_a_1698_) == 0)
{
lean_object* v___x_1702_; lean_object* v___x_1704_; 
v___x_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1702_, 0, v_a_1698_);
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 0, v___x_1702_);
v___x_1704_ = v___x_1694_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1702_);
lean_ctor_set(v_reuseFailAlloc_1708_, 1, v_snd_1692_);
v___x_1704_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
lean_object* v___x_1706_; 
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 0, v___x_1704_);
v___x_1706_ = v___x_1700_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1704_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
else
{
lean_object* v_a_1709_; lean_object* v___x_1710_; lean_object* v___x_1712_; 
lean_del_object(v___x_1700_);
lean_dec(v_snd_1692_);
v_a_1709_ = lean_ctor_get(v_a_1698_, 0);
lean_inc(v_a_1709_);
lean_dec_ref_known(v_a_1698_, 1);
v___x_1710_ = lean_box(0);
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 1, v_a_1709_);
lean_ctor_set(v___x_1694_, 0, v___x_1710_);
v___x_1712_ = v___x_1694_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1710_);
lean_ctor_set(v_reuseFailAlloc_1716_, 1, v_a_1709_);
v___x_1712_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
size_t v___x_1713_; size_t v___x_1714_; 
v___x_1713_ = ((size_t)1ULL);
v___x_1714_ = lean_usize_add(v_i_1685_, v___x_1713_);
v_i_1685_ = v___x_1714_;
v_b_1686_ = v___x_1712_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
lean_del_object(v___x_1694_);
lean_dec(v_snd_1692_);
v_a_1718_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1697_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1697_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39___boxed(lean_object* v_init_1728_, lean_object* v___x_1729_, lean_object* v_as_1730_, lean_object* v_sz_1731_, lean_object* v_i_1732_, lean_object* v_b_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
uint8_t v___x_37101__boxed_1737_; size_t v_sz_boxed_1738_; size_t v_i_boxed_1739_; lean_object* v_res_1740_; 
v___x_37101__boxed_1737_ = lean_unbox(v___x_1729_);
v_sz_boxed_1738_ = lean_unbox_usize(v_sz_1731_);
lean_dec(v_sz_1731_);
v_i_boxed_1739_ = lean_unbox_usize(v_i_1732_);
lean_dec(v_i_1732_);
v_res_1740_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(v_init_1728_, v___x_37101__boxed_1737_, v_as_1730_, v_sz_boxed_1738_, v_i_boxed_1739_, v_b_1733_, v___y_1734_, v___y_1735_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec_ref(v_as_1730_);
lean_dec_ref(v_init_1728_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27___boxed(lean_object* v_init_1741_, lean_object* v___x_1742_, lean_object* v_n_1743_, lean_object* v_b_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
uint8_t v___x_37121__boxed_1748_; lean_object* v_res_1749_; 
v___x_37121__boxed_1748_ = lean_unbox(v___x_1742_);
v_res_1749_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1741_, v___x_37121__boxed_1748_, v_n_1743_, v_b_1744_, v___y_1745_, v___y_1746_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
lean_dec_ref(v_n_1743_);
lean_dec_ref(v_init_1741_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(uint8_t v___x_1750_, lean_object* v_as_1751_, size_t v_sz_1752_, size_t v_i_1753_, lean_object* v_b_1754_, lean_object* v___y_1755_){
_start:
{
uint8_t v___x_1757_; 
v___x_1757_ = lean_usize_dec_lt(v_i_1753_, v_sz_1752_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; 
v___x_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1758_, 0, v_b_1754_);
return v___x_1758_;
}
else
{
lean_object* v_snd_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1796_; 
v_snd_1759_ = lean_ctor_get(v_b_1754_, 1);
v_isSharedCheck_1796_ = !lean_is_exclusive(v_b_1754_);
if (v_isSharedCheck_1796_ == 0)
{
lean_object* v_unused_1797_; 
v_unused_1797_ = lean_ctor_get(v_b_1754_, 0);
lean_dec(v_unused_1797_);
v___x_1761_ = v_b_1754_;
v_isShared_1762_ = v_isSharedCheck_1796_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_snd_1759_);
lean_dec(v_b_1754_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1796_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v_ref_1763_; lean_object* v_a_1764_; lean_object* v_ref_1765_; lean_object* v_msg_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1795_; 
v_ref_1763_ = lean_ctor_get(v___y_1755_, 2);
v_a_1764_ = lean_array_uget(v_as_1751_, v_i_1753_);
v_ref_1765_ = lean_ctor_get(v_a_1764_, 0);
v_msg_1766_ = lean_ctor_get(v_a_1764_, 1);
v_isSharedCheck_1795_ = !lean_is_exclusive(v_a_1764_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1768_ = v_a_1764_;
v_isShared_1769_ = v_isSharedCheck_1795_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_msg_1766_);
lean_inc(v_ref_1765_);
lean_dec(v_a_1764_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1795_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1770_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v_ref_1787_; lean_object* v___y_1789_; lean_object* v___x_1792_; 
v___x_1770_ = lean_box(0);
v_ref_1787_ = l_Lean_replaceRef(v_ref_1765_, v_ref_1763_);
lean_dec(v_ref_1765_);
v___x_1792_ = l_Lean_Syntax_getPos_x3f(v_ref_1787_, v___x_1750_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v___x_1793_; 
v___x_1793_ = lean_unsigned_to_nat(0u);
v___y_1789_ = v___x_1793_;
goto v___jp_1788_;
}
else
{
lean_object* v_val_1794_; 
v_val_1794_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_val_1794_);
lean_dec_ref_known(v___x_1792_, 1);
v___y_1789_ = v_val_1794_;
goto v___jp_1788_;
}
v___jp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 1, v___y_1773_);
lean_ctor_set(v___x_1761_, 0, v___y_1772_);
v___x_1775_ = v___x_1761_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___y_1772_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v___y_1773_);
v___x_1775_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v_pos2traces_1779_; lean_object* v___x_1781_; 
v___x_1776_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1777_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1759_, v___x_1775_, v___x_1776_);
v___x_1778_ = lean_array_push(v___x_1777_, v_msg_1766_);
v_pos2traces_1779_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1759_, v___x_1775_, v___x_1778_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 1, v_pos2traces_1779_);
lean_ctor_set(v___x_1768_, 0, v___x_1770_);
v___x_1781_ = v___x_1768_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1770_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_pos2traces_1779_);
v___x_1781_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
size_t v___x_1782_; size_t v___x_1783_; 
v___x_1782_ = ((size_t)1ULL);
v___x_1783_ = lean_usize_add(v_i_1753_, v___x_1782_);
v_i_1753_ = v___x_1783_;
v_b_1754_ = v___x_1781_;
goto _start;
}
}
}
v___jp_1788_:
{
lean_object* v___x_1790_; 
v___x_1790_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1787_, v___x_1750_);
lean_dec(v_ref_1787_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_inc(v___y_1789_);
v___y_1772_ = v___y_1789_;
v___y_1773_ = v___y_1789_;
goto v___jp_1771_;
}
else
{
lean_object* v_val_1791_; 
v_val_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc(v_val_1791_);
lean_dec_ref_known(v___x_1790_, 1);
v___y_1772_ = v___y_1789_;
v___y_1773_ = v_val_1791_;
goto v___jp_1771_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg___boxed(lean_object* v___x_1798_, lean_object* v_as_1799_, lean_object* v_sz_1800_, lean_object* v_i_1801_, lean_object* v_b_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
uint8_t v___x_37304__boxed_1805_; size_t v_sz_boxed_1806_; size_t v_i_boxed_1807_; lean_object* v_res_1808_; 
v___x_37304__boxed_1805_ = lean_unbox(v___x_1798_);
v_sz_boxed_1806_ = lean_unbox_usize(v_sz_1800_);
lean_dec(v_sz_1800_);
v_i_boxed_1807_ = lean_unbox_usize(v_i_1801_);
lean_dec(v_i_1801_);
v_res_1808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_37304__boxed_1805_, v_as_1799_, v_sz_boxed_1806_, v_i_boxed_1807_, v_b_1802_, v___y_1803_);
lean_dec_ref(v___y_1803_);
lean_dec_ref(v_as_1799_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(uint8_t v___x_1809_, lean_object* v_as_1810_, size_t v_sz_1811_, size_t v_i_1812_, lean_object* v_b_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
uint8_t v___x_1817_; 
v___x_1817_ = lean_usize_dec_lt(v_i_1812_, v_sz_1811_);
if (v___x_1817_ == 0)
{
lean_object* v___x_1818_; 
v___x_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1818_, 0, v_b_1813_);
return v___x_1818_;
}
else
{
lean_object* v_snd_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1856_; 
v_snd_1819_ = lean_ctor_get(v_b_1813_, 1);
v_isSharedCheck_1856_ = !lean_is_exclusive(v_b_1813_);
if (v_isSharedCheck_1856_ == 0)
{
lean_object* v_unused_1857_; 
v_unused_1857_ = lean_ctor_get(v_b_1813_, 0);
lean_dec(v_unused_1857_);
v___x_1821_ = v_b_1813_;
v_isShared_1822_ = v_isSharedCheck_1856_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_snd_1819_);
lean_dec(v_b_1813_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1856_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v_ref_1823_; lean_object* v_a_1824_; lean_object* v_ref_1825_; lean_object* v_msg_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1855_; 
v_ref_1823_ = lean_ctor_get(v___y_1814_, 2);
v_a_1824_ = lean_array_uget(v_as_1810_, v_i_1812_);
v_ref_1825_ = lean_ctor_get(v_a_1824_, 0);
v_msg_1826_ = lean_ctor_get(v_a_1824_, 1);
v_isSharedCheck_1855_ = !lean_is_exclusive(v_a_1824_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1828_ = v_a_1824_;
v_isShared_1829_ = v_isSharedCheck_1855_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_msg_1826_);
lean_inc(v_ref_1825_);
lean_dec(v_a_1824_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1855_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1830_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v_ref_1847_; lean_object* v___y_1849_; lean_object* v___x_1852_; 
v___x_1830_ = lean_box(0);
v_ref_1847_ = l_Lean_replaceRef(v_ref_1825_, v_ref_1823_);
lean_dec(v_ref_1825_);
v___x_1852_ = l_Lean_Syntax_getPos_x3f(v_ref_1847_, v___x_1809_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v___x_1853_; 
v___x_1853_ = lean_unsigned_to_nat(0u);
v___y_1849_ = v___x_1853_;
goto v___jp_1848_;
}
else
{
lean_object* v_val_1854_; 
v_val_1854_ = lean_ctor_get(v___x_1852_, 0);
lean_inc(v_val_1854_);
lean_dec_ref_known(v___x_1852_, 1);
v___y_1849_ = v_val_1854_;
goto v___jp_1848_;
}
v___jp_1831_:
{
lean_object* v___x_1835_; 
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 1, v___y_1833_);
lean_ctor_set(v___x_1821_, 0, v___y_1832_);
v___x_1835_ = v___x_1821_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___y_1832_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v___y_1833_);
v___x_1835_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v_pos2traces_1839_; lean_object* v___x_1841_; 
v___x_1836_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1837_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1819_, v___x_1835_, v___x_1836_);
v___x_1838_ = lean_array_push(v___x_1837_, v_msg_1826_);
v_pos2traces_1839_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1819_, v___x_1835_, v___x_1838_);
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 1, v_pos2traces_1839_);
lean_ctor_set(v___x_1828_, 0, v___x_1830_);
v___x_1841_ = v___x_1828_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1830_);
lean_ctor_set(v_reuseFailAlloc_1845_, 1, v_pos2traces_1839_);
v___x_1841_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
size_t v___x_1842_; size_t v___x_1843_; lean_object* v___x_1844_; 
v___x_1842_ = ((size_t)1ULL);
v___x_1843_ = lean_usize_add(v_i_1812_, v___x_1842_);
v___x_1844_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_1809_, v_as_1810_, v_sz_1811_, v___x_1843_, v___x_1841_, v___y_1814_);
return v___x_1844_;
}
}
}
v___jp_1848_:
{
lean_object* v___x_1850_; 
v___x_1850_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1847_, v___x_1809_);
lean_dec(v_ref_1847_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_inc(v___y_1849_);
v___y_1832_ = v___y_1849_;
v___y_1833_ = v___y_1849_;
goto v___jp_1831_;
}
else
{
lean_object* v_val_1851_; 
v_val_1851_ = lean_ctor_get(v___x_1850_, 0);
lean_inc(v_val_1851_);
lean_dec_ref_known(v___x_1850_, 1);
v___y_1832_ = v___y_1849_;
v___y_1833_ = v_val_1851_;
goto v___jp_1831_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28___boxed(lean_object* v___x_1858_, lean_object* v_as_1859_, lean_object* v_sz_1860_, lean_object* v_i_1861_, lean_object* v_b_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
uint8_t v___x_37384__boxed_1866_; size_t v_sz_boxed_1867_; size_t v_i_boxed_1868_; lean_object* v_res_1869_; 
v___x_37384__boxed_1866_ = lean_unbox(v___x_1858_);
v_sz_boxed_1867_ = lean_unbox_usize(v_sz_1860_);
lean_dec(v_sz_1860_);
v_i_boxed_1868_ = lean_unbox_usize(v_i_1861_);
lean_dec(v_i_1861_);
v_res_1869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(v___x_37384__boxed_1866_, v_as_1859_, v_sz_boxed_1867_, v_i_boxed_1868_, v_b_1862_, v___y_1863_, v___y_1864_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec_ref(v_as_1859_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(uint8_t v___x_1870_, lean_object* v_t_1871_, lean_object* v_init_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v_root_1876_; lean_object* v_tail_1877_; lean_object* v___x_1878_; 
v_root_1876_ = lean_ctor_get(v_t_1871_, 0);
v_tail_1877_ = lean_ctor_get(v_t_1871_, 1);
lean_inc_ref(v_init_1872_);
v___x_1878_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1872_, v___x_1870_, v_root_1876_, v_init_1872_, v___y_1873_, v___y_1874_);
lean_dec_ref(v_init_1872_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1915_; 
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1881_ = v___x_1878_;
v_isShared_1882_ = v_isSharedCheck_1915_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1878_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1915_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
if (lean_obj_tag(v_a_1879_) == 0)
{
lean_object* v_a_1883_; lean_object* v___x_1885_; 
v_a_1883_ = lean_ctor_get(v_a_1879_, 0);
lean_inc(v_a_1883_);
lean_dec_ref_known(v_a_1879_, 1);
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 0, v_a_1883_);
v___x_1885_ = v___x_1881_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1883_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
else
{
lean_object* v_a_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; size_t v_sz_1890_; size_t v___x_1891_; lean_object* v___x_1892_; 
lean_del_object(v___x_1881_);
v_a_1887_ = lean_ctor_get(v_a_1879_, 0);
lean_inc(v_a_1887_);
lean_dec_ref_known(v_a_1879_, 1);
v___x_1888_ = lean_box(0);
v___x_1889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
lean_ctor_set(v___x_1889_, 1, v_a_1887_);
v_sz_1890_ = lean_array_size(v_tail_1877_);
v___x_1891_ = ((size_t)0ULL);
v___x_1892_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(v___x_1870_, v_tail_1877_, v_sz_1890_, v___x_1891_, v___x_1889_, v___y_1873_, v___y_1874_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1906_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1895_ = v___x_1892_;
v_isShared_1896_ = v_isSharedCheck_1906_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1892_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1906_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v_fst_1897_; 
v_fst_1897_ = lean_ctor_get(v_a_1893_, 0);
if (lean_obj_tag(v_fst_1897_) == 0)
{
lean_object* v_snd_1898_; lean_object* v___x_1900_; 
v_snd_1898_ = lean_ctor_get(v_a_1893_, 1);
lean_inc(v_snd_1898_);
lean_dec(v_a_1893_);
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 0, v_snd_1898_);
v___x_1900_ = v___x_1895_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_snd_1898_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
else
{
lean_object* v_val_1902_; lean_object* v___x_1904_; 
lean_inc_ref(v_fst_1897_);
lean_dec(v_a_1893_);
v_val_1902_ = lean_ctor_get(v_fst_1897_, 0);
lean_inc(v_val_1902_);
lean_dec_ref_known(v_fst_1897_, 1);
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 0, v_val_1902_);
v___x_1904_ = v___x_1895_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_val_1902_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
else
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
v_a_1907_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v___x_1892_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1892_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1907_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
}
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
v_a_1916_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1918_ = v___x_1878_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1878_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19___boxed(lean_object* v___x_1924_, lean_object* v_t_1925_, lean_object* v_init_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
uint8_t v___x_37465__boxed_1930_; lean_object* v_res_1931_; 
v___x_37465__boxed_1930_ = lean_unbox(v___x_1924_);
v_res_1931_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(v___x_37465__boxed_1930_, v_t_1925_, v_init_1926_, v___y_1927_, v___y_1928_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec_ref(v_t_1925_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(lean_object* v_x_1932_, lean_object* v_x_1933_){
_start:
{
if (lean_obj_tag(v_x_1933_) == 0)
{
return v_x_1932_;
}
else
{
lean_object* v_key_1934_; lean_object* v_value_1935_; lean_object* v_tail_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
v_key_1934_ = lean_ctor_get(v_x_1933_, 0);
v_value_1935_ = lean_ctor_get(v_x_1933_, 1);
v_tail_1936_ = lean_ctor_get(v_x_1933_, 2);
lean_inc(v_value_1935_);
lean_inc(v_key_1934_);
v___x_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1937_, 0, v_key_1934_);
lean_ctor_set(v___x_1937_, 1, v_value_1935_);
v___x_1938_ = lean_array_push(v_x_1932_, v___x_1937_);
v_x_1932_ = v___x_1938_;
v_x_1933_ = v_tail_1936_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22___boxed(lean_object* v_x_1940_, lean_object* v_x_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(v_x_1940_, v_x_1941_);
lean_dec(v_x_1941_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(lean_object* v_as_1943_, size_t v_i_1944_, size_t v_stop_1945_, lean_object* v_b_1946_){
_start:
{
uint8_t v___x_1947_; 
v___x_1947_ = lean_usize_dec_eq(v_i_1944_, v_stop_1945_);
if (v___x_1947_ == 0)
{
lean_object* v___x_1948_; lean_object* v___x_1949_; size_t v___x_1950_; size_t v___x_1951_; 
v___x_1948_ = lean_array_uget_borrowed(v_as_1943_, v_i_1944_);
v___x_1949_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(v_b_1946_, v___x_1948_);
v___x_1950_ = ((size_t)1ULL);
v___x_1951_ = lean_usize_add(v_i_1944_, v___x_1950_);
v_i_1944_ = v___x_1951_;
v_b_1946_ = v___x_1949_;
goto _start;
}
else
{
return v_b_1946_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23___boxed(lean_object* v_as_1953_, lean_object* v_i_1954_, lean_object* v_stop_1955_, lean_object* v_b_1956_){
_start:
{
size_t v_i_boxed_1957_; size_t v_stop_boxed_1958_; lean_object* v_res_1959_; 
v_i_boxed_1957_ = lean_unbox_usize(v_i_1954_);
lean_dec(v_i_1954_);
v_stop_boxed_1958_ = lean_unbox_usize(v_stop_1955_);
lean_dec(v_stop_1955_);
v_res_1959_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_as_1953_, v_i_boxed_1957_, v_stop_boxed_1958_, v_b_1956_);
lean_dec_ref(v_as_1953_);
return v_res_1959_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0(void){
_start:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1960_ = lean_unsigned_to_nat(32u);
v___x_1961_ = lean_mk_empty_array_with_capacity(v___x_1960_);
v___x_1962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1961_);
return v___x_1962_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1(void){
_start:
{
size_t v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1963_ = ((size_t)5ULL);
v___x_1964_ = lean_unsigned_to_nat(0u);
v___x_1965_ = lean_unsigned_to_nat(32u);
v___x_1966_ = lean_mk_empty_array_with_capacity(v___x_1965_);
v___x_1967_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0);
v___x_1968_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1968_, 0, v___x_1967_);
lean_ctor_set(v___x_1968_, 1, v___x_1966_);
lean_ctor_set(v___x_1968_, 2, v___x_1964_);
lean_ctor_set(v___x_1968_, 3, v___x_1964_);
lean_ctor_set_usize(v___x_1968_, 4, v___x_1963_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(lean_object* v___y_1969_){
_start:
{
lean_object* v___x_1971_; lean_object* v_traceState_1972_; lean_object* v_traces_1973_; lean_object* v___x_1974_; lean_object* v_traceState_1975_; lean_object* v_env_1976_; lean_object* v_nextMacroScope_1977_; lean_object* v_ngen_1978_; lean_object* v_auxDeclNGen_1979_; lean_object* v_cache_1980_; lean_object* v_messages_1981_; lean_object* v_infoState_1982_; lean_object* v_snapshotTasks_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2002_; 
v___x_1971_ = lean_st_ref_get(v___y_1969_);
v_traceState_1972_ = lean_ctor_get(v___x_1971_, 4);
lean_inc_ref(v_traceState_1972_);
lean_dec(v___x_1971_);
v_traces_1973_ = lean_ctor_get(v_traceState_1972_, 0);
lean_inc_ref(v_traces_1973_);
lean_dec_ref(v_traceState_1972_);
v___x_1974_ = lean_st_ref_take(v___y_1969_);
v_traceState_1975_ = lean_ctor_get(v___x_1974_, 4);
v_env_1976_ = lean_ctor_get(v___x_1974_, 0);
v_nextMacroScope_1977_ = lean_ctor_get(v___x_1974_, 1);
v_ngen_1978_ = lean_ctor_get(v___x_1974_, 2);
v_auxDeclNGen_1979_ = lean_ctor_get(v___x_1974_, 3);
v_cache_1980_ = lean_ctor_get(v___x_1974_, 5);
v_messages_1981_ = lean_ctor_get(v___x_1974_, 6);
v_infoState_1982_ = lean_ctor_get(v___x_1974_, 7);
v_snapshotTasks_1983_ = lean_ctor_get(v___x_1974_, 8);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1985_ = v___x_1974_;
v_isShared_1986_ = v_isSharedCheck_2002_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_snapshotTasks_1983_);
lean_inc(v_infoState_1982_);
lean_inc(v_messages_1981_);
lean_inc(v_cache_1980_);
lean_inc(v_traceState_1975_);
lean_inc(v_auxDeclNGen_1979_);
lean_inc(v_ngen_1978_);
lean_inc(v_nextMacroScope_1977_);
lean_inc(v_env_1976_);
lean_dec(v___x_1974_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2002_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
uint64_t v_tid_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_2000_; 
v_tid_1987_ = lean_ctor_get_uint64(v_traceState_1975_, sizeof(void*)*1);
v_isSharedCheck_2000_ = !lean_is_exclusive(v_traceState_1975_);
if (v_isSharedCheck_2000_ == 0)
{
lean_object* v_unused_2001_; 
v_unused_2001_ = lean_ctor_get(v_traceState_1975_, 0);
lean_dec(v_unused_2001_);
v___x_1989_ = v_traceState_1975_;
v_isShared_1990_ = v_isSharedCheck_2000_;
goto v_resetjp_1988_;
}
else
{
lean_dec(v_traceState_1975_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_2000_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1991_; lean_object* v___x_1993_; 
v___x_1991_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 0, v___x_1991_);
v___x_1993_ = v___x_1989_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1991_);
lean_ctor_set_uint64(v_reuseFailAlloc_1999_, sizeof(void*)*1, v_tid_1987_);
v___x_1993_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
lean_object* v___x_1995_; 
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 4, v___x_1993_);
v___x_1995_ = v___x_1985_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_env_1976_);
lean_ctor_set(v_reuseFailAlloc_1998_, 1, v_nextMacroScope_1977_);
lean_ctor_set(v_reuseFailAlloc_1998_, 2, v_ngen_1978_);
lean_ctor_set(v_reuseFailAlloc_1998_, 3, v_auxDeclNGen_1979_);
lean_ctor_set(v_reuseFailAlloc_1998_, 4, v___x_1993_);
lean_ctor_set(v_reuseFailAlloc_1998_, 5, v_cache_1980_);
lean_ctor_set(v_reuseFailAlloc_1998_, 6, v_messages_1981_);
lean_ctor_set(v_reuseFailAlloc_1998_, 7, v_infoState_1982_);
lean_ctor_set(v_reuseFailAlloc_1998_, 8, v_snapshotTasks_1983_);
v___x_1995_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1996_ = lean_st_ref_put(v___y_1969_, v___x_1995_);
v___x_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1997_, 0, v_traces_1973_);
return v___x_1997_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___boxed(lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_2003_);
lean_dec(v___y_2003_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(lean_object* v_hi_2006_, lean_object* v_pivot_2007_, lean_object* v_as_2008_, lean_object* v_i_2009_, lean_object* v_k_2010_){
_start:
{
uint8_t v___x_2011_; 
v___x_2011_ = lean_nat_dec_lt(v_k_2010_, v_hi_2006_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
lean_dec(v_k_2010_);
v___x_2012_ = lean_array_fswap(v_as_2008_, v_i_2009_, v_hi_2006_);
v___x_2013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2013_, 0, v_i_2009_);
lean_ctor_set(v___x_2013_, 1, v___x_2012_);
return v___x_2013_;
}
else
{
lean_object* v___x_2014_; lean_object* v_fst_2015_; lean_object* v_fst_2016_; lean_object* v_fst_2017_; lean_object* v_fst_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; uint8_t v___x_2021_; 
v___x_2014_ = lean_array_fget_borrowed(v_as_2008_, v_k_2010_);
v_fst_2015_ = lean_ctor_get(v___x_2014_, 0);
v_fst_2016_ = lean_ctor_get(v_pivot_2007_, 0);
v_fst_2017_ = lean_ctor_get(v_fst_2015_, 0);
v_fst_2018_ = lean_ctor_get(v_fst_2016_, 0);
v___x_2019_ = lean_unsigned_to_nat(1u);
v___x_2020_ = lean_nat_add(v_fst_2017_, v___x_2019_);
v___x_2021_ = lean_nat_dec_le(v___x_2020_, v_fst_2018_);
lean_dec(v___x_2020_);
if (v___x_2021_ == 0)
{
lean_object* v___x_2022_; 
v___x_2022_ = lean_nat_add(v_k_2010_, v___x_2019_);
lean_dec(v_k_2010_);
v_k_2010_ = v___x_2022_;
goto _start;
}
else
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2024_ = lean_array_fswap(v_as_2008_, v_i_2009_, v_k_2010_);
v___x_2025_ = lean_nat_add(v_i_2009_, v___x_2019_);
lean_dec(v_i_2009_);
v___x_2026_ = lean_nat_add(v_k_2010_, v___x_2019_);
lean_dec(v_k_2010_);
v_as_2008_ = v___x_2024_;
v_i_2009_ = v___x_2025_;
v_k_2010_ = v___x_2026_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg___boxed(lean_object* v_hi_2028_, lean_object* v_pivot_2029_, lean_object* v_as_2030_, lean_object* v_i_2031_, lean_object* v_k_2032_){
_start:
{
lean_object* v_res_2033_; 
v_res_2033_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_2028_, v_pivot_2029_, v_as_2030_, v_i_2031_, v_k_2032_);
lean_dec_ref(v_pivot_2029_);
lean_dec(v_hi_2028_);
return v_res_2033_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(lean_object* v_x_2034_, lean_object* v_x_2035_){
_start:
{
lean_object* v_fst_2036_; lean_object* v_fst_2037_; lean_object* v_fst_2038_; lean_object* v_fst_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; uint8_t v___x_2042_; 
v_fst_2036_ = lean_ctor_get(v_x_2034_, 0);
v_fst_2037_ = lean_ctor_get(v_x_2035_, 0);
v_fst_2038_ = lean_ctor_get(v_fst_2036_, 0);
v_fst_2039_ = lean_ctor_get(v_fst_2037_, 0);
v___x_2040_ = lean_unsigned_to_nat(1u);
v___x_2041_ = lean_nat_add(v_fst_2038_, v___x_2040_);
v___x_2042_ = lean_nat_dec_le(v___x_2041_, v_fst_2039_);
lean_dec(v___x_2041_);
return v___x_2042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0___boxed(lean_object* v_x_2043_, lean_object* v_x_2044_){
_start:
{
uint8_t v_res_2045_; lean_object* v_r_2046_; 
v_res_2045_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v_x_2043_, v_x_2044_);
lean_dec_ref(v_x_2044_);
lean_dec_ref(v_x_2043_);
v_r_2046_ = lean_box(v_res_2045_);
return v_r_2046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(lean_object* v_n_2047_, lean_object* v_as_2048_, lean_object* v_lo_2049_, lean_object* v_hi_2050_){
_start:
{
lean_object* v___y_2052_; uint8_t v___x_2062_; 
v___x_2062_ = lean_nat_dec_lt(v_lo_2049_, v_hi_2050_);
if (v___x_2062_ == 0)
{
lean_dec(v_lo_2049_);
return v_as_2048_;
}
else
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v_mid_2065_; lean_object* v___y_2067_; lean_object* v___y_2073_; lean_object* v___x_2078_; lean_object* v___x_2079_; uint8_t v___x_2080_; 
v___x_2063_ = lean_nat_add(v_lo_2049_, v_hi_2050_);
v___x_2064_ = lean_unsigned_to_nat(1u);
v_mid_2065_ = lean_nat_shiftr(v___x_2063_, v___x_2064_);
lean_dec(v___x_2063_);
v___x_2078_ = lean_array_fget_borrowed(v_as_2048_, v_mid_2065_);
v___x_2079_ = lean_array_fget_borrowed(v_as_2048_, v_lo_2049_);
v___x_2080_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2078_, v___x_2079_);
if (v___x_2080_ == 0)
{
v___y_2073_ = v_as_2048_;
goto v___jp_2072_;
}
else
{
lean_object* v___x_2081_; 
v___x_2081_ = lean_array_fswap(v_as_2048_, v_lo_2049_, v_mid_2065_);
v___y_2073_ = v___x_2081_;
goto v___jp_2072_;
}
v___jp_2066_:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; uint8_t v___x_2070_; 
v___x_2068_ = lean_array_fget_borrowed(v___y_2067_, v_mid_2065_);
v___x_2069_ = lean_array_fget_borrowed(v___y_2067_, v_hi_2050_);
v___x_2070_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2068_, v___x_2069_);
if (v___x_2070_ == 0)
{
lean_dec(v_mid_2065_);
v___y_2052_ = v___y_2067_;
goto v___jp_2051_;
}
else
{
lean_object* v___x_2071_; 
v___x_2071_ = lean_array_fswap(v___y_2067_, v_mid_2065_, v_hi_2050_);
lean_dec(v_mid_2065_);
v___y_2052_ = v___x_2071_;
goto v___jp_2051_;
}
}
v___jp_2072_:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; uint8_t v___x_2076_; 
v___x_2074_ = lean_array_fget_borrowed(v___y_2073_, v_hi_2050_);
v___x_2075_ = lean_array_fget_borrowed(v___y_2073_, v_lo_2049_);
v___x_2076_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2074_, v___x_2075_);
if (v___x_2076_ == 0)
{
v___y_2067_ = v___y_2073_;
goto v___jp_2066_;
}
else
{
lean_object* v___x_2077_; 
v___x_2077_ = lean_array_fswap(v___y_2073_, v_lo_2049_, v_hi_2050_);
v___y_2067_ = v___x_2077_;
goto v___jp_2066_;
}
}
}
v___jp_2051_:
{
lean_object* v_pivot_2053_; lean_object* v___x_2054_; lean_object* v_fst_2055_; lean_object* v_snd_2056_; uint8_t v___x_2057_; 
v_pivot_2053_ = lean_array_fget(v___y_2052_, v_hi_2050_);
lean_inc_n(v_lo_2049_, 2);
v___x_2054_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_2050_, v_pivot_2053_, v___y_2052_, v_lo_2049_, v_lo_2049_);
lean_dec(v_pivot_2053_);
v_fst_2055_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_fst_2055_);
v_snd_2056_ = lean_ctor_get(v___x_2054_, 1);
lean_inc(v_snd_2056_);
lean_dec_ref(v___x_2054_);
v___x_2057_ = lean_nat_dec_le(v_hi_2050_, v_fst_2055_);
if (v___x_2057_ == 0)
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2058_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_2047_, v_snd_2056_, v_lo_2049_, v_fst_2055_);
v___x_2059_ = lean_unsigned_to_nat(1u);
v___x_2060_ = lean_nat_add(v_fst_2055_, v___x_2059_);
lean_dec(v_fst_2055_);
v_as_2048_ = v___x_2058_;
v_lo_2049_ = v___x_2060_;
goto _start;
}
else
{
lean_dec(v_fst_2055_);
lean_dec(v_lo_2049_);
return v_snd_2056_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___boxed(lean_object* v_n_2082_, lean_object* v_as_2083_, lean_object* v_lo_2084_, lean_object* v_hi_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_2082_, v_as_2083_, v_lo_2084_, v_hi_2085_);
lean_dec(v_hi_2085_);
lean_dec(v_n_2082_);
return v_res_2086_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0(void){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2087_ = lean_box(0);
v___x_2088_ = lean_unsigned_to_nat(16u);
v___x_2089_ = lean_mk_array(v___x_2088_, v___x_2087_);
return v___x_2089_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1(void){
_start:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v_pos2traces_2092_; 
v___x_2090_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0, &l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0);
v___x_2091_ = lean_unsigned_to_nat(0u);
v_pos2traces_2092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos2traces_2092_, 0, v___x_2091_);
lean_ctor_set(v_pos2traces_2092_, 1, v___x_2090_);
return v_pos2traces_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10(lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
lean_object* v_toCold_2099_; lean_object* v_options_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v_toCold_2099_ = lean_ctor_get(v___y_2093_, 0);
v_options_2100_ = lean_ctor_get(v_toCold_2099_, 2);
v___x_2101_ = l_Lean_trace_profiler_output;
v___x_2102_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(v_options_2100_, v___x_2101_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v___x_2103_; uint8_t v___x_2104_; 
v___x_2103_ = l_Lean_trace_profiler_serve;
v___x_2104_ = l_Lean_Option_get___at___00main_spec__8(v_options_2100_, v___x_2103_);
if (v___x_2104_ == 0)
{
lean_object* v___x_2105_; lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2168_; 
v___x_2105_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_2094_);
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2108_ = v___x_2105_;
v_isShared_2109_ = v_isSharedCheck_2168_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2105_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2168_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
uint8_t v___x_2110_; 
v___x_2110_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_2106_);
if (v___x_2110_ == 0)
{
lean_object* v___x_2111_; lean_object* v_pos2traces_2112_; lean_object* v___x_2113_; 
lean_del_object(v___x_2108_);
v___x_2111_ = lean_unsigned_to_nat(0u);
v_pos2traces_2112_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1, &l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1);
v___x_2113_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(v___x_2110_, v_a_2106_, v_pos2traces_2112_, v___y_2093_, v___y_2094_);
lean_dec(v_a_2106_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_a_2114_; lean_object* v___y_2116_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2133_; lean_object* v___y_2136_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2142_; lean_object* v_size_2148_; lean_object* v_buckets_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; uint8_t v___x_2152_; 
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_a_2114_);
lean_dec_ref_known(v___x_2113_, 1);
v_size_2148_ = lean_ctor_get(v_a_2114_, 0);
lean_inc(v_size_2148_);
v_buckets_2149_ = lean_ctor_get(v_a_2114_, 1);
lean_inc_ref(v_buckets_2149_);
lean_dec(v_a_2114_);
v___x_2150_ = lean_mk_empty_array_with_capacity(v_size_2148_);
lean_dec(v_size_2148_);
v___x_2151_ = lean_array_get_size(v_buckets_2149_);
v___x_2152_ = lean_nat_dec_lt(v___x_2111_, v___x_2151_);
if (v___x_2152_ == 0)
{
lean_dec_ref(v_buckets_2149_);
v___y_2142_ = v___x_2150_;
goto v___jp_2141_;
}
else
{
size_t v___x_2153_; size_t v___x_2154_; lean_object* v___x_2155_; 
v___x_2153_ = ((size_t)0ULL);
v___x_2154_ = lean_usize_of_nat(v___x_2151_);
v___x_2155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_buckets_2149_, v___x_2153_, v___x_2154_, v___x_2150_);
lean_dec_ref(v_buckets_2149_);
v___y_2142_ = v___x_2155_;
goto v___jp_2141_;
}
v___jp_2115_:
{
lean_object* v___x_2117_; size_t v_sz_2118_; size_t v___x_2119_; lean_object* v___x_2120_; 
v___x_2117_ = lean_box(0);
v_sz_2118_ = lean_array_size(v___y_2116_);
v___x_2119_ = ((size_t)0ULL);
v___x_2120_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(v___x_2104_, v___y_2116_, v_sz_2118_, v___x_2119_, v___x_2117_, v___y_2093_, v___y_2094_);
lean_dec_ref(v___y_2116_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2127_ == 0)
{
lean_object* v_unused_2128_; 
v_unused_2128_ = lean_ctor_get(v___x_2120_, 0);
lean_dec(v_unused_2128_);
v___x_2122_ = v___x_2120_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_dec(v___x_2120_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 0, v___x_2117_);
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2117_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
else
{
return v___x_2120_;
}
}
v___jp_2129_:
{
lean_object* v___x_2134_; 
v___x_2134_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
lean_dec(v___y_2133_);
lean_dec(v___y_2130_);
v___y_2116_ = v___x_2134_;
goto v___jp_2115_;
}
v___jp_2135_:
{
uint8_t v___x_2140_; 
v___x_2140_ = lean_nat_dec_le(v___y_2139_, v___y_2138_);
if (v___x_2140_ == 0)
{
lean_dec(v___y_2138_);
lean_inc(v___y_2139_);
v___y_2130_ = v___y_2136_;
v___y_2131_ = v___y_2137_;
v___y_2132_ = v___y_2139_;
v___y_2133_ = v___y_2139_;
goto v___jp_2129_;
}
else
{
v___y_2130_ = v___y_2136_;
v___y_2131_ = v___y_2137_;
v___y_2132_ = v___y_2139_;
v___y_2133_ = v___y_2138_;
goto v___jp_2129_;
}
}
v___jp_2141_:
{
lean_object* v___x_2143_; uint8_t v___x_2144_; 
v___x_2143_ = lean_array_get_size(v___y_2142_);
v___x_2144_ = lean_nat_dec_eq(v___x_2143_, v___x_2111_);
if (v___x_2144_ == 0)
{
lean_object* v___x_2145_; lean_object* v___x_2146_; uint8_t v___x_2147_; 
v___x_2145_ = lean_unsigned_to_nat(1u);
v___x_2146_ = lean_nat_sub(v___x_2143_, v___x_2145_);
v___x_2147_ = lean_nat_dec_le(v___x_2111_, v___x_2146_);
if (v___x_2147_ == 0)
{
lean_inc(v___x_2146_);
v___y_2136_ = v___x_2143_;
v___y_2137_ = v___y_2142_;
v___y_2138_ = v___x_2146_;
v___y_2139_ = v___x_2146_;
goto v___jp_2135_;
}
else
{
v___y_2136_ = v___x_2143_;
v___y_2137_ = v___y_2142_;
v___y_2138_ = v___x_2146_;
v___y_2139_ = v___x_2111_;
goto v___jp_2135_;
}
}
else
{
v___y_2116_ = v___y_2142_;
goto v___jp_2115_;
}
}
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
v_a_2156_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2113_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2113_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2161_; 
if (v_isShared_2159_ == 0)
{
v___x_2161_ = v___x_2158_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_a_2156_);
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
lean_object* v___x_2164_; lean_object* v___x_2166_; 
lean_dec(v_a_2106_);
v___x_2164_ = lean_box(0);
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 0, v___x_2164_);
v___x_2166_ = v___x_2108_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2164_);
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
goto v___jp_2096_;
}
}
else
{
lean_dec_ref_known(v___x_2102_, 1);
goto v___jp_2096_;
}
v___jp_2096_:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2097_ = lean_box(0);
v___x_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
return v___x_2098_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10___boxed(lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2169_, v___y_2170_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(lean_object* v_as_2173_, size_t v_sz_2174_, size_t v_i_2175_, lean_object* v_b_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
uint8_t v___x_2180_; 
v___x_2180_ = lean_usize_dec_lt(v_i_2175_, v_sz_2174_);
if (v___x_2180_ == 0)
{
lean_object* v___x_2181_; 
v___x_2181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2181_, 0, v_b_2176_);
return v___x_2181_;
}
else
{
lean_object* v_toCold_2182_; lean_object* v_options_2183_; lean_object* v_a_2184_; lean_object* v___x_2185_; 
v_toCold_2182_ = lean_ctor_get(v___y_2177_, 0);
v_options_2183_ = lean_ctor_get(v_toCold_2182_, 2);
v_a_2184_ = lean_array_uget_borrowed(v_as_2173_, v_i_2175_);
lean_inc_ref(v_options_2183_);
lean_inc(v_a_2184_);
v___x_2185_ = l_Lean_Compiler_LCNF_resumeCompilation(v_a_2184_, v_options_2183_, v___y_2177_, v___y_2178_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v___x_2186_; 
lean_dec_ref_known(v___x_2185_, 1);
v___x_2186_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2177_, v___y_2178_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v___x_2187_; size_t v___x_2188_; size_t v___x_2189_; 
lean_dec_ref_known(v___x_2186_, 1);
v___x_2187_ = lean_box(0);
v___x_2188_ = ((size_t)1ULL);
v___x_2189_ = lean_usize_add(v_i_2175_, v___x_2188_);
v_i_2175_ = v___x_2189_;
v_b_2176_ = v___x_2187_;
goto _start;
}
else
{
return v___x_2186_;
}
}
else
{
lean_object* v_a_2191_; lean_object* v___x_2192_; 
v_a_2191_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_a_2191_);
lean_dec_ref_known(v___x_2185_, 1);
v___x_2192_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2177_, v___y_2178_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2199_ == 0)
{
lean_object* v_unused_2200_; 
v_unused_2200_ = lean_ctor_get(v___x_2192_, 0);
lean_dec(v_unused_2200_);
v___x_2194_ = v___x_2192_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_dec(v___x_2192_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
lean_ctor_set_tag(v___x_2194_, 1);
lean_ctor_set(v___x_2194_, 0, v_a_2191_);
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2191_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
else
{
lean_dec(v_a_2191_);
return v___x_2192_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11___boxed(lean_object* v_as_2201_, lean_object* v_sz_2202_, lean_object* v_i_2203_, lean_object* v_b_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
size_t v_sz_boxed_2208_; size_t v_i_boxed_2209_; lean_object* v_res_2210_; 
v_sz_boxed_2208_ = lean_unbox_usize(v_sz_2202_);
lean_dec(v_sz_2202_);
v_i_boxed_2209_ = lean_unbox_usize(v_i_2203_);
lean_dec(v_i_2203_);
v_res_2210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(v_as_2201_, v_sz_boxed_2208_, v_i_boxed_2209_, v_b_2204_, v___y_2205_, v___y_2206_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
lean_dec_ref(v_as_2201_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(lean_object* v_as_2211_, size_t v_sz_2212_, size_t v_i_2213_, lean_object* v_b_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
uint8_t v___x_2218_; 
v___x_2218_ = lean_usize_dec_lt(v_i_2213_, v_sz_2212_);
if (v___x_2218_ == 0)
{
lean_object* v___x_2219_; 
v___x_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2219_, 0, v_b_2214_);
return v___x_2219_;
}
else
{
lean_object* v_a_2220_; lean_object* v_declNames_2221_; lean_object* v___x_2222_; size_t v_sz_2223_; size_t v___x_2224_; lean_object* v___x_2225_; 
v_a_2220_ = lean_array_uget_borrowed(v_as_2211_, v_i_2213_);
v_declNames_2221_ = lean_ctor_get(v_a_2220_, 0);
v___x_2222_ = lean_box(0);
v_sz_2223_ = lean_array_size(v_declNames_2221_);
v___x_2224_ = ((size_t)0ULL);
v___x_2225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(v_declNames_2221_, v_sz_2223_, v___x_2224_, v___x_2222_, v___y_2215_, v___y_2216_);
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_object* v___x_2226_; 
lean_dec_ref_known(v___x_2225_, 1);
v___x_2226_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v___y_2216_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; lean_object* v_unreported_2228_; lean_object* v___x_2229_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
lean_inc(v_a_2227_);
lean_dec_ref_known(v___x_2226_, 1);
v_unreported_2228_ = lean_ctor_get(v_a_2227_, 1);
lean_inc_ref(v_unreported_2228_);
lean_dec(v_a_2227_);
v___x_2229_ = l_Lean_PersistentArray_forIn___at___00main_spec__12(v_unreported_2228_, v___x_2222_, v___y_2215_, v___y_2216_);
lean_dec_ref(v_unreported_2228_);
if (lean_obj_tag(v___x_2229_) == 0)
{
size_t v___x_2230_; size_t v___x_2231_; 
lean_dec_ref_known(v___x_2229_, 1);
v___x_2230_ = ((size_t)1ULL);
v___x_2231_ = lean_usize_add(v_i_2213_, v___x_2230_);
v_i_2213_ = v___x_2231_;
v_b_2214_ = v___x_2222_;
goto _start;
}
else
{
return v___x_2229_;
}
}
else
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
v_a_2233_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___x_2226_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2226_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2236_ == 0)
{
v___x_2238_ = v___x_2235_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2233_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
else
{
return v___x_2225_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13___boxed(lean_object* v_as_2241_, lean_object* v_sz_2242_, lean_object* v_i_2243_, lean_object* v_b_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
size_t v_sz_boxed_2248_; size_t v_i_boxed_2249_; lean_object* v_res_2250_; 
v_sz_boxed_2248_ = lean_unbox_usize(v_sz_2242_);
lean_dec(v_sz_2242_);
v_i_boxed_2249_ = lean_unbox_usize(v_i_2243_);
lean_dec(v_i_2243_);
v_res_2250_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(v_as_2241_, v_sz_boxed_2248_, v_i_boxed_2249_, v_b_2244_, v___y_2245_, v___y_2246_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec_ref(v_as_2241_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(lean_object* v_as_2251_, size_t v_i_2252_, size_t v_stop_2253_, lean_object* v_b_2254_){
_start:
{
uint8_t v___x_2255_; 
v___x_2255_ = lean_usize_dec_eq(v_i_2252_, v_stop_2253_);
if (v___x_2255_ == 0)
{
lean_object* v___x_2256_; lean_object* v_name_2257_; lean_object* v___x_2258_; size_t v___x_2259_; size_t v___x_2260_; 
v___x_2256_ = lean_array_uget_borrowed(v_as_2251_, v_i_2252_);
v_name_2257_ = lean_ctor_get(v___x_2256_, 0);
lean_inc(v_name_2257_);
v___x_2258_ = l_Lean_Compiler_LCNF_setDeclPublic(v_b_2254_, v_name_2257_);
v___x_2259_ = ((size_t)1ULL);
v___x_2260_ = lean_usize_add(v_i_2252_, v___x_2259_);
v_i_2252_ = v___x_2260_;
v_b_2254_ = v___x_2258_;
goto _start;
}
else
{
return v_b_2254_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___boxed(lean_object* v_as_2262_, lean_object* v_i_2263_, lean_object* v_stop_2264_, lean_object* v_b_2265_){
_start:
{
size_t v_i_boxed_2266_; size_t v_stop_boxed_2267_; lean_object* v_res_2268_; 
v_i_boxed_2266_ = lean_unbox_usize(v_i_2263_);
lean_dec(v_i_2263_);
v_stop_boxed_2267_ = lean_unbox_usize(v_stop_2264_);
lean_dec(v_stop_2264_);
v_res_2268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v_as_2262_, v_i_boxed_2266_, v_stop_boxed_2267_, v_b_2265_);
lean_dec_ref(v_as_2262_);
return v_res_2268_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0(uint8_t v_suppressElabErrors_2269_, uint8_t v___y_2270_, lean_object* v_x_2271_){
_start:
{
if (lean_obj_tag(v_x_2271_) == 1)
{
lean_object* v_pre_2272_; 
v_pre_2272_ = lean_ctor_get(v_x_2271_, 0);
switch(lean_obj_tag(v_pre_2272_))
{
case 1:
{
lean_object* v_pre_2273_; 
v_pre_2273_ = lean_ctor_get(v_pre_2272_, 0);
switch(lean_obj_tag(v_pre_2273_))
{
case 0:
{
lean_object* v_str_2274_; lean_object* v_str_2275_; lean_object* v___x_2276_; uint8_t v___x_2277_; 
v_str_2274_ = lean_ctor_get(v_x_2271_, 1);
v_str_2275_ = lean_ctor_get(v_pre_2272_, 1);
v___x_2276_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0));
v___x_2277_ = lean_string_dec_eq(v_str_2275_, v___x_2276_);
if (v___x_2277_ == 0)
{
lean_object* v___x_2278_; uint8_t v___x_2279_; 
v___x_2278_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1));
v___x_2279_ = lean_string_dec_eq(v_str_2275_, v___x_2278_);
if (v___x_2279_ == 0)
{
return v___x_2279_;
}
else
{
lean_object* v___x_2280_; uint8_t v___x_2281_; 
v___x_2280_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2));
v___x_2281_ = lean_string_dec_eq(v_str_2274_, v___x_2280_);
if (v___x_2281_ == 0)
{
return v___x_2281_;
}
else
{
return v_suppressElabErrors_2269_;
}
}
}
else
{
lean_object* v___x_2282_; uint8_t v___x_2283_; 
v___x_2282_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3));
v___x_2283_ = lean_string_dec_eq(v_str_2274_, v___x_2282_);
if (v___x_2283_ == 0)
{
return v___x_2283_;
}
else
{
return v_suppressElabErrors_2269_;
}
}
}
case 1:
{
lean_object* v_pre_2284_; 
v_pre_2284_ = lean_ctor_get(v_pre_2273_, 0);
if (lean_obj_tag(v_pre_2284_) == 0)
{
lean_object* v_str_2285_; lean_object* v_str_2286_; lean_object* v_str_2287_; lean_object* v___x_2288_; uint8_t v___x_2289_; 
v_str_2285_ = lean_ctor_get(v_x_2271_, 1);
v_str_2286_ = lean_ctor_get(v_pre_2272_, 1);
v_str_2287_ = lean_ctor_get(v_pre_2273_, 1);
v___x_2288_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4));
v___x_2289_ = lean_string_dec_eq(v_str_2287_, v___x_2288_);
if (v___x_2289_ == 0)
{
return v___x_2289_;
}
else
{
lean_object* v___x_2290_; uint8_t v___x_2291_; 
v___x_2290_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5));
v___x_2291_ = lean_string_dec_eq(v_str_2286_, v___x_2290_);
if (v___x_2291_ == 0)
{
return v___x_2291_;
}
else
{
lean_object* v___x_2292_; uint8_t v___x_2293_; 
v___x_2292_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6));
v___x_2293_ = lean_string_dec_eq(v_str_2285_, v___x_2292_);
if (v___x_2293_ == 0)
{
return v___x_2293_;
}
else
{
return v_suppressElabErrors_2269_;
}
}
}
}
else
{
return v___y_2270_;
}
}
default: 
{
return v___y_2270_;
}
}
}
case 0:
{
lean_object* v_str_2294_; lean_object* v___x_2295_; uint8_t v___x_2296_; 
v_str_2294_ = lean_ctor_get(v_x_2271_, 1);
v___x_2295_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_2296_ = lean_string_dec_eq(v_str_2294_, v___x_2295_);
if (v___x_2296_ == 0)
{
return v___x_2296_;
}
else
{
return v_suppressElabErrors_2269_;
}
}
default: 
{
return v___y_2270_;
}
}
}
else
{
return v___y_2270_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0___boxed(lean_object* v_suppressElabErrors_2297_, lean_object* v___y_2298_, lean_object* v_x_2299_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2300_; uint8_t v___y_38065__boxed_2301_; uint8_t v_res_2302_; lean_object* v_r_2303_; 
v_suppressElabErrors_boxed_2300_ = lean_unbox(v_suppressElabErrors_2297_);
v___y_38065__boxed_2301_ = lean_unbox(v___y_2298_);
v_res_2302_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0(v_suppressElabErrors_boxed_2300_, v___y_38065__boxed_2301_, v_x_2299_);
lean_dec(v_x_2299_);
v_r_2303_ = lean_box(v_res_2302_);
return v_r_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(lean_object* v_ref_2304_, lean_object* v_msgData_2305_, uint8_t v_severity_2306_, uint8_t v_isSilent_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v___y_2312_; lean_object* v___y_2313_; lean_object* v___y_2314_; lean_object* v___y_2315_; uint8_t v___y_2316_; lean_object* v___y_2317_; uint8_t v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2349_; lean_object* v___y_2350_; uint8_t v___y_2351_; lean_object* v___y_2352_; uint8_t v___y_2353_; lean_object* v___y_2354_; uint8_t v___y_2355_; lean_object* v___y_2356_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2376_; uint8_t v___y_2377_; uint8_t v___y_2378_; lean_object* v___y_2379_; uint8_t v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2387_; uint8_t v___y_2388_; lean_object* v___y_2389_; uint8_t v___y_2390_; uint8_t v___y_2391_; uint8_t v___x_2396_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; uint8_t v___y_2402_; uint8_t v___y_2403_; uint8_t v___y_2404_; uint8_t v___y_2406_; uint8_t v___x_2422_; 
v___x_2396_ = 2;
v___x_2422_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2306_, v___x_2396_);
if (v___x_2422_ == 0)
{
v___y_2406_ = v___x_2422_;
goto v___jp_2405_;
}
else
{
uint8_t v___x_2423_; 
lean_inc_ref(v_msgData_2305_);
v___x_2423_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2305_);
v___y_2406_ = v___x_2423_;
goto v___jp_2405_;
}
v___jp_2311_:
{
lean_object* v___x_2321_; lean_object* v_toCold_2322_; lean_object* v_currNamespace_2323_; lean_object* v_openDecls_2324_; lean_object* v_env_2325_; lean_object* v_nextMacroScope_2326_; lean_object* v_ngen_2327_; lean_object* v_auxDeclNGen_2328_; lean_object* v_traceState_2329_; lean_object* v_cache_2330_; lean_object* v_messages_2331_; lean_object* v_infoState_2332_; lean_object* v_snapshotTasks_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2347_; 
v___x_2321_ = lean_st_ref_take(v___y_2320_);
v_toCold_2322_ = lean_ctor_get(v___y_2319_, 0);
v_currNamespace_2323_ = lean_ctor_get(v_toCold_2322_, 4);
v_openDecls_2324_ = lean_ctor_get(v_toCold_2322_, 5);
v_env_2325_ = lean_ctor_get(v___x_2321_, 0);
v_nextMacroScope_2326_ = lean_ctor_get(v___x_2321_, 1);
v_ngen_2327_ = lean_ctor_get(v___x_2321_, 2);
v_auxDeclNGen_2328_ = lean_ctor_get(v___x_2321_, 3);
v_traceState_2329_ = lean_ctor_get(v___x_2321_, 4);
v_cache_2330_ = lean_ctor_get(v___x_2321_, 5);
v_messages_2331_ = lean_ctor_get(v___x_2321_, 6);
v_infoState_2332_ = lean_ctor_get(v___x_2321_, 7);
v_snapshotTasks_2333_ = lean_ctor_get(v___x_2321_, 8);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2335_ = v___x_2321_;
v_isShared_2336_ = v_isSharedCheck_2347_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_snapshotTasks_2333_);
lean_inc(v_infoState_2332_);
lean_inc(v_messages_2331_);
lean_inc(v_cache_2330_);
lean_inc(v_traceState_2329_);
lean_inc(v_auxDeclNGen_2328_);
lean_inc(v_ngen_2327_);
lean_inc(v_nextMacroScope_2326_);
lean_inc(v_env_2325_);
lean_dec(v___x_2321_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2347_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2342_; 
lean_inc(v_openDecls_2324_);
lean_inc(v_currNamespace_2323_);
v___x_2337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2337_, 0, v_currNamespace_2323_);
lean_ctor_set(v___x_2337_, 1, v_openDecls_2324_);
v___x_2338_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2337_);
lean_ctor_set(v___x_2338_, 1, v___y_2315_);
lean_inc_ref(v___y_2313_);
lean_inc_ref(v___y_2317_);
v___x_2339_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2339_, 0, v___y_2317_);
lean_ctor_set(v___x_2339_, 1, v___y_2314_);
lean_ctor_set(v___x_2339_, 2, v___y_2312_);
lean_ctor_set(v___x_2339_, 3, v___y_2313_);
lean_ctor_set(v___x_2339_, 4, v___x_2338_);
lean_ctor_set_uint8(v___x_2339_, sizeof(void*)*5, v___y_2318_);
lean_ctor_set_uint8(v___x_2339_, sizeof(void*)*5 + 1, v___y_2316_);
lean_ctor_set_uint8(v___x_2339_, sizeof(void*)*5 + 2, v_isSilent_2307_);
v___x_2340_ = l_Lean_MessageLog_add(v___x_2339_, v_messages_2331_);
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 6, v___x_2340_);
v___x_2342_ = v___x_2335_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_env_2325_);
lean_ctor_set(v_reuseFailAlloc_2346_, 1, v_nextMacroScope_2326_);
lean_ctor_set(v_reuseFailAlloc_2346_, 2, v_ngen_2327_);
lean_ctor_set(v_reuseFailAlloc_2346_, 3, v_auxDeclNGen_2328_);
lean_ctor_set(v_reuseFailAlloc_2346_, 4, v_traceState_2329_);
lean_ctor_set(v_reuseFailAlloc_2346_, 5, v_cache_2330_);
lean_ctor_set(v_reuseFailAlloc_2346_, 6, v___x_2340_);
lean_ctor_set(v_reuseFailAlloc_2346_, 7, v_infoState_2332_);
lean_ctor_set(v_reuseFailAlloc_2346_, 8, v_snapshotTasks_2333_);
v___x_2342_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2343_ = lean_st_ref_put(v___y_2320_, v___x_2342_);
v___x_2344_ = lean_box(0);
v___x_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2344_);
return v___x_2345_;
}
}
}
v___jp_2348_:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v_a_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2372_; 
v___x_2357_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2305_);
v___x_2358_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(v___x_2357_, v___y_2308_, v___y_2309_);
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2361_ = v___x_2358_;
v_isShared_2362_ = v_isSharedCheck_2372_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_dec(v___x_2358_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2372_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
lean_inc_ref_n(v___y_2350_, 2);
v___x_2363_ = l_Lean_FileMap_toPosition(v___y_2350_, v___y_2352_);
lean_dec(v___y_2352_);
v___x_2364_ = l_Lean_FileMap_toPosition(v___y_2350_, v___y_2356_);
lean_dec(v___y_2356_);
v___x_2365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2364_);
v___x_2366_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1));
if (v___y_2351_ == 0)
{
lean_del_object(v___x_2361_);
lean_dec_ref(v___y_2349_);
v___y_2312_ = v___x_2365_;
v___y_2313_ = v___x_2366_;
v___y_2314_ = v___x_2363_;
v___y_2315_ = v_a_2359_;
v___y_2316_ = v___y_2353_;
v___y_2317_ = v___y_2354_;
v___y_2318_ = v___y_2355_;
v___y_2319_ = v___y_2308_;
v___y_2320_ = v___y_2309_;
goto v___jp_2311_;
}
else
{
uint8_t v___x_2367_; 
lean_inc(v_a_2359_);
v___x_2367_ = l_Lean_MessageData_hasTag(v___y_2349_, v_a_2359_);
if (v___x_2367_ == 0)
{
lean_object* v___x_2368_; lean_object* v___x_2370_; 
lean_dec_ref_known(v___x_2365_, 1);
lean_dec_ref(v___x_2363_);
lean_dec(v_a_2359_);
v___x_2368_ = lean_box(0);
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 0, v___x_2368_);
v___x_2370_ = v___x_2361_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v___x_2368_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
else
{
lean_del_object(v___x_2361_);
v___y_2312_ = v___x_2365_;
v___y_2313_ = v___x_2366_;
v___y_2314_ = v___x_2363_;
v___y_2315_ = v_a_2359_;
v___y_2316_ = v___y_2353_;
v___y_2317_ = v___y_2354_;
v___y_2318_ = v___y_2355_;
v___y_2319_ = v___y_2308_;
v___y_2320_ = v___y_2309_;
goto v___jp_2311_;
}
}
}
}
v___jp_2373_:
{
lean_object* v___x_2382_; 
v___x_2382_ = l_Lean_Syntax_getTailPos_x3f(v___y_2375_, v___y_2380_);
lean_dec(v___y_2375_);
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_inc(v___y_2381_);
v___y_2349_ = v___y_2374_;
v___y_2350_ = v___y_2376_;
v___y_2351_ = v___y_2377_;
v___y_2352_ = v___y_2381_;
v___y_2353_ = v___y_2378_;
v___y_2354_ = v___y_2379_;
v___y_2355_ = v___y_2380_;
v___y_2356_ = v___y_2381_;
goto v___jp_2348_;
}
else
{
lean_object* v_val_2383_; 
v_val_2383_ = lean_ctor_get(v___x_2382_, 0);
lean_inc(v_val_2383_);
lean_dec_ref_known(v___x_2382_, 1);
v___y_2349_ = v___y_2374_;
v___y_2350_ = v___y_2376_;
v___y_2351_ = v___y_2377_;
v___y_2352_ = v___y_2381_;
v___y_2353_ = v___y_2378_;
v___y_2354_ = v___y_2379_;
v___y_2355_ = v___y_2380_;
v___y_2356_ = v_val_2383_;
goto v___jp_2348_;
}
}
v___jp_2384_:
{
lean_object* v_ref_2392_; lean_object* v___x_2393_; 
v_ref_2392_ = l_Lean_replaceRef(v_ref_2304_, v___y_2387_);
v___x_2393_ = l_Lean_Syntax_getPos_x3f(v_ref_2392_, v___y_2390_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v___x_2394_; 
v___x_2394_ = lean_unsigned_to_nat(0u);
v___y_2374_ = v___y_2385_;
v___y_2375_ = v_ref_2392_;
v___y_2376_ = v___y_2386_;
v___y_2377_ = v___y_2388_;
v___y_2378_ = v___y_2391_;
v___y_2379_ = v___y_2389_;
v___y_2380_ = v___y_2390_;
v___y_2381_ = v___x_2394_;
goto v___jp_2373_;
}
else
{
lean_object* v_val_2395_; 
v_val_2395_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_val_2395_);
lean_dec_ref_known(v___x_2393_, 1);
v___y_2374_ = v___y_2385_;
v___y_2375_ = v_ref_2392_;
v___y_2376_ = v___y_2386_;
v___y_2377_ = v___y_2388_;
v___y_2378_ = v___y_2391_;
v___y_2379_ = v___y_2389_;
v___y_2380_ = v___y_2390_;
v___y_2381_ = v_val_2395_;
goto v___jp_2373_;
}
}
v___jp_2397_:
{
if (v___y_2404_ == 0)
{
v___y_2385_ = v___y_2398_;
v___y_2386_ = v___y_2399_;
v___y_2387_ = v___y_2401_;
v___y_2388_ = v___y_2402_;
v___y_2389_ = v___y_2400_;
v___y_2390_ = v___y_2403_;
v___y_2391_ = v_severity_2306_;
goto v___jp_2384_;
}
else
{
v___y_2385_ = v___y_2398_;
v___y_2386_ = v___y_2399_;
v___y_2387_ = v___y_2401_;
v___y_2388_ = v___y_2402_;
v___y_2389_ = v___y_2400_;
v___y_2390_ = v___y_2403_;
v___y_2391_ = v___x_2396_;
goto v___jp_2384_;
}
}
v___jp_2405_:
{
if (v___y_2406_ == 0)
{
lean_object* v_toCold_2407_; lean_object* v_ref_2408_; uint8_t v_suppressElabErrors_2409_; lean_object* v_fileName_2410_; lean_object* v_fileMap_2411_; lean_object* v_options_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___f_2415_; uint8_t v___x_2416_; uint8_t v___x_2417_; 
v_toCold_2407_ = lean_ctor_get(v___y_2308_, 0);
v_ref_2408_ = lean_ctor_get(v___y_2308_, 2);
v_suppressElabErrors_2409_ = lean_ctor_get_uint8(v___y_2308_, sizeof(void*)*3 + 1);
v_fileName_2410_ = lean_ctor_get(v_toCold_2407_, 0);
v_fileMap_2411_ = lean_ctor_get(v_toCold_2407_, 1);
v_options_2412_ = lean_ctor_get(v_toCold_2407_, 2);
v___x_2413_ = lean_box(v_suppressElabErrors_2409_);
v___x_2414_ = lean_box(v___y_2406_);
v___f_2415_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2415_, 0, v___x_2413_);
lean_closure_set(v___f_2415_, 1, v___x_2414_);
v___x_2416_ = 1;
v___x_2417_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2306_, v___x_2416_);
if (v___x_2417_ == 0)
{
v___y_2398_ = v___f_2415_;
v___y_2399_ = v_fileMap_2411_;
v___y_2400_ = v_fileName_2410_;
v___y_2401_ = v_ref_2408_;
v___y_2402_ = v_suppressElabErrors_2409_;
v___y_2403_ = v___y_2406_;
v___y_2404_ = v___x_2417_;
goto v___jp_2397_;
}
else
{
lean_object* v___x_2418_; uint8_t v___x_2419_; 
v___x_2418_ = l_Lean_warningAsError;
v___x_2419_ = l_Lean_Option_get___at___00main_spec__8(v_options_2412_, v___x_2418_);
v___y_2398_ = v___f_2415_;
v___y_2399_ = v_fileMap_2411_;
v___y_2400_ = v_fileName_2410_;
v___y_2401_ = v_ref_2408_;
v___y_2402_ = v_suppressElabErrors_2409_;
v___y_2403_ = v___y_2406_;
v___y_2404_ = v___x_2419_;
goto v___jp_2397_;
}
}
else
{
lean_object* v___x_2420_; lean_object* v___x_2421_; 
lean_dec_ref(v_msgData_2305_);
v___x_2420_ = lean_box(0);
v___x_2421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2421_, 0, v___x_2420_);
return v___x_2421_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___boxed(lean_object* v_ref_2424_, lean_object* v_msgData_2425_, lean_object* v_severity_2426_, lean_object* v_isSilent_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
uint8_t v_severity_boxed_2431_; uint8_t v_isSilent_boxed_2432_; lean_object* v_res_2433_; 
v_severity_boxed_2431_ = lean_unbox(v_severity_2426_);
v_isSilent_boxed_2432_ = lean_unbox(v_isSilent_2427_);
v_res_2433_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(v_ref_2424_, v_msgData_2425_, v_severity_boxed_2431_, v_isSilent_boxed_2432_, v___y_2428_, v___y_2429_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec(v_ref_2424_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(lean_object* v_msgData_2434_, uint8_t v_severity_2435_, uint8_t v_isSilent_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_){
_start:
{
lean_object* v_ref_2440_; lean_object* v___x_2441_; 
v_ref_2440_ = lean_ctor_get(v___y_2437_, 2);
v___x_2441_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(v_ref_2440_, v_msgData_2434_, v_severity_2435_, v_isSilent_2436_, v___y_2437_, v___y_2438_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30___boxed(lean_object* v_msgData_2442_, lean_object* v_severity_2443_, lean_object* v_isSilent_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
uint8_t v_severity_boxed_2448_; uint8_t v_isSilent_boxed_2449_; lean_object* v_res_2450_; 
v_severity_boxed_2448_ = lean_unbox(v_severity_2443_);
v_isSilent_boxed_2449_ = lean_unbox(v_isSilent_2444_);
v_res_2450_ = l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(v_msgData_2442_, v_severity_boxed_2448_, v_isSilent_boxed_2449_, v___y_2445_, v___y_2446_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__14(lean_object* v_msgData_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
uint8_t v___x_2455_; uint8_t v___x_2456_; lean_object* v___x_2457_; 
v___x_2455_ = 2;
v___x_2456_ = 0;
v___x_2457_ = l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(v_msgData_2451_, v___x_2455_, v___x_2456_, v___y_2452_, v___y_2453_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__14___boxed(lean_object* v_msgData_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l_Lean_logError___at___00main_spec__14(v_msgData_2458_, v___y_2459_, v___y_2460_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(lean_object* v_x2_2463_, lean_object* v_as_2464_, size_t v_i_2465_, size_t v_stop_2466_, lean_object* v_b_2467_){
_start:
{
uint8_t v___x_2468_; 
v___x_2468_ = lean_usize_dec_eq(v_i_2465_, v_stop_2466_);
if (v___x_2468_ == 0)
{
lean_object* v___x_2469_; lean_object* v___x_2470_; size_t v___x_2471_; size_t v___x_2472_; 
v___x_2469_ = lean_array_uget_borrowed(v_as_2464_, v_i_2465_);
lean_inc_ref(v_x2_2463_);
lean_inc(v___x_2469_);
v___x_2470_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2469_, v_x2_2463_, v_b_2467_);
v___x_2471_ = ((size_t)1ULL);
v___x_2472_ = lean_usize_add(v_i_2465_, v___x_2471_);
v_i_2465_ = v___x_2472_;
v_b_2467_ = v___x_2470_;
goto _start;
}
else
{
lean_dec_ref(v_x2_2463_);
return v_b_2467_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2___boxed(lean_object* v_x2_2474_, lean_object* v_as_2475_, lean_object* v_i_2476_, lean_object* v_stop_2477_, lean_object* v_b_2478_){
_start:
{
size_t v_i_boxed_2479_; size_t v_stop_boxed_2480_; lean_object* v_res_2481_; 
v_i_boxed_2479_ = lean_unbox_usize(v_i_2476_);
lean_dec(v_i_2476_);
v_stop_boxed_2480_ = lean_unbox_usize(v_stop_2477_);
lean_dec(v_stop_2477_);
v_res_2481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v_x2_2474_, v_as_2475_, v_i_boxed_2479_, v_stop_boxed_2480_, v_b_2478_);
lean_dec_ref(v_as_2475_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(lean_object* v_as_2482_, size_t v_i_2483_, size_t v_stop_2484_, lean_object* v_b_2485_){
_start:
{
lean_object* v___y_2487_; uint8_t v___x_2491_; 
v___x_2491_ = lean_usize_dec_eq(v_i_2483_, v_stop_2484_);
if (v___x_2491_ == 0)
{
lean_object* v___x_2492_; lean_object* v_declNames_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; uint8_t v___x_2496_; 
v___x_2492_ = lean_array_uget_borrowed(v_as_2482_, v_i_2483_);
v_declNames_2493_ = lean_ctor_get(v___x_2492_, 0);
v___x_2494_ = lean_unsigned_to_nat(0u);
v___x_2495_ = lean_array_get_size(v_declNames_2493_);
v___x_2496_ = lean_nat_dec_lt(v___x_2494_, v___x_2495_);
if (v___x_2496_ == 0)
{
v___y_2487_ = v_b_2485_;
goto v___jp_2486_;
}
else
{
uint8_t v___x_2497_; 
v___x_2497_ = lean_nat_dec_le(v___x_2495_, v___x_2495_);
if (v___x_2497_ == 0)
{
if (v___x_2496_ == 0)
{
v___y_2487_ = v_b_2485_;
goto v___jp_2486_;
}
else
{
size_t v___x_2498_; size_t v___x_2499_; lean_object* v___x_2500_; 
v___x_2498_ = ((size_t)0ULL);
v___x_2499_ = lean_usize_of_nat(v___x_2495_);
lean_inc(v___x_2492_);
v___x_2500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_2492_, v_declNames_2493_, v___x_2498_, v___x_2499_, v_b_2485_);
v___y_2487_ = v___x_2500_;
goto v___jp_2486_;
}
}
else
{
size_t v___x_2501_; size_t v___x_2502_; lean_object* v___x_2503_; 
v___x_2501_ = ((size_t)0ULL);
v___x_2502_ = lean_usize_of_nat(v___x_2495_);
lean_inc(v___x_2492_);
v___x_2503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_2492_, v_declNames_2493_, v___x_2501_, v___x_2502_, v_b_2485_);
v___y_2487_ = v___x_2503_;
goto v___jp_2486_;
}
}
}
else
{
return v_b_2485_;
}
v___jp_2486_:
{
size_t v___x_2488_; size_t v___x_2489_; 
v___x_2488_ = ((size_t)1ULL);
v___x_2489_ = lean_usize_add(v_i_2483_, v___x_2488_);
v_i_2483_ = v___x_2489_;
v_b_2485_ = v___y_2487_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___boxed(lean_object* v_as_2504_, lean_object* v_i_2505_, lean_object* v_stop_2506_, lean_object* v_b_2507_){
_start:
{
size_t v_i_boxed_2508_; size_t v_stop_boxed_2509_; lean_object* v_res_2510_; 
v_i_boxed_2508_ = lean_unbox_usize(v_i_2505_);
lean_dec(v_i_2505_);
v_stop_boxed_2509_ = lean_unbox_usize(v_stop_2506_);
lean_dec(v_stop_2506_);
v_res_2510_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v_as_2504_, v_i_boxed_2508_, v_stop_boxed_2509_, v_b_2507_);
lean_dec_ref(v_as_2504_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(lean_object* v_a_2511_, lean_object* v_as_2512_, size_t v_i_2513_, size_t v_stop_2514_, lean_object* v_b_2515_){
_start:
{
lean_object* v___y_2517_; uint8_t v___x_2521_; 
v___x_2521_ = lean_usize_dec_eq(v_i_2513_, v_stop_2514_);
if (v___x_2521_ == 0)
{
lean_object* v___x_2522_; lean_object* v_name_2523_; uint8_t v___x_2524_; 
v___x_2522_ = lean_array_uget_borrowed(v_as_2512_, v_i_2513_);
v_name_2523_ = lean_ctor_get(v___x_2522_, 0);
lean_inc(v_name_2523_);
lean_inc_ref(v_a_2511_);
v___x_2524_ = l_Lean_isExtern(v_a_2511_, v_name_2523_);
if (v___x_2524_ == 0)
{
v___y_2517_ = v_b_2515_;
goto v___jp_2516_;
}
else
{
lean_object* v___x_2525_; 
lean_inc(v___x_2522_);
v___x_2525_ = lean_array_push(v_b_2515_, v___x_2522_);
v___y_2517_ = v___x_2525_;
goto v___jp_2516_;
}
}
else
{
lean_dec_ref(v_a_2511_);
return v_b_2515_;
}
v___jp_2516_:
{
size_t v___x_2518_; size_t v___x_2519_; 
v___x_2518_ = ((size_t)1ULL);
v___x_2519_ = lean_usize_add(v_i_2513_, v___x_2518_);
v_i_2513_ = v___x_2519_;
v_b_2515_ = v___y_2517_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19___boxed(lean_object* v_a_2526_, lean_object* v_as_2527_, lean_object* v_i_2528_, lean_object* v_stop_2529_, lean_object* v_b_2530_){
_start:
{
size_t v_i_boxed_2531_; size_t v_stop_boxed_2532_; lean_object* v_res_2533_; 
v_i_boxed_2531_ = lean_unbox_usize(v_i_2528_);
lean_dec(v_i_2528_);
v_stop_boxed_2532_ = lean_unbox_usize(v_stop_2529_);
lean_dec(v_stop_2529_);
v_res_2533_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_2526_, v_as_2527_, v_i_boxed_2531_, v_stop_boxed_2532_, v_b_2530_);
lean_dec_ref(v_as_2527_);
return v_res_2533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(lean_object* v_as_2534_, size_t v_sz_2535_, size_t v_i_2536_, lean_object* v_b_2537_){
_start:
{
uint8_t v___x_2539_; 
v___x_2539_ = lean_usize_dec_lt(v_i_2536_, v_sz_2535_);
if (v___x_2539_ == 0)
{
lean_object* v___x_2540_; 
v___x_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2540_, 0, v_b_2537_);
return v___x_2540_;
}
else
{
uint8_t v___x_2541_; lean_object* v_a_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
lean_dec_ref(v_b_2537_);
v___x_2541_ = 0;
v_a_2542_ = lean_array_uget_borrowed(v_as_2534_, v_i_2536_);
lean_inc(v_a_2542_);
v___x_2543_ = l_Lean_Message_toString(v_a_2542_, v___x_2541_);
v___x_2544_ = l_IO_eprintln___at___00main_spec__6(v___x_2543_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v___x_2545_; size_t v___x_2546_; size_t v___x_2547_; 
lean_dec_ref_known(v___x_2544_, 1);
v___x_2545_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_2546_ = ((size_t)1ULL);
v___x_2547_ = lean_usize_add(v_i_2536_, v___x_2546_);
v_i_2536_ = v___x_2547_;
v_b_2537_ = v___x_2545_;
goto _start;
}
else
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
v_a_2549_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2551_ = v___x_2544_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2544_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_a_2549_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27___boxed(lean_object* v_as_2557_, lean_object* v_sz_2558_, lean_object* v_i_2559_, lean_object* v_b_2560_, lean_object* v___y_2561_){
_start:
{
size_t v_sz_boxed_2562_; size_t v_i_boxed_2563_; lean_object* v_res_2564_; 
v_sz_boxed_2562_ = lean_unbox_usize(v_sz_2558_);
lean_dec(v_sz_2558_);
v_i_boxed_2563_ = lean_unbox_usize(v_i_2559_);
lean_dec(v_i_2559_);
v_res_2564_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(v_as_2557_, v_sz_boxed_2562_, v_i_boxed_2563_, v_b_2560_);
lean_dec_ref(v_as_2557_);
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(lean_object* v_as_2565_, size_t v_sz_2566_, size_t v_i_2567_, lean_object* v_b_2568_){
_start:
{
uint8_t v___x_2570_; 
v___x_2570_ = lean_usize_dec_lt(v_i_2567_, v_sz_2566_);
if (v___x_2570_ == 0)
{
lean_object* v___x_2571_; 
v___x_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2571_, 0, v_b_2568_);
return v___x_2571_;
}
else
{
uint8_t v___x_2572_; lean_object* v_a_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
lean_dec_ref(v_b_2568_);
v___x_2572_ = 0;
v_a_2573_ = lean_array_uget_borrowed(v_as_2565_, v_i_2567_);
lean_inc(v_a_2573_);
v___x_2574_ = l_Lean_Message_toString(v_a_2573_, v___x_2572_);
v___x_2575_ = l_IO_eprintln___at___00main_spec__6(v___x_2574_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v___x_2576_; size_t v___x_2577_; size_t v___x_2578_; lean_object* v___x_2579_; 
lean_dec_ref_known(v___x_2575_, 1);
v___x_2576_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_2577_ = ((size_t)1ULL);
v___x_2578_ = lean_usize_add(v_i_2567_, v___x_2577_);
v___x_2579_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(v_as_2565_, v_sz_2566_, v___x_2578_, v___x_2576_);
return v___x_2579_;
}
else
{
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2587_; 
v_a_2580_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2582_ = v___x_2575_;
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2575_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2585_; 
if (v_isShared_2583_ == 0)
{
v___x_2585_ = v___x_2582_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2580_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14___boxed(lean_object* v_as_2588_, lean_object* v_sz_2589_, lean_object* v_i_2590_, lean_object* v_b_2591_, lean_object* v___y_2592_){
_start:
{
size_t v_sz_boxed_2593_; size_t v_i_boxed_2594_; lean_object* v_res_2595_; 
v_sz_boxed_2593_ = lean_unbox_usize(v_sz_2589_);
lean_dec(v_sz_2589_);
v_i_boxed_2594_ = lean_unbox_usize(v_i_2590_);
lean_dec(v_i_2590_);
v_res_2595_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(v_as_2588_, v_sz_boxed_2593_, v_i_boxed_2594_, v_b_2591_);
lean_dec_ref(v_as_2588_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(lean_object* v_init_2596_, lean_object* v_n_2597_, lean_object* v_b_2598_){
_start:
{
if (lean_obj_tag(v_n_2597_) == 0)
{
lean_object* v_cs_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; size_t v_sz_2603_; size_t v___x_2604_; lean_object* v___x_2605_; 
v_cs_2600_ = lean_ctor_get(v_n_2597_, 0);
v___x_2601_ = lean_box(0);
v___x_2602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2601_);
lean_ctor_set(v___x_2602_, 1, v_b_2598_);
v_sz_2603_ = lean_array_size(v_cs_2600_);
v___x_2604_ = ((size_t)0ULL);
v___x_2605_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_init_2596_, v_cs_2600_, v_sz_2603_, v___x_2604_, v___x_2602_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2620_; 
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2608_ = v___x_2605_;
v_isShared_2609_ = v_isSharedCheck_2620_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2605_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2620_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v_fst_2610_; 
v_fst_2610_ = lean_ctor_get(v_a_2606_, 0);
if (lean_obj_tag(v_fst_2610_) == 0)
{
lean_object* v_snd_2611_; lean_object* v___x_2612_; lean_object* v___x_2614_; 
v_snd_2611_ = lean_ctor_get(v_a_2606_, 1);
lean_inc(v_snd_2611_);
lean_dec(v_a_2606_);
v___x_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2612_, 0, v_snd_2611_);
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 0, v___x_2612_);
v___x_2614_ = v___x_2608_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v___x_2612_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
else
{
lean_object* v_val_2616_; lean_object* v___x_2618_; 
lean_inc_ref(v_fst_2610_);
lean_dec(v_a_2606_);
v_val_2616_ = lean_ctor_get(v_fst_2610_, 0);
lean_inc(v_val_2616_);
lean_dec_ref_known(v_fst_2610_, 1);
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 0, v_val_2616_);
v___x_2618_ = v___x_2608_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_val_2616_);
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
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
v_a_2621_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2605_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2605_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2621_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
else
{
lean_object* v_vs_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; size_t v_sz_2632_; size_t v___x_2633_; lean_object* v___x_2634_; 
v_vs_2629_ = lean_ctor_get(v_n_2597_, 0);
v___x_2630_ = lean_box(0);
v___x_2631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2630_);
lean_ctor_set(v___x_2631_, 1, v_b_2598_);
v_sz_2632_ = lean_array_size(v_vs_2629_);
v___x_2633_ = ((size_t)0ULL);
v___x_2634_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(v_vs_2629_, v_sz_2632_, v___x_2633_, v___x_2631_);
if (lean_obj_tag(v___x_2634_) == 0)
{
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2649_; 
v_a_2635_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2637_ = v___x_2634_;
v_isShared_2638_ = v_isSharedCheck_2649_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2634_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2649_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v_fst_2639_; 
v_fst_2639_ = lean_ctor_get(v_a_2635_, 0);
if (lean_obj_tag(v_fst_2639_) == 0)
{
lean_object* v_snd_2640_; lean_object* v___x_2641_; lean_object* v___x_2643_; 
v_snd_2640_ = lean_ctor_get(v_a_2635_, 1);
lean_inc(v_snd_2640_);
lean_dec(v_a_2635_);
v___x_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2641_, 0, v_snd_2640_);
if (v_isShared_2638_ == 0)
{
lean_ctor_set(v___x_2637_, 0, v___x_2641_);
v___x_2643_ = v___x_2637_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2641_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
else
{
lean_object* v_val_2645_; lean_object* v___x_2647_; 
lean_inc_ref(v_fst_2639_);
lean_dec(v_a_2635_);
v_val_2645_ = lean_ctor_get(v_fst_2639_, 0);
lean_inc(v_val_2645_);
lean_dec_ref_known(v_fst_2639_, 1);
if (v_isShared_2638_ == 0)
{
lean_ctor_set(v___x_2637_, 0, v_val_2645_);
v___x_2647_ = v___x_2637_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_val_2645_);
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
else
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2657_; 
v_a_2650_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2652_ = v___x_2634_;
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2634_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2655_; 
if (v_isShared_2653_ == 0)
{
v___x_2655_ = v___x_2652_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_a_2650_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(lean_object* v_init_2658_, lean_object* v_as_2659_, size_t v_sz_2660_, size_t v_i_2661_, lean_object* v_b_2662_){
_start:
{
uint8_t v___x_2664_; 
v___x_2664_ = lean_usize_dec_lt(v_i_2661_, v_sz_2660_);
if (v___x_2664_ == 0)
{
lean_object* v___x_2665_; 
v___x_2665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2665_, 0, v_b_2662_);
return v___x_2665_;
}
else
{
lean_object* v_snd_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2700_; 
v_snd_2666_ = lean_ctor_get(v_b_2662_, 1);
v_isSharedCheck_2700_ = !lean_is_exclusive(v_b_2662_);
if (v_isSharedCheck_2700_ == 0)
{
lean_object* v_unused_2701_; 
v_unused_2701_ = lean_ctor_get(v_b_2662_, 0);
lean_dec(v_unused_2701_);
v___x_2668_ = v_b_2662_;
v_isShared_2669_ = v_isSharedCheck_2700_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_snd_2666_);
lean_dec(v_b_2662_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2700_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v_a_2670_; lean_object* v___x_2671_; 
v_a_2670_ = lean_array_uget_borrowed(v_as_2659_, v_i_2661_);
lean_inc(v_snd_2666_);
v___x_2671_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2658_, v_a_2670_, v_snd_2666_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2691_; 
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2674_ = v___x_2671_;
v_isShared_2675_ = v_isSharedCheck_2691_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2671_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2691_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
if (lean_obj_tag(v_a_2672_) == 0)
{
lean_object* v___x_2676_; lean_object* v___x_2678_; 
v___x_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2676_, 0, v_a_2672_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 0, v___x_2676_);
v___x_2678_ = v___x_2668_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v___x_2676_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v_snd_2666_);
v___x_2678_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
lean_object* v___x_2680_; 
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 0, v___x_2678_);
v___x_2680_ = v___x_2674_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2678_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
else
{
lean_object* v_a_2683_; lean_object* v___x_2684_; lean_object* v___x_2686_; 
lean_del_object(v___x_2674_);
lean_dec(v_snd_2666_);
v_a_2683_ = lean_ctor_get(v_a_2672_, 0);
lean_inc(v_a_2683_);
lean_dec_ref_known(v_a_2672_, 1);
v___x_2684_ = lean_box(0);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 1, v_a_2683_);
lean_ctor_set(v___x_2668_, 0, v___x_2684_);
v___x_2686_ = v___x_2668_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___x_2684_);
lean_ctor_set(v_reuseFailAlloc_2690_, 1, v_a_2683_);
v___x_2686_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
size_t v___x_2687_; size_t v___x_2688_; 
v___x_2687_ = ((size_t)1ULL);
v___x_2688_ = lean_usize_add(v_i_2661_, v___x_2687_);
v_i_2661_ = v___x_2688_;
v_b_2662_ = v___x_2686_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2699_; 
lean_del_object(v___x_2668_);
lean_dec(v_snd_2666_);
v_a_2692_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2694_ = v___x_2671_;
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v___x_2671_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2697_; 
if (v_isShared_2695_ == 0)
{
v___x_2697_ = v___x_2694_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_a_2692_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13___boxed(lean_object* v_init_2702_, lean_object* v_as_2703_, lean_object* v_sz_2704_, lean_object* v_i_2705_, lean_object* v_b_2706_, lean_object* v___y_2707_){
_start:
{
size_t v_sz_boxed_2708_; size_t v_i_boxed_2709_; lean_object* v_res_2710_; 
v_sz_boxed_2708_ = lean_unbox_usize(v_sz_2704_);
lean_dec(v_sz_2704_);
v_i_boxed_2709_ = lean_unbox_usize(v_i_2705_);
lean_dec(v_i_2705_);
v_res_2710_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_init_2702_, v_as_2703_, v_sz_boxed_2708_, v_i_boxed_2709_, v_b_2706_);
lean_dec_ref(v_as_2703_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10___boxed(lean_object* v_init_2711_, lean_object* v_n_2712_, lean_object* v_b_2713_, lean_object* v___y_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2711_, v_n_2712_, v_b_2713_);
lean_dec_ref(v_n_2712_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(lean_object* v_as_2716_, size_t v_sz_2717_, size_t v_i_2718_, lean_object* v_b_2719_){
_start:
{
uint8_t v___x_2721_; 
v___x_2721_ = lean_usize_dec_lt(v_i_2718_, v_sz_2717_);
if (v___x_2721_ == 0)
{
lean_object* v___x_2722_; 
v___x_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2722_, 0, v_b_2719_);
return v___x_2722_;
}
else
{
uint8_t v___x_2723_; lean_object* v_a_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
lean_dec_ref(v_b_2719_);
v___x_2723_ = 0;
v_a_2724_ = lean_array_uget_borrowed(v_as_2716_, v_i_2718_);
lean_inc(v_a_2724_);
v___x_2725_ = l_Lean_Message_toString(v_a_2724_, v___x_2723_);
v___x_2726_ = l_IO_eprintln___at___00main_spec__6(v___x_2725_);
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_object* v___x_2727_; size_t v___x_2728_; size_t v___x_2729_; 
lean_dec_ref_known(v___x_2726_, 1);
v___x_2727_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_2728_ = ((size_t)1ULL);
v___x_2729_ = lean_usize_add(v_i_2718_, v___x_2728_);
v_i_2718_ = v___x_2729_;
v_b_2719_ = v___x_2727_;
goto _start;
}
else
{
lean_object* v_a_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2738_; 
v_a_2731_ = lean_ctor_get(v___x_2726_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2726_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2733_ = v___x_2726_;
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_a_2731_);
lean_dec(v___x_2726_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2736_; 
if (v_isShared_2734_ == 0)
{
v___x_2736_ = v___x_2733_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_a_2731_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16___boxed(lean_object* v_as_2739_, lean_object* v_sz_2740_, lean_object* v_i_2741_, lean_object* v_b_2742_, lean_object* v___y_2743_){
_start:
{
size_t v_sz_boxed_2744_; size_t v_i_boxed_2745_; lean_object* v_res_2746_; 
v_sz_boxed_2744_ = lean_unbox_usize(v_sz_2740_);
lean_dec(v_sz_2740_);
v_i_boxed_2745_ = lean_unbox_usize(v_i_2741_);
lean_dec(v_i_2741_);
v_res_2746_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(v_as_2739_, v_sz_boxed_2744_, v_i_boxed_2745_, v_b_2742_);
lean_dec_ref(v_as_2739_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(lean_object* v_as_2747_, size_t v_sz_2748_, size_t v_i_2749_, lean_object* v_b_2750_){
_start:
{
uint8_t v___x_2752_; 
v___x_2752_ = lean_usize_dec_lt(v_i_2749_, v_sz_2748_);
if (v___x_2752_ == 0)
{
lean_object* v___x_2753_; 
v___x_2753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2753_, 0, v_b_2750_);
return v___x_2753_;
}
else
{
uint8_t v___x_2754_; lean_object* v_a_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; 
lean_dec_ref(v_b_2750_);
v___x_2754_ = 0;
v_a_2755_ = lean_array_uget_borrowed(v_as_2747_, v_i_2749_);
lean_inc(v_a_2755_);
v___x_2756_ = l_Lean_Message_toString(v_a_2755_, v___x_2754_);
v___x_2757_ = l_IO_eprintln___at___00main_spec__6(v___x_2756_);
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_object* v___x_2758_; size_t v___x_2759_; size_t v___x_2760_; lean_object* v___x_2761_; 
lean_dec_ref_known(v___x_2757_, 1);
v___x_2758_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_2759_ = ((size_t)1ULL);
v___x_2760_ = lean_usize_add(v_i_2749_, v___x_2759_);
v___x_2761_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(v_as_2747_, v_sz_2748_, v___x_2760_, v___x_2758_);
return v___x_2761_;
}
else
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
v_a_2762_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2764_ = v___x_2757_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2757_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2767_; 
if (v_isShared_2765_ == 0)
{
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_a_2762_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11___boxed(lean_object* v_as_2770_, lean_object* v_sz_2771_, lean_object* v_i_2772_, lean_object* v_b_2773_, lean_object* v___y_2774_){
_start:
{
size_t v_sz_boxed_2775_; size_t v_i_boxed_2776_; lean_object* v_res_2777_; 
v_sz_boxed_2775_ = lean_unbox_usize(v_sz_2771_);
lean_dec(v_sz_2771_);
v_i_boxed_2776_ = lean_unbox_usize(v_i_2772_);
lean_dec(v_i_2772_);
v_res_2777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_as_2770_, v_sz_boxed_2775_, v_i_boxed_2776_, v_b_2773_);
lean_dec_ref(v_as_2770_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7(lean_object* v_t_2778_, lean_object* v_init_2779_){
_start:
{
lean_object* v_root_2781_; lean_object* v_tail_2782_; lean_object* v___x_2783_; 
v_root_2781_ = lean_ctor_get(v_t_2778_, 0);
v_tail_2782_ = lean_ctor_get(v_t_2778_, 1);
v___x_2783_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2779_, v_root_2781_, v_init_2779_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2820_; 
v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2786_ = v___x_2783_;
v_isShared_2787_ = v_isSharedCheck_2820_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2783_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2820_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
if (lean_obj_tag(v_a_2784_) == 0)
{
lean_object* v_a_2788_; lean_object* v___x_2790_; 
v_a_2788_ = lean_ctor_get(v_a_2784_, 0);
lean_inc(v_a_2788_);
lean_dec_ref_known(v_a_2784_, 1);
if (v_isShared_2787_ == 0)
{
lean_ctor_set(v___x_2786_, 0, v_a_2788_);
v___x_2790_ = v___x_2786_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_a_2788_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
else
{
lean_object* v_a_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; size_t v_sz_2795_; size_t v___x_2796_; lean_object* v___x_2797_; 
lean_del_object(v___x_2786_);
v_a_2792_ = lean_ctor_get(v_a_2784_, 0);
lean_inc(v_a_2792_);
lean_dec_ref_known(v_a_2784_, 1);
v___x_2793_ = lean_box(0);
v___x_2794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2793_);
lean_ctor_set(v___x_2794_, 1, v_a_2792_);
v_sz_2795_ = lean_array_size(v_tail_2782_);
v___x_2796_ = ((size_t)0ULL);
v___x_2797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_tail_2782_, v_sz_2795_, v___x_2796_, v___x_2794_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2811_; 
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2800_ = v___x_2797_;
v_isShared_2801_ = v_isSharedCheck_2811_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_a_2798_);
lean_dec(v___x_2797_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2811_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v_fst_2802_; 
v_fst_2802_ = lean_ctor_get(v_a_2798_, 0);
if (lean_obj_tag(v_fst_2802_) == 0)
{
lean_object* v_snd_2803_; lean_object* v___x_2805_; 
v_snd_2803_ = lean_ctor_get(v_a_2798_, 1);
lean_inc(v_snd_2803_);
lean_dec(v_a_2798_);
if (v_isShared_2801_ == 0)
{
lean_ctor_set(v___x_2800_, 0, v_snd_2803_);
v___x_2805_ = v___x_2800_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_snd_2803_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
else
{
lean_object* v_val_2807_; lean_object* v___x_2809_; 
lean_inc_ref(v_fst_2802_);
lean_dec(v_a_2798_);
v_val_2807_ = lean_ctor_get(v_fst_2802_, 0);
lean_inc(v_val_2807_);
lean_dec_ref_known(v_fst_2802_, 1);
if (v_isShared_2801_ == 0)
{
lean_ctor_set(v___x_2800_, 0, v_val_2807_);
v___x_2809_ = v___x_2800_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_val_2807_);
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
else
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2819_; 
v_a_2812_ = lean_ctor_get(v___x_2797_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2814_ = v___x_2797_;
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2797_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2817_; 
if (v_isShared_2815_ == 0)
{
v___x_2817_ = v___x_2814_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_a_2812_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
}
}
}
else
{
lean_object* v_a_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2828_; 
v_a_2821_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2823_ = v___x_2783_;
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_a_2821_);
lean_dec(v___x_2783_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2826_; 
if (v_isShared_2824_ == 0)
{
v___x_2826_ = v___x_2823_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_a_2821_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
return v___x_2826_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7___boxed(lean_object* v_t_2829_, lean_object* v_init_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_t_2829_, v_init_2830_);
lean_dec_ref(v_t_2829_);
return v_res_2832_;
}
}
static lean_object* _init_l_main___closed__3(void){
_start:
{
lean_object* v___x_2836_; 
v___x_2836_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(lean_box(0), lean_box(0), lean_box(0));
return v___x_2836_;
}
}
static lean_object* _init_l_main___closed__4(void){
_start:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2837_ = l_Lean_instInhabitedClassState_default;
v___x_2838_ = lean_box(0);
v___x_2839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2838_);
lean_ctor_set(v___x_2839_, 1, v___x_2837_);
return v___x_2839_;
}
}
static lean_object* _init_l_main___closed__5(void){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___x_2840_ = l_Lean_Meta_Match_Extension_instInhabitedState;
v___x_2841_ = lean_box(0);
v___x_2842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2842_, 0, v___x_2841_);
lean_ctor_set(v___x_2842_, 1, v___x_2840_);
return v___x_2842_;
}
}
static lean_object* _init_l_main___closed__6(void){
_start:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
v___x_2843_ = ((lean_object*)(l_main___closed__2));
v___x_2844_ = ((lean_object*)(l_main___closed__1));
v___x_2845_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_2844_, v___x_2843_);
return v___x_2845_;
}
}
static lean_object* _init_l_main___closed__7(void){
_start:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; 
v___x_2846_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_2847_ = lean_box(0);
v___x_2848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2847_);
lean_ctor_set(v___x_2848_, 1, v___x_2846_);
return v___x_2848_;
}
}
static lean_object* _init_l_main___closed__8(void){
_start:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2849_ = lean_obj_once(&l_main___closed__7, &l_main___closed__7_once, _init_l_main___closed__7);
v___x_2850_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2849_);
return v___x_2850_;
}
}
static lean_object* _init_l_main___closed__9(void){
_start:
{
lean_object* v___x_2851_; 
v___x_2851_ = l_Array_instInhabited(lean_box(0));
return v___x_2851_;
}
}
static lean_object* _init_l_main___closed__15(void){
_start:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = l_Lean_Options_empty;
v___x_2861_ = l_Lean_Core_getMaxHeartbeats(v___x_2860_);
return v___x_2861_;
}
}
static lean_object* _init_l_main___closed__20(void){
_start:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; 
v___x_2866_ = ((lean_object*)(l_main___closed__19));
v___x_2867_ = lean_unsigned_to_nat(27u);
v___x_2868_ = lean_unsigned_to_nat(149u);
v___x_2869_ = ((lean_object*)(l_main___closed__18));
v___x_2870_ = ((lean_object*)(l_main___closed__17));
v___x_2871_ = l_mkPanicMessageWithDecl(v___x_2870_, v___x_2869_, v___x_2868_, v___x_2867_, v___x_2866_);
return v___x_2871_;
}
}
static lean_object* _init_l_main___closed__22(void){
_start:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2873_ = ((lean_object*)(l_main___closed__19));
v___x_2874_ = lean_unsigned_to_nat(51u);
v___x_2875_ = lean_unsigned_to_nat(122u);
v___x_2876_ = ((lean_object*)(l_main___closed__18));
v___x_2877_ = ((lean_object*)(l_main___closed__17));
v___x_2878_ = l_mkPanicMessageWithDecl(v___x_2877_, v___x_2876_, v___x_2875_, v___x_2874_, v___x_2873_);
return v___x_2878_;
}
}
static lean_object* _init_l_main___closed__23(void){
_start:
{
lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2879_ = lean_unsigned_to_nat(1u);
v___x_2880_ = l_Lean_firstFrontendMacroScope;
v___x_2881_ = lean_nat_add(v___x_2880_, v___x_2879_);
return v___x_2881_;
}
}
static lean_object* _init_l_main___closed__27(void){
_start:
{
lean_object* v___x_2888_; uint64_t v___x_2889_; lean_object* v___x_2890_; 
v___x_2888_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2889_ = 0ULL;
v___x_2890_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2890_, 0, v___x_2888_);
lean_ctor_set_uint64(v___x_2890_, sizeof(void*)*1, v___x_2889_);
return v___x_2890_;
}
}
static lean_object* _init_l_main___closed__28(void){
_start:
{
lean_object* v___x_2891_; 
v___x_2891_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2891_;
}
}
static lean_object* _init_l_main___closed__29(void){
_start:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2892_ = lean_obj_once(&l_main___closed__28, &l_main___closed__28_once, _init_l_main___closed__28);
v___x_2893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2892_);
return v___x_2893_;
}
}
static lean_object* _init_l_main___closed__30(void){
_start:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2894_ = lean_obj_once(&l_main___closed__29, &l_main___closed__29_once, _init_l_main___closed__29);
v___x_2895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2894_);
lean_ctor_set(v___x_2895_, 1, v___x_2894_);
return v___x_2895_;
}
}
static lean_object* _init_l_main___closed__31(void){
_start:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2896_ = l_Lean_NameSet_empty;
v___x_2897_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2898_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2897_);
lean_ctor_set(v___x_2898_, 1, v___x_2897_);
lean_ctor_set(v___x_2898_, 2, v___x_2896_);
return v___x_2898_;
}
}
static lean_object* _init_l_main___closed__32(void){
_start:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; uint8_t v___x_2901_; lean_object* v___x_2902_; 
v___x_2899_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2900_ = lean_obj_once(&l_main___closed__29, &l_main___closed__29_once, _init_l_main___closed__29);
v___x_2901_ = 1;
v___x_2902_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2902_, 0, v___x_2900_);
lean_ctor_set(v___x_2902_, 1, v___x_2900_);
lean_ctor_set(v___x_2902_, 2, v___x_2899_);
lean_ctor_set_uint8(v___x_2902_, sizeof(void*)*3, v___x_2901_);
return v___x_2902_;
}
}
static uint8_t _init_l_main___closed__37(void){
_start:
{
uint8_t v___x_2909_; uint8_t v___x_2910_; uint8_t v___x_2911_; 
v___x_2909_ = 2;
v___x_2910_ = 0;
v___x_2911_ = l_Lean_instOrdOLeanLevel_ord(v___x_2910_, v___x_2909_);
return v___x_2911_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_2912_; lean_object* v___x_2913_; 
v___x_2912_ = 1;
v___x_2913_ = lean_box_uint32(v___x_2912_);
return v___x_2913_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_2914_; lean_object* v___x_2915_; 
v___x_2914_ = 0;
v___x_2915_ = lean_box_uint32(v___x_2914_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_2916_){
_start:
{
if (lean_obj_tag(v_args_2916_) == 1)
{
lean_object* v_tail_2941_; 
v_tail_2941_ = lean_ctor_get(v_args_2916_, 1);
lean_inc(v_tail_2941_);
if (lean_obj_tag(v_tail_2941_) == 1)
{
lean_object* v_tail_2942_; 
v_tail_2942_ = lean_ctor_get(v_tail_2941_, 1);
lean_inc(v_tail_2942_);
if (lean_obj_tag(v_tail_2942_) == 1)
{
lean_object* v_head_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_3597_; 
v_head_2943_ = lean_ctor_get(v_args_2916_, 0);
v_isSharedCheck_3597_ = !lean_is_exclusive(v_args_2916_);
if (v_isSharedCheck_3597_ == 0)
{
lean_object* v_unused_3598_; 
v_unused_3598_ = lean_ctor_get(v_args_2916_, 1);
lean_dec(v_unused_3598_);
v___x_2945_ = v_args_2916_;
v_isShared_2946_ = v_isSharedCheck_3597_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_head_2943_);
lean_dec(v_args_2916_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_3597_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v_head_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_3595_; 
v_head_2947_ = lean_ctor_get(v_tail_2941_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v_tail_2941_);
if (v_isSharedCheck_3595_ == 0)
{
lean_object* v_unused_3596_; 
v_unused_3596_ = lean_ctor_get(v_tail_2941_, 1);
lean_dec(v_unused_3596_);
v___x_2949_ = v_tail_2941_;
v_isShared_2950_ = v_isSharedCheck_3595_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_head_2947_);
lean_dec(v_tail_2941_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_3595_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v_head_2951_; lean_object* v_tail_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_3594_; 
v_head_2951_ = lean_ctor_get(v_tail_2942_, 0);
v_tail_2952_ = lean_ctor_get(v_tail_2942_, 1);
v_isSharedCheck_3594_ = !lean_is_exclusive(v_tail_2942_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_2954_ = v_tail_2942_;
v_isShared_2955_ = v_isSharedCheck_3594_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_tail_2952_);
lean_inc(v_head_2951_);
lean_dec(v_tail_2942_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_3594_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2956_; 
v___x_2956_ = l_Lean_ModuleSetup_load(v_head_2943_);
lean_dec(v_head_2943_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; lean_object* v_name_2958_; lean_object* v_importArts_2959_; lean_object* v_options_2960_; uint8_t v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2965_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
lean_inc(v_a_2957_);
lean_dec_ref_known(v___x_2956_, 1);
v_name_2958_ = lean_ctor_get(v_a_2957_, 0);
lean_inc(v_name_2958_);
v_importArts_2959_ = lean_ctor_get(v_a_2957_, 3);
lean_inc(v_importArts_2959_);
v_options_2960_ = lean_ctor_get(v_a_2957_, 6);
lean_inc(v_options_2960_);
lean_dec(v_a_2957_);
v___x_2961_ = 0;
v___x_2962_ = l_Lean_LeanOptions_toOptions(v_options_2960_);
v___x_2963_ = lean_box(v___x_2961_);
if (v_isShared_2955_ == 0)
{
lean_ctor_set_tag(v___x_2954_, 0);
lean_ctor_set(v___x_2954_, 1, v___x_2962_);
lean_ctor_set(v___x_2954_, 0, v___x_2963_);
v___x_2965_ = v___x_2954_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v___x_2963_);
lean_ctor_set(v_reuseFailAlloc_3585_, 1, v___x_2962_);
v___x_2965_ = v_reuseFailAlloc_3585_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
lean_object* v___x_2966_; 
v___x_2966_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_tail_2952_, v___x_2965_);
lean_dec(v_tail_2952_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v_a_2967_; lean_object* v___x_2968_; 
v_a_2967_ = lean_ctor_get(v___x_2966_, 0);
lean_inc(v_a_2967_);
lean_dec_ref_known(v___x_2966_, 1);
v___x_2968_ = lean_init_search_path();
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v_fst_2969_; lean_object* v_snd_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_3568_; 
lean_dec_ref_known(v___x_2968_, 1);
v_fst_2969_ = lean_ctor_get(v_a_2967_, 0);
v_snd_2970_ = lean_ctor_get(v_a_2967_, 1);
v_isSharedCheck_3568_ = !lean_is_exclusive(v_a_2967_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_2972_ = v_a_2967_;
v_isShared_2973_ = v_isSharedCheck_3568_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_snd_2970_);
lean_inc(v_fst_2969_);
lean_dec(v_a_2967_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_3568_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; uint8_t v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; uint8_t v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; uint8_t v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v_nextMacroScope_3163_; lean_object* v_ngen_3164_; lean_object* v_auxDeclNGen_3165_; lean_object* v_traceState_3166_; lean_object* v_messages_3167_; lean_object* v_infoState_3168_; lean_object* v_snapshotTasks_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; uint8_t v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; uint8_t v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; uint8_t v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; uint8_t v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; uint8_t v___y_3288_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; uint8_t v___x_3313_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; uint8_t v___x_3471_; uint8_t v___y_3473_; uint8_t v___x_3567_; 
v___x_2974_ = lean_obj_once(&l_main___closed__3, &l_main___closed__3_once, _init_l_main___closed__3);
v___x_2975_ = lean_box(0);
v___x_2976_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_2977_ = lean_obj_once(&l_main___closed__5, &l_main___closed__5_once, _init_l_main___closed__5);
v___x_2978_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_2979_ = lean_obj_once(&l_main___closed__8, &l_main___closed__8_once, _init_l_main___closed__8);
v___x_2980_ = lean_obj_once(&l_main___closed__9, &l_main___closed__9_once, _init_l_main___closed__9);
v___x_2981_ = lean_box(1);
v___x_2982_ = ((lean_object*)(l_main___closed__10));
v___x_2983_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_2984_ = 1;
v___x_2985_ = l_Lean_Option_set___at___00Lean_Environment_realizeConst_spec__0(v_snd_2970_, v___x_2983_, v___x_2984_);
v___x_2986_ = l_Lean_maxHeartbeats;
v___x_2987_ = lean_unsigned_to_nat(0u);
v___x_2988_ = l_Lean_Option_set___at___00main_spec__3(v___x_2985_, v___x_2986_, v___x_2987_);
v___x_3308_ = ((lean_object*)(l_main___closed__21));
lean_inc(v_name_2958_);
v___x_3309_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_3309_, 0, v_name_2958_);
lean_ctor_set_uint8(v___x_3309_, sizeof(void*)*1, v___x_2984_);
lean_ctor_set_uint8(v___x_3309_, sizeof(void*)*1 + 1, v___x_2984_);
lean_ctor_set_uint8(v___x_3309_, sizeof(void*)*1 + 2, v___x_2961_);
v___x_3310_ = lean_unsigned_to_nat(1u);
v___x_3311_ = lean_mk_empty_array_with_capacity(v___x_3310_);
v___x_3312_ = lean_array_push(v___x_3311_, v___x_3309_);
v___x_3313_ = 0;
v___x_3471_ = 2;
v___x_3567_ = lean_uint8_once(&l_main___closed__37, &l_main___closed__37_once, _init_l_main___closed__37);
if (v___x_3567_ == 0)
{
v___y_3473_ = v___x_2984_;
goto v___jp_3472_;
}
else
{
v___y_3473_ = v___x_2961_;
goto v___jp_3472_;
}
v___jp_2989_:
{
lean_object* v___x_3009_; lean_object* v_messages_3010_; lean_object* v_env_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3134_; 
v___x_3009_ = lean_st_ref_get(v___y_3000_);
lean_dec(v___y_3000_);
v_messages_3010_ = lean_ctor_get(v___x_3009_, 6);
v_env_3011_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3134_ == 0)
{
lean_object* v_unused_3135_; lean_object* v_unused_3136_; lean_object* v_unused_3137_; lean_object* v_unused_3138_; lean_object* v_unused_3139_; lean_object* v_unused_3140_; lean_object* v_unused_3141_; 
v_unused_3135_ = lean_ctor_get(v___x_3009_, 8);
lean_dec(v_unused_3135_);
v_unused_3136_ = lean_ctor_get(v___x_3009_, 7);
lean_dec(v_unused_3136_);
v_unused_3137_ = lean_ctor_get(v___x_3009_, 5);
lean_dec(v_unused_3137_);
v_unused_3138_ = lean_ctor_get(v___x_3009_, 4);
lean_dec(v_unused_3138_);
v_unused_3139_ = lean_ctor_get(v___x_3009_, 3);
lean_dec(v_unused_3139_);
v_unused_3140_ = lean_ctor_get(v___x_3009_, 2);
lean_dec(v_unused_3140_);
v_unused_3141_ = lean_ctor_get(v___x_3009_, 1);
lean_dec(v_unused_3141_);
v___x_3013_ = v___x_3009_;
v_isShared_3014_ = v_isSharedCheck_3134_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_messages_3010_);
lean_inc(v_env_3011_);
lean_dec(v___x_3009_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3134_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v_unreported_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v_unreported_3015_ = lean_ctor_get(v_messages_3010_, 1);
v___x_3016_ = lean_box(0);
v___x_3017_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_unreported_3015_, v___x_3016_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3124_; 
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3124_ == 0)
{
lean_object* v_unused_3125_; 
v_unused_3125_ = lean_ctor_get(v___x_3017_, 0);
lean_dec(v_unused_3125_);
v___x_3019_ = v___x_3017_;
v_isShared_3020_ = v_isSharedCheck_3124_;
goto v_resetjp_3018_;
}
else
{
lean_dec(v___x_3017_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3124_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
uint8_t v___x_3021_; 
v___x_3021_ = l_Lean_MessageLog_hasErrors(v_messages_3010_);
lean_dec_ref(v_messages_3010_);
if (v___x_3021_ == 0)
{
lean_object* v___x_3022_; 
lean_del_object(v___x_3019_);
lean_inc_ref(v_env_3011_);
v___x_3022_ = l___private_LeanIR_0__mkIRSigData(v_env_3011_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_object* v_a_3023_; lean_object* v___x_3024_; 
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc(v_a_3023_);
lean_dec_ref_known(v___x_3022_, 1);
lean_inc_ref(v_env_3011_);
v___x_3024_ = l___private_LeanIR_0__mkIRData(v_env_3011_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3032_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_a_3025_);
lean_dec_ref_known(v___x_3024_, 1);
v___x_3026_ = ((lean_object*)(l_main___closed__11));
lean_inc(v_head_2947_);
v___x_3027_ = l_System_FilePath_addExtension(v_head_2947_, v___x_3026_);
v___x_3028_ = l_Lean_Environment_mainModule(v_env_3011_);
v___x_3029_ = ((lean_object*)(l_main___closed__13));
v___x_3030_ = l_Lean_Name_append(v___x_3028_, v___x_3029_);
if (v_isShared_2973_ == 0)
{
lean_ctor_set(v___x_2972_, 1, v_a_3023_);
lean_ctor_set(v___x_2972_, 0, v___x_3027_);
v___x_3032_ = v___x_2972_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v___x_3027_);
lean_ctor_set(v_reuseFailAlloc_3103_, 1, v_a_3023_);
v___x_3032_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
lean_object* v___x_3034_; 
lean_inc(v_head_2947_);
if (v_isShared_2950_ == 0)
{
lean_ctor_set_tag(v___x_2949_, 0);
lean_ctor_set(v___x_2949_, 1, v_a_3025_);
v___x_3034_ = v___x_2949_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_head_2947_);
lean_ctor_set(v_reuseFailAlloc_3102_, 1, v_a_3025_);
v___x_3034_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3035_ = lean_unsigned_to_nat(2u);
v___x_3036_ = lean_mk_empty_array_with_capacity(v___x_3035_);
v___x_3037_ = lean_array_push(v___x_3036_, v___x_3032_);
v___x_3038_ = lean_array_push(v___x_3037_, v___x_3034_);
v___x_3039_ = l_Lean_saveModuleDataParts(v___x_3030_, v___x_3038_);
lean_dec_ref(v___x_3038_);
lean_dec(v___x_3030_);
if (lean_obj_tag(v___x_3039_) == 0)
{
uint8_t v___x_3040_; lean_object* v___x_3041_; 
lean_dec_ref_known(v___x_3039_, 1);
v___x_3040_ = 1;
v___x_3041_ = lean_io_prim_handle_mk(v_head_2951_, v___x_3040_);
if (lean_obj_tag(v___x_3041_) == 0)
{
lean_object* v_a_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3047_; 
lean_dec(v_head_2951_);
v_a_3042_ = lean_ctor_get(v___x_3041_, 0);
lean_inc(v_a_3042_);
lean_dec_ref_known(v___x_3041_, 1);
v___x_3043_ = ((lean_object*)(l_main___closed__14));
v___x_3044_ = l_Lean_Options_empty;
v___x_3045_ = lean_obj_once(&l_main___closed__15, &l_main___closed__15_once, _init_l_main___closed__15);
lean_inc_ref(v___y_3005_);
lean_inc_ref(v___y_2999_);
lean_inc_ref(v___y_3003_);
lean_inc_ref(v___y_3007_);
lean_inc_ref(v___y_3006_);
lean_inc_ref(v___y_3008_);
lean_inc(v___y_3004_);
lean_inc_ref(v_env_3011_);
if (v_isShared_3014_ == 0)
{
lean_ctor_set(v___x_3013_, 8, v___y_3005_);
lean_ctor_set(v___x_3013_, 7, v___y_2999_);
lean_ctor_set(v___x_3013_, 6, v___y_3003_);
lean_ctor_set(v___x_3013_, 5, v___y_3007_);
lean_ctor_set(v___x_3013_, 4, v___y_3006_);
lean_ctor_set(v___x_3013_, 3, v___y_3002_);
lean_ctor_set(v___x_3013_, 2, v___y_3008_);
lean_ctor_set(v___x_3013_, 1, v___y_3004_);
v___x_3047_ = v___x_3013_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v_env_3011_);
lean_ctor_set(v_reuseFailAlloc_3071_, 1, v___y_3004_);
lean_ctor_set(v_reuseFailAlloc_3071_, 2, v___y_3008_);
lean_ctor_set(v_reuseFailAlloc_3071_, 3, v___y_3002_);
lean_ctor_set(v_reuseFailAlloc_3071_, 4, v___y_3006_);
lean_ctor_set(v_reuseFailAlloc_3071_, 5, v___y_3007_);
lean_ctor_set(v_reuseFailAlloc_3071_, 6, v___y_3003_);
lean_ctor_set(v_reuseFailAlloc_3071_, 7, v___y_2999_);
lean_ctor_set(v_reuseFailAlloc_3071_, 8, v___y_3005_);
v___x_3047_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___f_3050_; lean_object* v___x_3051_; 
v___x_3048_ = lean_box(v___y_2996_);
v___x_3049_ = lean_box(v___x_2961_);
lean_inc(v___y_2997_);
lean_inc(v___y_2994_);
lean_inc(v___y_2991_);
lean_inc(v___y_2990_);
lean_inc_ref(v___y_2995_);
lean_inc_ref(v___y_2998_);
lean_inc(v___y_2993_);
v___f_3050_ = lean_alloc_closure((void*)(l_main___lam__1___boxed), 18, 17);
lean_closure_set(v___f_3050_, 0, v___x_3047_);
lean_closure_set(v___f_3050_, 1, v___y_2993_);
lean_closure_set(v___f_3050_, 2, v___x_3044_);
lean_closure_set(v___f_3050_, 3, v_name_2958_);
lean_closure_set(v___f_3050_, 4, v_a_3042_);
lean_closure_set(v___f_3050_, 5, v___x_3048_);
lean_closure_set(v___f_3050_, 6, v___y_2998_);
lean_closure_set(v___f_3050_, 7, v_head_2947_);
lean_closure_set(v___f_3050_, 8, v___y_2995_);
lean_closure_set(v___f_3050_, 9, v___y_2992_);
lean_closure_set(v___f_3050_, 10, v___y_2990_);
lean_closure_set(v___f_3050_, 11, v___x_3045_);
lean_closure_set(v___f_3050_, 12, v___y_2991_);
lean_closure_set(v___f_3050_, 13, v___y_2994_);
lean_closure_set(v___f_3050_, 14, v___x_2987_);
lean_closure_set(v___f_3050_, 15, v___y_2997_);
lean_closure_set(v___f_3050_, 16, v___x_3049_);
v___x_3051_ = l_Lean_profileitIOUnsafe___redArg(v___x_3043_, v___x_2988_, v___f_3050_, v___y_3001_);
lean_dec_ref(v___x_2988_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_object* v___x_3052_; uint8_t v___x_3053_; 
lean_dec_ref_known(v___x_3051_, 1);
v___x_3052_ = lean_display_cumulative_profiling_times();
v___x_3053_ = lean_unbox(v_fst_2969_);
lean_dec(v_fst_2969_);
if (v___x_3053_ == 0)
{
lean_dec_ref(v_env_3011_);
goto v___jp_2938_;
}
else
{
lean_object* v___x_3054_; 
v___x_3054_ = l_Lean_Environment_displayStats(v_env_3011_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_dec_ref_known(v___x_3054_, 1);
goto v___jp_2938_;
}
else
{
lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
v_a_3055_ = lean_ctor_get(v___x_3054_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3057_ = v___x_3054_;
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___x_3054_);
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
lean_object* v_a_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3070_; 
lean_dec_ref(v_env_3011_);
lean_dec(v_fst_2969_);
v_a_3063_ = lean_ctor_get(v___x_3051_, 0);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3065_ = v___x_3051_;
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_a_3063_);
lean_dec(v___x_3051_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3068_; 
if (v_isShared_3066_ == 0)
{
v___x_3068_ = v___x_3065_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_a_3063_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
}
}
else
{
lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
lean_dec_ref_known(v___x_3041_, 1);
lean_del_object(v___x_3013_);
lean_dec_ref(v_env_3011_);
lean_dec_ref(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec(v___y_2992_);
lean_dec_ref(v___x_2988_);
lean_dec(v_fst_2969_);
lean_dec(v_name_2958_);
lean_dec(v_head_2947_);
v___x_3072_ = ((lean_object*)(l_main___closed__16));
v___x_3073_ = lean_string_append(v___x_3072_, v_head_2951_);
lean_dec(v_head_2951_);
v___x_3074_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__1));
v___x_3075_ = lean_string_append(v___x_3073_, v___x_3074_);
v___x_3076_ = l_IO_eprintln___at___00main_spec__6(v___x_3075_);
if (lean_obj_tag(v___x_3076_) == 0)
{
lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3084_; 
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3076_);
if (v_isSharedCheck_3084_ == 0)
{
lean_object* v_unused_3085_; 
v_unused_3085_ = lean_ctor_get(v___x_3076_, 0);
lean_dec(v_unused_3085_);
v___x_3078_ = v___x_3076_;
v_isShared_3079_ = v_isSharedCheck_3084_;
goto v_resetjp_3077_;
}
else
{
lean_dec(v___x_3076_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3084_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3080_; lean_object* v___x_3082_; 
v___x_3080_ = l_main___boxed__const__1;
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 0, v___x_3080_);
v___x_3082_ = v___x_3078_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v___x_3080_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
else
{
lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3093_; 
v_a_3086_ = lean_ctor_get(v___x_3076_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3076_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3088_ = v___x_3076_;
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v___x_3076_);
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
else
{
lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3101_; 
lean_del_object(v___x_3013_);
lean_dec_ref(v_env_3011_);
lean_dec_ref(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec(v___y_2992_);
lean_dec_ref(v___x_2988_);
lean_dec(v_fst_2969_);
lean_dec(v_name_2958_);
lean_dec(v_head_2951_);
lean_dec(v_head_2947_);
v_a_3094_ = lean_ctor_get(v___x_3039_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3039_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3096_ = v___x_3039_;
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_3039_);
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
else
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
lean_dec(v_a_3023_);
lean_del_object(v___x_3013_);
lean_dec_ref(v_env_3011_);
lean_dec_ref(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec(v___y_2992_);
lean_dec_ref(v___x_2988_);
lean_del_object(v___x_2972_);
lean_dec(v_fst_2969_);
lean_dec(v_name_2958_);
lean_dec(v_head_2951_);
lean_del_object(v___x_2949_);
lean_dec(v_head_2947_);
v_a_3104_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_3024_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3024_);
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
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3119_; 
lean_del_object(v___x_3013_);
lean_dec_ref(v_env_3011_);
lean_dec_ref(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec(v___y_2992_);
lean_dec_ref(v___x_2988_);
lean_del_object(v___x_2972_);
lean_dec(v_fst_2969_);
lean_dec(v_name_2958_);
lean_dec(v_head_2951_);
lean_del_object(v___x_2949_);
lean_dec(v_head_2947_);
v_a_3112_ = lean_ctor_get(v___x_3022_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3114_ = v___x_3022_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3022_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3117_; 
if (v_isShared_3115_ == 0)
{
v___x_3117_ = v___x_3114_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3112_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
}
else
{
lean_object* v___x_3120_; lean_object* v___x_3122_; 
lean_del_object(v___x_3013_);
lean_dec_ref(v_env_3011_);
lean_dec_ref(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec(v___y_2992_);
lean_dec_ref(v___x_2988_);
lean_del_object(v___x_2972_);
lean_dec(v_fst_2969_);
lean_dec(v_name_2958_);
lean_dec(v_head_2951_);
lean_del_object(v___x_2949_);
lean_dec(v_head_2947_);
v___x_3120_ = l_main___boxed__const__1;
if (v_isShared_3020_ == 0)
{
lean_ctor_set(v___x_3019_, 0, v___x_3120_);
v___x_3122_ = v___x_3019_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v___x_3120_);
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
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3133_; 
lean_del_object(v___x_3013_);
lean_dec_ref(v_env_3011_);
lean_dec_ref(v_messages_3010_);
lean_dec_ref(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec(v___y_2992_);
lean_dec_ref(v___x_2988_);
lean_del_object(v___x_2972_);
lean_dec(v_fst_2969_);
lean_dec(v_name_2958_);
lean_dec(v_head_2951_);
lean_del_object(v___x_2949_);
lean_dec(v_head_2947_);
v_a_3126_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3128_ = v___x_3017_;
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_3017_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3131_; 
if (v_isShared_3129_ == 0)
{
v___x_3131_ = v___x_3128_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_a_3126_);
v___x_3131_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
return v___x_3131_;
}
}
}
}
}
v___jp_3142_:
{
lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; size_t v_sz_3176_; size_t v___x_3177_; lean_object* v___x_3178_; 
lean_inc_ref(v___y_3170_);
v___x_3173_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3173_, 0, v___y_3172_);
lean_ctor_set(v___x_3173_, 1, v_nextMacroScope_3163_);
lean_ctor_set(v___x_3173_, 2, v_ngen_3164_);
lean_ctor_set(v___x_3173_, 3, v_auxDeclNGen_3165_);
lean_ctor_set(v___x_3173_, 4, v_traceState_3166_);
lean_ctor_set(v___x_3173_, 5, v___y_3170_);
lean_ctor_set(v___x_3173_, 6, v_messages_3167_);
lean_ctor_set(v___x_3173_, 7, v_infoState_3168_);
lean_ctor_set(v___x_3173_, 8, v_snapshotTasks_3169_);
v___x_3174_ = lean_st_ref_put(v___y_3154_, v___x_3173_);
v___x_3175_ = lean_box(0);
v_sz_3176_ = lean_array_size(v___y_3171_);
v___x_3177_ = ((size_t)0ULL);
v___x_3178_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(v___y_3171_, v_sz_3176_, v___x_3177_, v___x_3175_, v___y_3153_, v___y_3154_);
lean_dec_ref(v___y_3171_);
if (lean_obj_tag(v___x_3178_) == 0)
{
lean_dec_ref_known(v___x_3178_, 1);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
v___y_2990_ = v___y_3143_;
v___y_2991_ = v___y_3144_;
v___y_2992_ = v___y_3146_;
v___y_2993_ = v___y_3145_;
v___y_2994_ = v___y_3147_;
v___y_2995_ = v___y_3149_;
v___y_2996_ = v___y_3148_;
v___y_2997_ = v___y_3150_;
v___y_2998_ = v___y_3151_;
v___y_2999_ = v___y_3152_;
v___y_3000_ = v___y_3159_;
v___y_3001_ = v___y_3160_;
v___y_3002_ = v___y_3155_;
v___y_3003_ = v___y_3161_;
v___y_3004_ = v___y_3156_;
v___y_3005_ = v___y_3162_;
v___y_3006_ = v___y_3157_;
v___y_3007_ = v___y_3170_;
v___y_3008_ = v___y_3158_;
goto v___jp_2989_;
}
else
{
if (lean_obj_tag(v___x_3178_) == 0)
{
lean_dec_ref_known(v___x_3178_, 1);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
v___y_2990_ = v___y_3143_;
v___y_2991_ = v___y_3144_;
v___y_2992_ = v___y_3146_;
v___y_2993_ = v___y_3145_;
v___y_2994_ = v___y_3147_;
v___y_2995_ = v___y_3149_;
v___y_2996_ = v___y_3148_;
v___y_2997_ = v___y_3150_;
v___y_2998_ = v___y_3151_;
v___y_2999_ = v___y_3152_;
v___y_3000_ = v___y_3159_;
v___y_3001_ = v___y_3160_;
v___y_3002_ = v___y_3155_;
v___y_3003_ = v___y_3161_;
v___y_3004_ = v___y_3156_;
v___y_3005_ = v___y_3162_;
v___y_3006_ = v___y_3157_;
v___y_3007_ = v___y_3170_;
v___y_3008_ = v___y_3158_;
goto v___jp_2989_;
}
else
{
lean_object* v_a_3179_; uint8_t v___x_3180_; 
v_a_3179_ = lean_ctor_get(v___x_3178_, 0);
lean_inc(v_a_3179_);
lean_dec_ref_known(v___x_3178_, 1);
v___x_3180_ = l_Lean_Exception_isInterrupt(v_a_3179_);
if (v___x_3180_ == 0)
{
lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3181_ = l_Lean_Exception_toMessageData(v_a_3179_);
v___x_3182_ = l_Lean_logError___at___00main_spec__14(v___x_3181_, v___y_3153_, v___y_3154_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
if (lean_obj_tag(v___x_3182_) == 0)
{
lean_dec_ref_known(v___x_3182_, 1);
v___y_2990_ = v___y_3143_;
v___y_2991_ = v___y_3144_;
v___y_2992_ = v___y_3146_;
v___y_2993_ = v___y_3145_;
v___y_2994_ = v___y_3147_;
v___y_2995_ = v___y_3149_;
v___y_2996_ = v___y_3148_;
v___y_2997_ = v___y_3150_;
v___y_2998_ = v___y_3151_;
v___y_2999_ = v___y_3152_;
v___y_3000_ = v___y_3159_;
v___y_3001_ = v___y_3160_;
v___y_3002_ = v___y_3155_;
v___y_3003_ = v___y_3161_;
v___y_3004_ = v___y_3156_;
v___y_3005_ = v___y_3162_;
v___y_3006_ = v___y_3157_;
v___y_3007_ = v___y_3170_;
v___y_3008_ = v___y_3158_;
goto v___jp_2989_;
}
else
{
lean_object* v___x_3183_; lean_object* v___x_3184_; 
lean_dec_ref_known(v___x_3182_, 1);
lean_dec(v___y_3160_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3146_);
lean_dec_ref(v___x_2988_);
lean_del_object(v___x_2972_);
lean_dec(v_fst_2969_);
lean_dec(v_name_2958_);
lean_dec(v_head_2951_);
lean_del_object(v___x_2949_);
lean_dec(v_head_2947_);
v___x_3183_ = lean_obj_once(&l_main___closed__20, &l_main___closed__20_once, _init_l_main___closed__20);
v___x_3184_ = l_panic___at___00main_spec__5(v___x_3183_);
return v___x_3184_;
}
}
else
{
lean_dec(v_a_3179_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
v___y_2990_ = v___y_3143_;
v___y_2991_ = v___y_3144_;
v___y_2992_ = v___y_3146_;
v___y_2993_ = v___y_3145_;
v___y_2994_ = v___y_3147_;
v___y_2995_ = v___y_3149_;
v___y_2996_ = v___y_3148_;
v___y_2997_ = v___y_3150_;
v___y_2998_ = v___y_3151_;
v___y_2999_ = v___y_3152_;
v___y_3000_ = v___y_3159_;
v___y_3001_ = v___y_3160_;
v___y_3002_ = v___y_3155_;
v___y_3003_ = v___y_3161_;
v___y_3004_ = v___y_3156_;
v___y_3005_ = v___y_3162_;
v___y_3006_ = v___y_3157_;
v___y_3007_ = v___y_3170_;
v___y_3008_ = v___y_3158_;
goto v___jp_2989_;
}
}
}
}
v___jp_3185_:
{
lean_object* v___x_3210_; lean_object* v_toCold_3211_; lean_object* v_currRecDepth_3212_; lean_object* v_ref_3213_; uint8_t v_suppressElabErrors_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3263_; 
v___x_3210_ = lean_st_ref_take(v___y_3209_);
v_toCold_3211_ = lean_ctor_get(v___y_3208_, 0);
v_currRecDepth_3212_ = lean_ctor_get(v___y_3208_, 1);
v_ref_3213_ = lean_ctor_get(v___y_3208_, 2);
v_suppressElabErrors_3214_ = lean_ctor_get_uint8(v___y_3208_, sizeof(void*)*3 + 1);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___y_3208_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3216_ = v___y_3208_;
v_isShared_3217_ = v_isSharedCheck_3263_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_ref_3213_);
lean_inc(v_currRecDepth_3212_);
lean_inc(v_toCold_3211_);
lean_dec(v___y_3208_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3263_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v_fileName_3218_; lean_object* v_fileMap_3219_; lean_object* v_currNamespace_3220_; lean_object* v_openDecls_3221_; lean_object* v_initHeartbeats_3222_; lean_object* v_maxHeartbeats_3223_; lean_object* v_quotContext_3224_; lean_object* v_currMacroScope_3225_; lean_object* v_cancelTk_x3f_3226_; lean_object* v_inheritedTraceOptions_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3260_; 
v_fileName_3218_ = lean_ctor_get(v_toCold_3211_, 0);
v_fileMap_3219_ = lean_ctor_get(v_toCold_3211_, 1);
v_currNamespace_3220_ = lean_ctor_get(v_toCold_3211_, 4);
v_openDecls_3221_ = lean_ctor_get(v_toCold_3211_, 5);
v_initHeartbeats_3222_ = lean_ctor_get(v_toCold_3211_, 6);
v_maxHeartbeats_3223_ = lean_ctor_get(v_toCold_3211_, 7);
v_quotContext_3224_ = lean_ctor_get(v_toCold_3211_, 8);
v_currMacroScope_3225_ = lean_ctor_get(v_toCold_3211_, 9);
v_cancelTk_x3f_3226_ = lean_ctor_get(v_toCold_3211_, 10);
v_inheritedTraceOptions_3227_ = lean_ctor_get(v_toCold_3211_, 11);
v_isSharedCheck_3260_ = !lean_is_exclusive(v_toCold_3211_);
if (v_isSharedCheck_3260_ == 0)
{
lean_object* v_unused_3261_; lean_object* v_unused_3262_; 
v_unused_3261_ = lean_ctor_get(v_toCold_3211_, 3);
lean_dec(v_unused_3261_);
v_unused_3262_ = lean_ctor_get(v_toCold_3211_, 2);
lean_dec(v_unused_3262_);
v___x_3229_ = v_toCold_3211_;
v_isShared_3230_ = v_isSharedCheck_3260_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_inheritedTraceOptions_3227_);
lean_inc(v_cancelTk_x3f_3226_);
lean_inc(v_currMacroScope_3225_);
lean_inc(v_quotContext_3224_);
lean_inc(v_maxHeartbeats_3223_);
lean_inc(v_initHeartbeats_3222_);
lean_inc(v_openDecls_3221_);
lean_inc(v_currNamespace_3220_);
lean_inc(v_fileMap_3219_);
lean_inc(v_fileName_3218_);
lean_dec(v_toCold_3211_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3260_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v_env_3231_; lean_object* v_nextMacroScope_3232_; lean_object* v_ngen_3233_; lean_object* v_auxDeclNGen_3234_; lean_object* v_traceState_3235_; lean_object* v_messages_3236_; lean_object* v_infoState_3237_; lean_object* v_snapshotTasks_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3242_; 
v_env_3231_ = lean_ctor_get(v___x_3210_, 0);
lean_inc_ref(v_env_3231_);
v_nextMacroScope_3232_ = lean_ctor_get(v___x_3210_, 1);
lean_inc(v_nextMacroScope_3232_);
v_ngen_3233_ = lean_ctor_get(v___x_3210_, 2);
lean_inc_ref(v_ngen_3233_);
v_auxDeclNGen_3234_ = lean_ctor_get(v___x_3210_, 3);
lean_inc_ref(v_auxDeclNGen_3234_);
v_traceState_3235_ = lean_ctor_get(v___x_3210_, 4);
lean_inc_ref(v_traceState_3235_);
v_messages_3236_ = lean_ctor_get(v___x_3210_, 6);
lean_inc_ref(v_messages_3236_);
v_infoState_3237_ = lean_ctor_get(v___x_3210_, 7);
lean_inc_ref(v_infoState_3237_);
v_snapshotTasks_3238_ = lean_ctor_get(v___x_3210_, 8);
lean_inc_ref(v_snapshotTasks_3238_);
lean_dec(v___x_3210_);
v___x_3239_ = l_Lean_maxRecDepth;
v___x_3240_ = l_Lean_Option_get___at___00main_spec__9(v___x_2988_, v___x_3239_);
lean_inc_ref(v___x_2988_);
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 3, v___x_3240_);
lean_ctor_set(v___x_3229_, 2, v___x_2988_);
v___x_3242_ = v___x_3229_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_fileName_3218_);
lean_ctor_set(v_reuseFailAlloc_3259_, 1, v_fileMap_3219_);
lean_ctor_set(v_reuseFailAlloc_3259_, 2, v___x_2988_);
lean_ctor_set(v_reuseFailAlloc_3259_, 3, v___x_3240_);
lean_ctor_set(v_reuseFailAlloc_3259_, 4, v_currNamespace_3220_);
lean_ctor_set(v_reuseFailAlloc_3259_, 5, v_openDecls_3221_);
lean_ctor_set(v_reuseFailAlloc_3259_, 6, v_initHeartbeats_3222_);
lean_ctor_set(v_reuseFailAlloc_3259_, 7, v_maxHeartbeats_3223_);
lean_ctor_set(v_reuseFailAlloc_3259_, 8, v_quotContext_3224_);
lean_ctor_set(v_reuseFailAlloc_3259_, 9, v_currMacroScope_3225_);
lean_ctor_set(v_reuseFailAlloc_3259_, 10, v_cancelTk_x3f_3226_);
lean_ctor_set(v_reuseFailAlloc_3259_, 11, v_inheritedTraceOptions_3227_);
v___x_3242_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
lean_object* v___x_3244_; 
if (v_isShared_3217_ == 0)
{
lean_ctor_set(v___x_3216_, 0, v___x_3242_);
v___x_3244_ = v___x_3216_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3242_);
lean_ctor_set(v_reuseFailAlloc_3258_, 1, v_currRecDepth_3212_);
lean_ctor_set(v_reuseFailAlloc_3258_, 2, v_ref_3213_);
lean_ctor_set_uint8(v_reuseFailAlloc_3258_, sizeof(void*)*3 + 1, v_suppressElabErrors_3214_);
v___x_3244_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
lean_object* v___x_3245_; uint8_t v___x_3246_; 
lean_ctor_set_uint8(v___x_3244_, sizeof(void*)*3, v___y_3200_);
v___x_3245_ = lean_array_get_size(v___y_3207_);
v___x_3246_ = lean_nat_dec_lt(v___x_2987_, v___x_3245_);
if (v___x_3246_ == 0)
{
lean_object* v___x_3247_; 
lean_inc_ref(v___y_3197_);
v___x_3247_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3197_, v_env_3231_, v___x_2981_);
v___y_3143_ = v___y_3186_;
v___y_3144_ = v___y_3187_;
v___y_3145_ = v___y_3189_;
v___y_3146_ = v___y_3188_;
v___y_3147_ = v___y_3190_;
v___y_3148_ = v___y_3192_;
v___y_3149_ = v___y_3191_;
v___y_3150_ = v___y_3193_;
v___y_3151_ = v___y_3194_;
v___y_3152_ = v___y_3195_;
v___y_3153_ = v___x_3244_;
v___y_3154_ = v___y_3209_;
v___y_3155_ = v___y_3196_;
v___y_3156_ = v___y_3198_;
v___y_3157_ = v___y_3199_;
v___y_3158_ = v___y_3201_;
v___y_3159_ = v___y_3202_;
v___y_3160_ = v___y_3203_;
v___y_3161_ = v___y_3204_;
v___y_3162_ = v___y_3205_;
v_nextMacroScope_3163_ = v_nextMacroScope_3232_;
v_ngen_3164_ = v_ngen_3233_;
v_auxDeclNGen_3165_ = v_auxDeclNGen_3234_;
v_traceState_3166_ = v_traceState_3235_;
v_messages_3167_ = v_messages_3236_;
v_infoState_3168_ = v_infoState_3237_;
v_snapshotTasks_3169_ = v_snapshotTasks_3238_;
v___y_3170_ = v___y_3206_;
v___y_3171_ = v___y_3207_;
v___y_3172_ = v___x_3247_;
goto v___jp_3142_;
}
else
{
uint8_t v___x_3248_; 
v___x_3248_ = lean_nat_dec_le(v___x_3245_, v___x_3245_);
if (v___x_3248_ == 0)
{
if (v___x_3246_ == 0)
{
lean_object* v___x_3249_; 
lean_inc_ref(v___y_3197_);
v___x_3249_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3197_, v_env_3231_, v___x_2981_);
v___y_3143_ = v___y_3186_;
v___y_3144_ = v___y_3187_;
v___y_3145_ = v___y_3189_;
v___y_3146_ = v___y_3188_;
v___y_3147_ = v___y_3190_;
v___y_3148_ = v___y_3192_;
v___y_3149_ = v___y_3191_;
v___y_3150_ = v___y_3193_;
v___y_3151_ = v___y_3194_;
v___y_3152_ = v___y_3195_;
v___y_3153_ = v___x_3244_;
v___y_3154_ = v___y_3209_;
v___y_3155_ = v___y_3196_;
v___y_3156_ = v___y_3198_;
v___y_3157_ = v___y_3199_;
v___y_3158_ = v___y_3201_;
v___y_3159_ = v___y_3202_;
v___y_3160_ = v___y_3203_;
v___y_3161_ = v___y_3204_;
v___y_3162_ = v___y_3205_;
v_nextMacroScope_3163_ = v_nextMacroScope_3232_;
v_ngen_3164_ = v_ngen_3233_;
v_auxDeclNGen_3165_ = v_auxDeclNGen_3234_;
v_traceState_3166_ = v_traceState_3235_;
v_messages_3167_ = v_messages_3236_;
v_infoState_3168_ = v_infoState_3237_;
v_snapshotTasks_3169_ = v_snapshotTasks_3238_;
v___y_3170_ = v___y_3206_;
v___y_3171_ = v___y_3207_;
v___y_3172_ = v___x_3249_;
goto v___jp_3142_;
}
else
{
size_t v___x_3250_; size_t v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
v___x_3250_ = ((size_t)0ULL);
v___x_3251_ = lean_usize_of_nat(v___x_3245_);
v___x_3252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3207_, v___x_3250_, v___x_3251_, v___x_2981_);
lean_inc_ref(v___y_3197_);
v___x_3253_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3197_, v_env_3231_, v___x_3252_);
v___y_3143_ = v___y_3186_;
v___y_3144_ = v___y_3187_;
v___y_3145_ = v___y_3189_;
v___y_3146_ = v___y_3188_;
v___y_3147_ = v___y_3190_;
v___y_3148_ = v___y_3192_;
v___y_3149_ = v___y_3191_;
v___y_3150_ = v___y_3193_;
v___y_3151_ = v___y_3194_;
v___y_3152_ = v___y_3195_;
v___y_3153_ = v___x_3244_;
v___y_3154_ = v___y_3209_;
v___y_3155_ = v___y_3196_;
v___y_3156_ = v___y_3198_;
v___y_3157_ = v___y_3199_;
v___y_3158_ = v___y_3201_;
v___y_3159_ = v___y_3202_;
v___y_3160_ = v___y_3203_;
v___y_3161_ = v___y_3204_;
v___y_3162_ = v___y_3205_;
v_nextMacroScope_3163_ = v_nextMacroScope_3232_;
v_ngen_3164_ = v_ngen_3233_;
v_auxDeclNGen_3165_ = v_auxDeclNGen_3234_;
v_traceState_3166_ = v_traceState_3235_;
v_messages_3167_ = v_messages_3236_;
v_infoState_3168_ = v_infoState_3237_;
v_snapshotTasks_3169_ = v_snapshotTasks_3238_;
v___y_3170_ = v___y_3206_;
v___y_3171_ = v___y_3207_;
v___y_3172_ = v___x_3253_;
goto v___jp_3142_;
}
}
else
{
size_t v___x_3254_; size_t v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; 
v___x_3254_ = ((size_t)0ULL);
v___x_3255_ = lean_usize_of_nat(v___x_3245_);
v___x_3256_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3207_, v___x_3254_, v___x_3255_, v___x_2981_);
lean_inc_ref(v___y_3197_);
v___x_3257_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3197_, v_env_3231_, v___x_3256_);
v___y_3143_ = v___y_3186_;
v___y_3144_ = v___y_3187_;
v___y_3145_ = v___y_3189_;
v___y_3146_ = v___y_3188_;
v___y_3147_ = v___y_3190_;
v___y_3148_ = v___y_3192_;
v___y_3149_ = v___y_3191_;
v___y_3150_ = v___y_3193_;
v___y_3151_ = v___y_3194_;
v___y_3152_ = v___y_3195_;
v___y_3153_ = v___x_3244_;
v___y_3154_ = v___y_3209_;
v___y_3155_ = v___y_3196_;
v___y_3156_ = v___y_3198_;
v___y_3157_ = v___y_3199_;
v___y_3158_ = v___y_3201_;
v___y_3159_ = v___y_3202_;
v___y_3160_ = v___y_3203_;
v___y_3161_ = v___y_3204_;
v___y_3162_ = v___y_3205_;
v_nextMacroScope_3163_ = v_nextMacroScope_3232_;
v_ngen_3164_ = v_ngen_3233_;
v_auxDeclNGen_3165_ = v_auxDeclNGen_3234_;
v_traceState_3166_ = v_traceState_3235_;
v_messages_3167_ = v_messages_3236_;
v_infoState_3168_ = v_infoState_3237_;
v_snapshotTasks_3169_ = v_snapshotTasks_3238_;
v___y_3170_ = v___y_3206_;
v___y_3171_ = v___y_3207_;
v___y_3172_ = v___x_3257_;
goto v___jp_3142_;
}
}
}
}
}
}
}
v___jp_3264_:
{
if (v___y_3288_ == 0)
{
lean_object* v___x_3289_; lean_object* v_env_3290_; lean_object* v_nextMacroScope_3291_; lean_object* v_ngen_3292_; lean_object* v_auxDeclNGen_3293_; lean_object* v_traceState_3294_; lean_object* v_messages_3295_; lean_object* v_infoState_3296_; lean_object* v_snapshotTasks_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3306_; 
v___x_3289_ = lean_st_ref_take(v___y_3282_);
v_env_3290_ = lean_ctor_get(v___x_3289_, 0);
v_nextMacroScope_3291_ = lean_ctor_get(v___x_3289_, 1);
v_ngen_3292_ = lean_ctor_get(v___x_3289_, 2);
v_auxDeclNGen_3293_ = lean_ctor_get(v___x_3289_, 3);
v_traceState_3294_ = lean_ctor_get(v___x_3289_, 4);
v_messages_3295_ = lean_ctor_get(v___x_3289_, 6);
v_infoState_3296_ = lean_ctor_get(v___x_3289_, 7);
v_snapshotTasks_3297_ = lean_ctor_get(v___x_3289_, 8);
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3306_ == 0)
{
lean_object* v_unused_3307_; 
v_unused_3307_ = lean_ctor_get(v___x_3289_, 5);
lean_dec(v_unused_3307_);
v___x_3299_ = v___x_3289_;
v_isShared_3300_ = v_isSharedCheck_3306_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_snapshotTasks_3297_);
lean_inc(v_infoState_3296_);
lean_inc(v_messages_3295_);
lean_inc(v_traceState_3294_);
lean_inc(v_auxDeclNGen_3293_);
lean_inc(v_ngen_3292_);
lean_inc(v_nextMacroScope_3291_);
lean_inc(v_env_3290_);
lean_dec(v___x_3289_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3306_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v___x_3301_; lean_object* v___x_3303_; 
v___x_3301_ = l_Lean_Kernel_enableDiag(v_env_3290_, v___y_3280_);
lean_inc_ref(v___y_3286_);
if (v_isShared_3300_ == 0)
{
lean_ctor_set(v___x_3299_, 5, v___y_3286_);
lean_ctor_set(v___x_3299_, 0, v___x_3301_);
v___x_3303_ = v___x_3299_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v___x_3301_);
lean_ctor_set(v_reuseFailAlloc_3305_, 1, v_nextMacroScope_3291_);
lean_ctor_set(v_reuseFailAlloc_3305_, 2, v_ngen_3292_);
lean_ctor_set(v_reuseFailAlloc_3305_, 3, v_auxDeclNGen_3293_);
lean_ctor_set(v_reuseFailAlloc_3305_, 4, v_traceState_3294_);
lean_ctor_set(v_reuseFailAlloc_3305_, 5, v___y_3286_);
lean_ctor_set(v_reuseFailAlloc_3305_, 6, v_messages_3295_);
lean_ctor_set(v_reuseFailAlloc_3305_, 7, v_infoState_3296_);
lean_ctor_set(v_reuseFailAlloc_3305_, 8, v_snapshotTasks_3297_);
v___x_3303_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
lean_object* v___x_3304_; 
v___x_3304_ = lean_st_ref_put(v___y_3282_, v___x_3303_);
lean_inc(v___y_3282_);
v___y_3186_ = v___y_3265_;
v___y_3187_ = v___y_3266_;
v___y_3188_ = v___y_3268_;
v___y_3189_ = v___y_3267_;
v___y_3190_ = v___y_3269_;
v___y_3191_ = v___y_3271_;
v___y_3192_ = v___y_3270_;
v___y_3193_ = v___y_3272_;
v___y_3194_ = v___y_3273_;
v___y_3195_ = v___y_3274_;
v___y_3196_ = v___y_3275_;
v___y_3197_ = v___y_3276_;
v___y_3198_ = v___y_3278_;
v___y_3199_ = v___y_3279_;
v___y_3200_ = v___y_3280_;
v___y_3201_ = v___y_3281_;
v___y_3202_ = v___y_3282_;
v___y_3203_ = v___y_3283_;
v___y_3204_ = v___y_3284_;
v___y_3205_ = v___y_3285_;
v___y_3206_ = v___y_3286_;
v___y_3207_ = v___y_3287_;
v___y_3208_ = v___y_3277_;
v___y_3209_ = v___y_3282_;
goto v___jp_3185_;
}
}
}
else
{
lean_inc(v___y_3282_);
v___y_3186_ = v___y_3265_;
v___y_3187_ = v___y_3266_;
v___y_3188_ = v___y_3268_;
v___y_3189_ = v___y_3267_;
v___y_3190_ = v___y_3269_;
v___y_3191_ = v___y_3271_;
v___y_3192_ = v___y_3270_;
v___y_3193_ = v___y_3272_;
v___y_3194_ = v___y_3273_;
v___y_3195_ = v___y_3274_;
v___y_3196_ = v___y_3275_;
v___y_3197_ = v___y_3276_;
v___y_3198_ = v___y_3278_;
v___y_3199_ = v___y_3279_;
v___y_3200_ = v___y_3280_;
v___y_3201_ = v___y_3281_;
v___y_3202_ = v___y_3282_;
v___y_3203_ = v___y_3283_;
v___y_3204_ = v___y_3284_;
v___y_3205_ = v___y_3285_;
v___y_3206_ = v___y_3286_;
v___y_3207_ = v___y_3287_;
v___y_3208_ = v___y_3277_;
v___y_3209_ = v___y_3282_;
goto v___jp_3185_;
}
}
v___jp_3314_:
{
lean_object* v___x_3323_; 
if (v_isShared_2946_ == 0)
{
lean_ctor_set_tag(v___x_2945_, 0);
lean_ctor_set(v___x_2945_, 1, v___y_3321_);
lean_ctor_set(v___x_2945_, 0, v___y_3320_);
v___x_3323_ = v___x_2945_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v___y_3320_);
lean_ctor_set(v_reuseFailAlloc_3419_, 1, v___y_3321_);
v___x_3323_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v_moduleData_3327_; lean_object* v___x_3328_; uint8_t v___x_3329_; 
v___x_3324_ = lean_box(0);
lean_inc_ref(v___y_3319_);
v___x_3325_ = l_Lean_EnvExtension_setState___redArg(v___y_3319_, v___y_3318_, v___x_3323_, v___x_3324_);
v___x_3326_ = l_Lean_Environment_header(v___x_3325_);
v_moduleData_3327_ = lean_ctor_get(v___x_3326_, 6);
lean_inc_ref(v_moduleData_3327_);
lean_dec_ref(v___x_3326_);
v___x_3328_ = lean_array_get_size(v_moduleData_3327_);
v___x_3329_ = lean_nat_dec_lt(v___y_3317_, v___x_3328_);
if (v___x_3329_ == 0)
{
lean_object* v___x_3330_; lean_object* v___x_3331_; 
lean_dec_ref(v_moduleData_3327_);
lean_dec_ref(v___x_3325_);
lean_dec(v___y_3317_);
lean_dec(v___y_3316_);
lean_dec(v___y_3315_);
lean_dec_ref(v___x_2988_);
lean_del_object(v___x_2972_);
lean_dec(v_fst_2969_);
lean_dec(v_name_2958_);
lean_dec(v_head_2951_);
lean_del_object(v___x_2949_);
lean_dec(v_head_2947_);
v___x_3330_ = lean_obj_once(&l_main___closed__22, &l_main___closed__22_once, _init_l_main___closed__22);
v___x_3331_ = l_panic___at___00main_spec__5(v___x_3330_);
return v___x_3331_;
}
else
{
lean_object* v_base_3332_; lean_object* v_private_3333_; lean_object* v_header_3334_; lean_object* v_serverBaseExts_3335_; lean_object* v_checked_3336_; lean_object* v_asyncConstsMap_3337_; lean_object* v_asyncCtx_x3f_3338_; lean_object* v_importRealizationCtx_x3f_3339_; lean_object* v_localRealizationCtxMap_3340_; lean_object* v_allRealizations_3341_; uint8_t v_isExporting_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3417_; 
v_base_3332_ = lean_ctor_get(v___x_3325_, 0);
lean_inc_ref(v_base_3332_);
v_private_3333_ = lean_ctor_get(v_base_3332_, 0);
lean_inc(v_private_3333_);
v_header_3334_ = lean_ctor_get(v_private_3333_, 5);
lean_inc_ref(v_header_3334_);
v_serverBaseExts_3335_ = lean_ctor_get(v___x_3325_, 1);
v_checked_3336_ = lean_ctor_get(v___x_3325_, 2);
v_asyncConstsMap_3337_ = lean_ctor_get(v___x_3325_, 3);
v_asyncCtx_x3f_3338_ = lean_ctor_get(v___x_3325_, 4);
v_importRealizationCtx_x3f_3339_ = lean_ctor_get(v___x_3325_, 5);
v_localRealizationCtxMap_3340_ = lean_ctor_get(v___x_3325_, 6);
v_allRealizations_3341_ = lean_ctor_get(v___x_3325_, 7);
v_isExporting_3342_ = lean_ctor_get_uint8(v___x_3325_, sizeof(void*)*8);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3325_);
if (v_isSharedCheck_3417_ == 0)
{
lean_object* v_unused_3418_; 
v_unused_3418_ = lean_ctor_get(v___x_3325_, 0);
lean_dec(v_unused_3418_);
v___x_3344_ = v___x_3325_;
v_isShared_3345_ = v_isSharedCheck_3417_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_allRealizations_3341_);
lean_inc(v_localRealizationCtxMap_3340_);
lean_inc(v_importRealizationCtx_x3f_3339_);
lean_inc(v_asyncCtx_x3f_3338_);
lean_inc(v_asyncConstsMap_3337_);
lean_inc(v_checked_3336_);
lean_inc(v_serverBaseExts_3335_);
lean_dec(v___x_3325_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3417_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v_public_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3415_; 
v_public_3346_ = lean_ctor_get(v_base_3332_, 1);
v_isSharedCheck_3415_ = !lean_is_exclusive(v_base_3332_);
if (v_isSharedCheck_3415_ == 0)
{
lean_object* v_unused_3416_; 
v_unused_3416_ = lean_ctor_get(v_base_3332_, 0);
lean_dec(v_unused_3416_);
v___x_3348_ = v_base_3332_;
v_isShared_3349_ = v_isSharedCheck_3415_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_public_3346_);
lean_dec(v_base_3332_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3415_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v_constants_3350_; uint8_t v_quotInit_3351_; lean_object* v_diagnostics_3352_; lean_object* v_const2ModIdx_3353_; lean_object* v_extensions_3354_; lean_object* v_irBaseExts_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3413_; 
v_constants_3350_ = lean_ctor_get(v_private_3333_, 0);
v_quotInit_3351_ = lean_ctor_get_uint8(v_private_3333_, sizeof(void*)*6);
v_diagnostics_3352_ = lean_ctor_get(v_private_3333_, 1);
v_const2ModIdx_3353_ = lean_ctor_get(v_private_3333_, 2);
v_extensions_3354_ = lean_ctor_get(v_private_3333_, 3);
v_irBaseExts_3355_ = lean_ctor_get(v_private_3333_, 4);
v_isSharedCheck_3413_ = !lean_is_exclusive(v_private_3333_);
if (v_isSharedCheck_3413_ == 0)
{
lean_object* v_unused_3414_; 
v_unused_3414_ = lean_ctor_get(v_private_3333_, 5);
lean_dec(v_unused_3414_);
v___x_3357_ = v_private_3333_;
v_isShared_3358_ = v_isSharedCheck_3413_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_irBaseExts_3355_);
lean_inc(v_extensions_3354_);
lean_inc(v_const2ModIdx_3353_);
lean_inc(v_diagnostics_3352_);
lean_inc(v_constants_3350_);
lean_dec(v_private_3333_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3413_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
uint32_t v_trustLevel_3359_; lean_object* v_mainModule_3360_; uint8_t v_isModule_3361_; lean_object* v_regions_3362_; lean_object* v_modules_3363_; lean_object* v_moduleName2Idx_3364_; lean_object* v_importAllModules_3365_; lean_object* v_moduleData_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3411_; 
v_trustLevel_3359_ = lean_ctor_get_uint32(v_header_3334_, sizeof(void*)*7);
v_mainModule_3360_ = lean_ctor_get(v_header_3334_, 0);
v_isModule_3361_ = lean_ctor_get_uint8(v_header_3334_, sizeof(void*)*7 + 4);
v_regions_3362_ = lean_ctor_get(v_header_3334_, 2);
v_modules_3363_ = lean_ctor_get(v_header_3334_, 3);
v_moduleName2Idx_3364_ = lean_ctor_get(v_header_3334_, 4);
v_importAllModules_3365_ = lean_ctor_get(v_header_3334_, 5);
v_moduleData_3366_ = lean_ctor_get(v_header_3334_, 6);
v_isSharedCheck_3411_ = !lean_is_exclusive(v_header_3334_);
if (v_isSharedCheck_3411_ == 0)
{
lean_object* v_unused_3412_; 
v_unused_3412_ = lean_ctor_get(v_header_3334_, 1);
lean_dec(v_unused_3412_);
v___x_3368_ = v_header_3334_;
v_isShared_3369_ = v_isSharedCheck_3411_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_moduleData_3366_);
lean_inc(v_importAllModules_3365_);
lean_inc(v_moduleName2Idx_3364_);
lean_inc(v_modules_3363_);
lean_inc(v_regions_3362_);
lean_inc(v_mainModule_3360_);
lean_dec(v_header_3334_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3411_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v___x_3370_; lean_object* v_imports_3371_; lean_object* v___x_3373_; 
v___x_3370_ = lean_array_fget(v_moduleData_3327_, v___y_3317_);
lean_dec_ref(v_moduleData_3327_);
v_imports_3371_ = lean_ctor_get(v___x_3370_, 0);
lean_inc_ref(v_imports_3371_);
lean_dec(v___x_3370_);
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 1, v_imports_3371_);
v___x_3373_ = v___x_3368_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 7, 5);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_mainModule_3360_);
lean_ctor_set(v_reuseFailAlloc_3410_, 1, v_imports_3371_);
lean_ctor_set(v_reuseFailAlloc_3410_, 2, v_regions_3362_);
lean_ctor_set(v_reuseFailAlloc_3410_, 3, v_modules_3363_);
lean_ctor_set(v_reuseFailAlloc_3410_, 4, v_moduleName2Idx_3364_);
lean_ctor_set(v_reuseFailAlloc_3410_, 5, v_importAllModules_3365_);
lean_ctor_set(v_reuseFailAlloc_3410_, 6, v_moduleData_3366_);
lean_ctor_set_uint32(v_reuseFailAlloc_3410_, sizeof(void*)*7, v_trustLevel_3359_);
lean_ctor_set_uint8(v_reuseFailAlloc_3410_, sizeof(void*)*7 + 4, v_isModule_3361_);
v___x_3373_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
lean_object* v___x_3375_; 
if (v_isShared_3358_ == 0)
{
lean_ctor_set(v___x_3357_, 5, v___x_3373_);
v___x_3375_ = v___x_3357_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_constants_3350_);
lean_ctor_set(v_reuseFailAlloc_3409_, 1, v_diagnostics_3352_);
lean_ctor_set(v_reuseFailAlloc_3409_, 2, v_const2ModIdx_3353_);
lean_ctor_set(v_reuseFailAlloc_3409_, 3, v_extensions_3354_);
lean_ctor_set(v_reuseFailAlloc_3409_, 4, v_irBaseExts_3355_);
lean_ctor_set(v_reuseFailAlloc_3409_, 5, v___x_3373_);
lean_ctor_set_uint8(v_reuseFailAlloc_3409_, sizeof(void*)*6, v_quotInit_3351_);
v___x_3375_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
lean_object* v___x_3377_; 
if (v_isShared_3349_ == 0)
{
lean_ctor_set(v___x_3348_, 0, v___x_3375_);
v___x_3377_ = v___x_3348_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v___x_3375_);
lean_ctor_set(v_reuseFailAlloc_3408_, 1, v_public_3346_);
v___x_3377_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
lean_object* v___x_3379_; 
if (v_isShared_3345_ == 0)
{
lean_ctor_set(v___x_3344_, 0, v___x_3377_);
v___x_3379_ = v___x_3344_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v___x_3377_);
lean_ctor_set(v_reuseFailAlloc_3407_, 1, v_serverBaseExts_3335_);
lean_ctor_set(v_reuseFailAlloc_3407_, 2, v_checked_3336_);
lean_ctor_set(v_reuseFailAlloc_3407_, 3, v_asyncConstsMap_3337_);
lean_ctor_set(v_reuseFailAlloc_3407_, 4, v_asyncCtx_x3f_3338_);
lean_ctor_set(v_reuseFailAlloc_3407_, 5, v_importRealizationCtx_x3f_3339_);
lean_ctor_set(v_reuseFailAlloc_3407_, 6, v_localRealizationCtxMap_3340_);
lean_ctor_set(v_reuseFailAlloc_3407_, 7, v_allRealizations_3341_);
lean_ctor_set_uint8(v_reuseFailAlloc_3407_, sizeof(void*)*8, v_isExporting_3342_);
v___x_3379_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v_env_3403_; lean_object* v___x_3404_; uint8_t v___x_3405_; uint8_t v___x_3406_; 
v___x_3380_ = l_Lean_Compiler_LCNF_postponedCompileDeclsExt;
v___x_3381_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2982_, v___x_3380_, v___x_3379_, v___y_3317_, v___x_3313_);
lean_dec(v___y_3317_);
v___x_3382_ = l_Lean_firstFrontendMacroScope;
v___x_3383_ = lean_obj_once(&l_main___closed__23, &l_main___closed__23_once, _init_l_main___closed__23);
v___x_3384_ = ((lean_object*)(l_main___closed__26));
lean_inc_n(v___y_3316_, 3);
v___x_3385_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3385_, 0, v___y_3316_);
lean_ctor_set(v___x_3385_, 1, v___x_3310_);
lean_ctor_set(v___x_3385_, 2, v___x_2975_);
v___x_3386_ = lean_obj_once(&l_main___closed__27, &l_main___closed__27_once, _init_l_main___closed__27);
v___x_3387_ = lean_obj_once(&l_main___closed__30, &l_main___closed__30_once, _init_l_main___closed__30);
v___x_3388_ = lean_obj_once(&l_main___closed__31, &l_main___closed__31_once, _init_l_main___closed__31);
v___x_3389_ = lean_obj_once(&l_main___closed__32, &l_main___closed__32_once, _init_l_main___closed__32);
v___x_3390_ = ((lean_object*)(l_main___closed__33));
lean_inc_ref(v___x_3385_);
v___x_3391_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3379_);
lean_ctor_set(v___x_3391_, 1, v___x_3383_);
lean_ctor_set(v___x_3391_, 2, v___x_3384_);
lean_ctor_set(v___x_3391_, 3, v___x_3385_);
lean_ctor_set(v___x_3391_, 4, v___x_3386_);
lean_ctor_set(v___x_3391_, 5, v___x_3387_);
lean_ctor_set(v___x_3391_, 6, v___x_3388_);
lean_ctor_set(v___x_3391_, 7, v___x_3389_);
lean_ctor_set(v___x_3391_, 8, v___x_3390_);
v___x_3392_ = lean_st_mk_ref(v___x_3391_);
v___x_3393_ = l_Lean_inheritedTraceOptions;
v___x_3394_ = lean_st_ref_get(v___x_3393_);
v___x_3395_ = lean_st_ref_get(v___x_3392_);
v___x_3396_ = l_Lean_instInhabitedFileMap_default;
v___x_3397_ = lean_unsigned_to_nat(1000u);
v___x_3398_ = l_Lean_Core_getMaxHeartbeats(v___x_2988_);
v___x_3399_ = lean_box(0);
v___x_3400_ = lean_box(0);
lean_inc_ref(v___x_2988_);
lean_inc(v_head_2947_);
v___x_3401_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3401_, 0, v_head_2947_);
lean_ctor_set(v___x_3401_, 1, v___x_3396_);
lean_ctor_set(v___x_3401_, 2, v___x_2988_);
lean_ctor_set(v___x_3401_, 3, v___x_3397_);
lean_ctor_set(v___x_3401_, 4, v___y_3316_);
lean_ctor_set(v___x_3401_, 5, v___x_2975_);
lean_ctor_set(v___x_3401_, 6, v___x_2987_);
lean_ctor_set(v___x_3401_, 7, v___x_3398_);
lean_ctor_set(v___x_3401_, 8, v___y_3316_);
lean_ctor_set(v___x_3401_, 9, v___x_3382_);
lean_ctor_set(v___x_3401_, 10, v___x_3399_);
lean_ctor_set(v___x_3401_, 11, v___x_3394_);
v___x_3402_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3402_, 0, v___x_3401_);
lean_ctor_set(v___x_3402_, 1, v___x_2987_);
lean_ctor_set(v___x_3402_, 2, v___x_3400_);
lean_ctor_set_uint8(v___x_3402_, sizeof(void*)*3, v___x_2961_);
lean_ctor_set_uint8(v___x_3402_, sizeof(void*)*3 + 1, v___x_2961_);
v_env_3403_ = lean_ctor_get(v___x_3395_, 0);
lean_inc_ref(v_env_3403_);
lean_dec(v___x_3395_);
v___x_3404_ = l_Lean_diagnostics;
v___x_3405_ = l_Lean_Option_get___at___00main_spec__8(v___x_2988_, v___x_3404_);
v___x_3406_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3403_);
lean_dec_ref(v_env_3403_);
if (v___x_3405_ == 0)
{
if (v___x_3406_ == 0)
{
v___y_3265_ = v___x_2975_;
v___y_3266_ = v___x_3382_;
v___y_3267_ = v___x_3393_;
v___y_3268_ = v___y_3315_;
v___y_3269_ = v___x_3399_;
v___y_3270_ = v___x_3329_;
v___y_3271_ = v___x_3396_;
v___y_3272_ = v___x_3400_;
v___y_3273_ = v___x_3387_;
v___y_3274_ = v___x_3389_;
v___y_3275_ = v___x_3385_;
v___y_3276_ = v___x_3380_;
v___y_3277_ = v___x_3402_;
v___y_3278_ = v___x_3383_;
v___y_3279_ = v___x_3386_;
v___y_3280_ = v___x_3405_;
v___y_3281_ = v___x_3384_;
v___y_3282_ = v___x_3392_;
v___y_3283_ = v___y_3316_;
v___y_3284_ = v___x_3388_;
v___y_3285_ = v___x_3390_;
v___y_3286_ = v___x_3387_;
v___y_3287_ = v___x_3381_;
v___y_3288_ = v___x_3329_;
goto v___jp_3264_;
}
else
{
v___y_3265_ = v___x_2975_;
v___y_3266_ = v___x_3382_;
v___y_3267_ = v___x_3393_;
v___y_3268_ = v___y_3315_;
v___y_3269_ = v___x_3399_;
v___y_3270_ = v___x_3329_;
v___y_3271_ = v___x_3396_;
v___y_3272_ = v___x_3400_;
v___y_3273_ = v___x_3387_;
v___y_3274_ = v___x_3389_;
v___y_3275_ = v___x_3385_;
v___y_3276_ = v___x_3380_;
v___y_3277_ = v___x_3402_;
v___y_3278_ = v___x_3383_;
v___y_3279_ = v___x_3386_;
v___y_3280_ = v___x_3405_;
v___y_3281_ = v___x_3384_;
v___y_3282_ = v___x_3392_;
v___y_3283_ = v___y_3316_;
v___y_3284_ = v___x_3388_;
v___y_3285_ = v___x_3390_;
v___y_3286_ = v___x_3387_;
v___y_3287_ = v___x_3381_;
v___y_3288_ = v___x_3405_;
goto v___jp_3264_;
}
}
else
{
v___y_3265_ = v___x_2975_;
v___y_3266_ = v___x_3382_;
v___y_3267_ = v___x_3393_;
v___y_3268_ = v___y_3315_;
v___y_3269_ = v___x_3399_;
v___y_3270_ = v___x_3329_;
v___y_3271_ = v___x_3396_;
v___y_3272_ = v___x_3400_;
v___y_3273_ = v___x_3387_;
v___y_3274_ = v___x_3389_;
v___y_3275_ = v___x_3385_;
v___y_3276_ = v___x_3380_;
v___y_3277_ = v___x_3402_;
v___y_3278_ = v___x_3383_;
v___y_3279_ = v___x_3386_;
v___y_3280_ = v___x_3405_;
v___y_3281_ = v___x_3384_;
v___y_3282_ = v___x_3392_;
v___y_3283_ = v___y_3316_;
v___y_3284_ = v___x_3388_;
v___y_3285_ = v___x_3390_;
v___y_3286_ = v___x_3387_;
v___y_3287_ = v___x_3381_;
v___y_3288_ = v___x_3406_;
goto v___jp_3264_;
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
v___jp_3420_:
{
lean_object* v___x_3425_; lean_object* v_toEnvExtension_3426_; lean_object* v_asyncMode_3427_; lean_object* v___x_3428_; lean_object* v_importedEntries_3429_; lean_object* v_state_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; uint8_t v___x_3433_; 
v___x_3425_ = l_Lean_IR_declMapExt;
v_toEnvExtension_3426_ = lean_ctor_get(v___x_3425_, 0);
v_asyncMode_3427_ = lean_ctor_get(v_toEnvExtension_3426_, 2);
lean_inc(v___y_3422_);
lean_inc_ref(v___y_3424_);
v___x_3428_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2979_, v_toEnvExtension_3426_, v___y_3424_, v_asyncMode_3427_, v___y_3422_);
v_importedEntries_3429_ = lean_ctor_get(v___x_3428_, 0);
lean_inc_ref(v_importedEntries_3429_);
v_state_3430_ = lean_ctor_get(v___x_3428_, 1);
lean_inc(v_state_3430_);
lean_dec(v___x_3428_);
v___x_3431_ = lean_array_get_borrowed(v___x_2980_, v_importedEntries_3429_, v___y_3423_);
v___x_3432_ = lean_array_get_size(v___x_3431_);
v___x_3433_ = lean_nat_dec_lt(v___x_2987_, v___x_3432_);
if (v___x_3433_ == 0)
{
v___y_3315_ = v___y_3421_;
v___y_3316_ = v___y_3422_;
v___y_3317_ = v___y_3423_;
v___y_3318_ = v___y_3424_;
v___y_3319_ = v_toEnvExtension_3426_;
v___y_3320_ = v_importedEntries_3429_;
v___y_3321_ = v_state_3430_;
goto v___jp_3314_;
}
else
{
uint8_t v___x_3434_; 
v___x_3434_ = lean_nat_dec_le(v___x_3432_, v___x_3432_);
if (v___x_3434_ == 0)
{
if (v___x_3433_ == 0)
{
v___y_3315_ = v___y_3421_;
v___y_3316_ = v___y_3422_;
v___y_3317_ = v___y_3423_;
v___y_3318_ = v___y_3424_;
v___y_3319_ = v_toEnvExtension_3426_;
v___y_3320_ = v_importedEntries_3429_;
v___y_3321_ = v_state_3430_;
goto v___jp_3314_;
}
else
{
size_t v___x_3435_; size_t v___x_3436_; lean_object* v___x_3437_; 
v___x_3435_ = ((size_t)0ULL);
v___x_3436_ = lean_usize_of_nat(v___x_3432_);
lean_inc_ref(v___y_3424_);
v___x_3437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3424_, v___x_3431_, v___x_3435_, v___x_3436_, v_state_3430_);
v___y_3315_ = v___y_3421_;
v___y_3316_ = v___y_3422_;
v___y_3317_ = v___y_3423_;
v___y_3318_ = v___y_3424_;
v___y_3319_ = v_toEnvExtension_3426_;
v___y_3320_ = v_importedEntries_3429_;
v___y_3321_ = v___x_3437_;
goto v___jp_3314_;
}
}
else
{
size_t v___x_3438_; size_t v___x_3439_; lean_object* v___x_3440_; 
v___x_3438_ = ((size_t)0ULL);
v___x_3439_ = lean_usize_of_nat(v___x_3432_);
lean_inc_ref(v___y_3424_);
v___x_3440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3424_, v___x_3431_, v___x_3438_, v___x_3439_, v_state_3430_);
v___y_3315_ = v___y_3421_;
v___y_3316_ = v___y_3422_;
v___y_3317_ = v___y_3423_;
v___y_3318_ = v___y_3424_;
v___y_3319_ = v_toEnvExtension_3426_;
v___y_3320_ = v_importedEntries_3429_;
v___y_3321_ = v___x_3440_;
goto v___jp_3314_;
}
}
}
v___jp_3441_:
{
uint8_t v___x_3448_; 
v___x_3448_ = lean_nat_dec_lt(v___x_2987_, v___y_3446_);
if (v___x_3448_ == 0)
{
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3443_);
v___y_3421_ = v___y_3442_;
v___y_3422_ = v___y_3444_;
v___y_3423_ = v___y_3445_;
v___y_3424_ = v___y_3447_;
goto v___jp_3420_;
}
else
{
uint8_t v___x_3449_; 
v___x_3449_ = lean_nat_dec_le(v___y_3446_, v___y_3446_);
if (v___x_3449_ == 0)
{
if (v___x_3448_ == 0)
{
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3443_);
v___y_3421_ = v___y_3442_;
v___y_3422_ = v___y_3444_;
v___y_3423_ = v___y_3445_;
v___y_3424_ = v___y_3447_;
goto v___jp_3420_;
}
else
{
size_t v___x_3450_; size_t v___x_3451_; lean_object* v___x_3452_; 
v___x_3450_ = ((size_t)0ULL);
v___x_3451_ = lean_usize_of_nat(v___y_3446_);
lean_dec(v___y_3446_);
v___x_3452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3443_, v___x_3450_, v___x_3451_, v___y_3447_);
lean_dec_ref(v___y_3443_);
v___y_3421_ = v___y_3442_;
v___y_3422_ = v___y_3444_;
v___y_3423_ = v___y_3445_;
v___y_3424_ = v___x_3452_;
goto v___jp_3420_;
}
}
else
{
size_t v___x_3453_; size_t v___x_3454_; lean_object* v___x_3455_; 
v___x_3453_ = ((size_t)0ULL);
v___x_3454_ = lean_usize_of_nat(v___y_3446_);
lean_dec(v___y_3446_);
v___x_3455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3443_, v___x_3453_, v___x_3454_, v___y_3447_);
lean_dec_ref(v___y_3443_);
v___y_3421_ = v___y_3442_;
v___y_3422_ = v___y_3444_;
v___y_3423_ = v___y_3445_;
v___y_3424_ = v___x_3455_;
goto v___jp_3420_;
}
}
}
v___jp_3456_:
{
lean_object* v___x_3462_; uint8_t v___x_3463_; 
v___x_3462_ = lean_array_get_size(v___y_3461_);
v___x_3463_ = lean_nat_dec_lt(v___x_2987_, v___x_3462_);
if (v___x_3463_ == 0)
{
v___y_3442_ = v___y_3457_;
v___y_3443_ = v___y_3461_;
v___y_3444_ = v___y_3460_;
v___y_3445_ = v___y_3458_;
v___y_3446_ = v___x_3462_;
v___y_3447_ = v___y_3459_;
goto v___jp_3441_;
}
else
{
uint8_t v___x_3464_; 
v___x_3464_ = lean_nat_dec_le(v___x_3462_, v___x_3462_);
if (v___x_3464_ == 0)
{
if (v___x_3463_ == 0)
{
v___y_3442_ = v___y_3457_;
v___y_3443_ = v___y_3461_;
v___y_3444_ = v___y_3460_;
v___y_3445_ = v___y_3458_;
v___y_3446_ = v___x_3462_;
v___y_3447_ = v___y_3459_;
goto v___jp_3441_;
}
else
{
size_t v___x_3465_; size_t v___x_3466_; lean_object* v___x_3467_; 
v___x_3465_ = ((size_t)0ULL);
v___x_3466_ = lean_usize_of_nat(v___x_3462_);
v___x_3467_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v___y_3461_, v___x_3465_, v___x_3466_, v___y_3459_);
v___y_3442_ = v___y_3457_;
v___y_3443_ = v___y_3461_;
v___y_3444_ = v___y_3460_;
v___y_3445_ = v___y_3458_;
v___y_3446_ = v___x_3462_;
v___y_3447_ = v___x_3467_;
goto v___jp_3441_;
}
}
else
{
size_t v___x_3468_; size_t v___x_3469_; lean_object* v___x_3470_; 
v___x_3468_ = ((size_t)0ULL);
v___x_3469_ = lean_usize_of_nat(v___x_3462_);
v___x_3470_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v___y_3461_, v___x_3468_, v___x_3469_, v___y_3459_);
v___y_3442_ = v___y_3457_;
v___y_3443_ = v___y_3461_;
v___y_3444_ = v___y_3460_;
v___y_3445_ = v___y_3458_;
v___y_3446_ = v___x_3462_;
v___y_3447_ = v___x_3470_;
goto v___jp_3441_;
}
}
}
v___jp_3472_:
{
lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___f_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
v___x_3474_ = l_Lean_instInhabitedImportState_default;
v___x_3475_ = lean_box(v___x_3313_);
v___x_3476_ = lean_box(v___y_3473_);
v___x_3477_ = lean_box(v___x_2984_);
v___x_3478_ = lean_box(v___x_3471_);
v___x_3479_ = lean_box(v___x_2961_);
lean_inc_ref(v___x_2988_);
lean_inc(v_name_2958_);
v___f_3480_ = lean_alloc_closure((void*)(l_main___lam__0___boxed), 11, 10);
lean_closure_set(v___f_3480_, 0, v___x_3474_);
lean_closure_set(v___f_3480_, 1, v___x_3312_);
lean_closure_set(v___f_3480_, 2, v___x_3475_);
lean_closure_set(v___f_3480_, 3, v_importArts_2959_);
lean_closure_set(v___f_3480_, 4, v___x_3476_);
lean_closure_set(v___f_3480_, 5, v___x_3477_);
lean_closure_set(v___f_3480_, 6, v_name_2958_);
lean_closure_set(v___f_3480_, 7, v___x_3478_);
lean_closure_set(v___f_3480_, 8, v___x_2988_);
lean_closure_set(v___f_3480_, 9, v___x_3479_);
v___x_3481_ = lean_alloc_closure((void*)(l_Lean_withImporting___boxed), 3, 2);
lean_closure_set(v___x_3481_, 0, lean_box(0));
lean_closure_set(v___x_3481_, 1, v___f_3480_);
v___x_3482_ = lean_box(0);
v___x_3483_ = l_Lean_profileitIOUnsafe___redArg(v___x_3308_, v___x_2988_, v___x_3481_, v___x_3482_);
if (lean_obj_tag(v___x_3483_) == 0)
{
lean_object* v_a_3484_; lean_object* v___x_3485_; lean_object* v_ext_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
v_a_3484_ = lean_ctor_get(v___x_3483_, 0);
lean_inc(v_a_3484_);
lean_dec_ref_known(v___x_3483_, 1);
v___x_3485_ = l_Lean_Compiler_CSimp_ext;
v_ext_3486_ = lean_ctor_get(v___x_3485_, 1);
lean_inc(v_name_2958_);
v___x_3487_ = l_Lean_Environment_setMainModule(v_a_3484_, v_name_2958_);
lean_inc_ref(v_ext_3486_);
v___x_3488_ = l_main___elam__0___redArg(v___x_3482_, v___x_2974_, v_ext_3486_, v___x_3487_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_a_3489_; lean_object* v___x_3490_; lean_object* v_ext_3491_; lean_object* v___x_3492_; 
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
lean_inc(v_a_3489_);
lean_dec_ref_known(v___x_3488_, 1);
v___x_3490_ = l_Lean_Meta_instanceExtension;
v_ext_3491_ = lean_ctor_get(v___x_3490_, 1);
lean_inc_ref(v_ext_3491_);
v___x_3492_ = l_main___elam__0___redArg(v___x_3482_, v___x_2974_, v_ext_3491_, v_a_3489_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
lean_inc(v_a_3493_);
lean_dec_ref_known(v___x_3492_, 1);
v___x_3494_ = l_Lean_classExtension;
v___x_3495_ = l_main___elam__0___redArg(v___x_3482_, v___x_2976_, v___x_3494_, v_a_3493_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3496_);
lean_dec_ref_known(v___x_3495_, 1);
v___x_3497_ = l_Lean_Meta_Match_Extension_extension;
v___x_3498_ = l_main___elam__0___redArg(v___x_3482_, v___x_2977_, v___x_3497_, v_a_3496_);
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_object* v_a_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3526_; 
v_a_3499_ = lean_ctor_get(v___x_3498_, 0);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3501_ = v___x_3498_;
v_isShared_3502_ = v_isSharedCheck_3526_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_a_3499_);
lean_dec(v___x_3498_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3526_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v___x_3503_; 
v___x_3503_ = l_Lean_Environment_getModuleIdx_x3f(v_a_3499_, v_name_2958_);
if (lean_obj_tag(v___x_3503_) == 1)
{
lean_object* v_val_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; uint8_t v___x_3509_; 
lean_del_object(v___x_3501_);
v_val_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_val_3504_);
lean_dec_ref_known(v___x_3503_, 1);
v___x_3505_ = l_Lean_Compiler_LCNF_impureSigExt;
v___x_3506_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2978_, v___x_3505_, v_a_3499_, v_val_3504_, v___x_3313_);
v___x_3507_ = lean_array_get_size(v___x_3506_);
v___x_3508_ = ((lean_object*)(l_main___closed__34));
v___x_3509_ = lean_nat_dec_lt(v___x_2987_, v___x_3507_);
if (v___x_3509_ == 0)
{
lean_dec_ref(v___x_3506_);
v___y_3457_ = v___x_3482_;
v___y_3458_ = v_val_3504_;
v___y_3459_ = v_a_3499_;
v___y_3460_ = v___x_3482_;
v___y_3461_ = v___x_3508_;
goto v___jp_3456_;
}
else
{
uint8_t v___x_3510_; 
v___x_3510_ = lean_nat_dec_le(v___x_3507_, v___x_3507_);
if (v___x_3510_ == 0)
{
if (v___x_3509_ == 0)
{
lean_dec_ref(v___x_3506_);
v___y_3457_ = v___x_3482_;
v___y_3458_ = v_val_3504_;
v___y_3459_ = v_a_3499_;
v___y_3460_ = v___x_3482_;
v___y_3461_ = v___x_3508_;
goto v___jp_3456_;
}
else
{
size_t v___x_3511_; size_t v___x_3512_; lean_object* v___x_3513_; 
v___x_3511_ = ((size_t)0ULL);
v___x_3512_ = lean_usize_of_nat(v___x_3507_);
lean_inc(v_a_3499_);
v___x_3513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_3499_, v___x_3506_, v___x_3511_, v___x_3512_, v___x_3508_);
lean_dec_ref(v___x_3506_);
v___y_3457_ = v___x_3482_;
v___y_3458_ = v_val_3504_;
v___y_3459_ = v_a_3499_;
v___y_3460_ = v___x_3482_;
v___y_3461_ = v___x_3513_;
goto v___jp_3456_;
}
}
else
{
size_t v___x_3514_; size_t v___x_3515_; lean_object* v___x_3516_; 
v___x_3514_ = ((size_t)0ULL);
v___x_3515_ = lean_usize_of_nat(v___x_3507_);
lean_inc(v_a_3499_);
v___x_3516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_3499_, v___x_3506_, v___x_3514_, v___x_3515_, v___x_3508_);
lean_dec_ref(v___x_3506_);
v___y_3457_ = v___x_3482_;
v___y_3458_ = v_val_3504_;
v___y_3459_ = v_a_3499_;
v___y_3460_ = v___x_3482_;
v___y_3461_ = v___x_3516_;
goto v___jp_3456_;
}
}
}
else
{
lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3524_; 
lean_dec(v___x_3503_);
lean_dec(v_a_3499_);
lean_dec_ref(v___x_2988_);
lean_del_object(v___x_2972_);
lean_dec(v_fst_2969_);
lean_dec(v_head_2951_);
lean_del_object(v___x_2949_);
lean_dec(v_head_2947_);
lean_del_object(v___x_2945_);
v___x_3517_ = ((lean_object*)(l_main___closed__35));
v___x_3518_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2958_, v___x_2984_);
v___x_3519_ = lean_string_append(v___x_3517_, v___x_3518_);
lean_dec_ref(v___x_3518_);
v___x_3520_ = ((lean_object*)(l_main___closed__36));
v___x_3521_ = lean_string_append(v___x_3519_, v___x_3520_);
v___x_3522_ = lean_mk_io_user_error(v___x_3521_);
if (v_isShared_3502_ == 0)
{
lean_ctor_set_tag(v___x_3501_, 1);
lean_ctor_set(v___x_3501_, 0, v___x_3522_);
v___x_3524_ = v___x_3501_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v___x_3522_);
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
lean_dec_ref(v___x_2988_);
lean_del_object(v___x_2972_);
lean_dec(v_fst_2969_);
lean_dec(v_name_2958_);
lean_dec(v_head_2951_);
lean_del_object(v___x_2949_);
lean_dec(v_head_2947_);
lean_del_object(v___x_2945_);
v_a_3527_ = lean_ctor_get(v___x_3498_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3529_ = v___x_3498_;
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_a_3527_);
lean_dec(v___x_3498_);
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
lean_dec_ref(v___x_2988_);
lean_del_object(v___x_2972_);
lean_dec(v_fst_2969_);
lean_dec(v_name_2958_);
lean_dec(v_head_2951_);
lean_del_object(v___x_2949_);
lean_dec(v_head_2947_);
lean_del_object(v___x_2945_);
v_a_3535_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3537_ = v___x_3495_;
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_a_3535_);
lean_dec(v___x_3495_);
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
lean_dec_ref(v___x_2988_);
lean_del_object(v___x_2972_);
lean_dec(v_fst_2969_);
lean_dec(v_name_2958_);
lean_dec(v_head_2951_);
lean_del_object(v___x_2949_);
lean_dec(v_head_2947_);
lean_del_object(v___x_2945_);
v_a_3543_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3545_ = v___x_3492_;
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_a_3543_);
lean_dec(v___x_3492_);
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
else
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3558_; 
lean_dec_ref(v___x_2988_);
lean_del_object(v___x_2972_);
lean_dec(v_fst_2969_);
lean_dec(v_name_2958_);
lean_dec(v_head_2951_);
lean_del_object(v___x_2949_);
lean_dec(v_head_2947_);
lean_del_object(v___x_2945_);
v_a_3551_ = lean_ctor_get(v___x_3488_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3553_ = v___x_3488_;
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___x_3488_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3556_; 
if (v_isShared_3554_ == 0)
{
v___x_3556_ = v___x_3553_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_a_3551_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
}
else
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3566_; 
lean_dec_ref(v___x_2988_);
lean_del_object(v___x_2972_);
lean_dec(v_fst_2969_);
lean_dec(v_name_2958_);
lean_dec(v_head_2951_);
lean_del_object(v___x_2949_);
lean_dec(v_head_2947_);
lean_del_object(v___x_2945_);
v_a_3559_ = lean_ctor_get(v___x_3483_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3483_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3561_ = v___x_3483_;
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3483_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3564_; 
if (v_isShared_3562_ == 0)
{
v___x_3564_ = v___x_3561_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_a_3559_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
}
}
}
}
else
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
lean_dec(v_a_2967_);
lean_dec(v_importArts_2959_);
lean_dec(v_name_2958_);
lean_dec(v_head_2951_);
lean_del_object(v___x_2949_);
lean_dec(v_head_2947_);
lean_del_object(v___x_2945_);
v_a_3569_ = lean_ctor_get(v___x_2968_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_2968_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_2968_);
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
else
{
lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3584_; 
lean_dec(v_importArts_2959_);
lean_dec(v_name_2958_);
lean_dec(v_head_2951_);
lean_del_object(v___x_2949_);
lean_dec(v_head_2947_);
lean_del_object(v___x_2945_);
v_a_3577_ = lean_ctor_get(v___x_2966_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3579_ = v___x_2966_;
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_2966_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3582_; 
if (v_isShared_3580_ == 0)
{
v___x_3582_ = v___x_3579_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_a_3577_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
}
}
}
else
{
lean_object* v_a_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3593_; 
lean_del_object(v___x_2954_);
lean_dec(v_tail_2952_);
lean_dec(v_head_2951_);
lean_del_object(v___x_2949_);
lean_dec(v_head_2947_);
lean_del_object(v___x_2945_);
v_a_3586_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3588_ = v___x_2956_;
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_a_3586_);
lean_dec(v___x_2956_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v___x_3591_; 
if (v_isShared_3589_ == 0)
{
v___x_3591_ = v___x_3588_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v_a_3586_);
v___x_3591_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
return v___x_3591_;
}
}
}
}
}
}
}
else
{
lean_dec(v_tail_2942_);
lean_dec_ref_known(v_tail_2941_, 2);
lean_dec_ref_known(v_args_2916_, 2);
goto v___jp_2918_;
}
}
else
{
lean_dec_ref_known(v_args_2916_, 2);
lean_dec(v_tail_2941_);
goto v___jp_2918_;
}
}
else
{
lean_dec(v_args_2916_);
goto v___jp_2918_;
}
v___jp_2918_:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2919_ = ((lean_object*)(l_main___closed__0));
v___x_2920_ = l_IO_println___at___00Lean_Environment_displayStats_spec__1(v___x_2919_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2928_; 
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_2928_ == 0)
{
lean_object* v_unused_2929_; 
v_unused_2929_ = lean_ctor_get(v___x_2920_, 0);
lean_dec(v_unused_2929_);
v___x_2922_ = v___x_2920_;
v_isShared_2923_ = v_isSharedCheck_2928_;
goto v_resetjp_2921_;
}
else
{
lean_dec(v___x_2920_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2928_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2924_; lean_object* v___x_2926_; 
v___x_2924_ = l_main___boxed__const__1;
if (v_isShared_2923_ == 0)
{
lean_ctor_set(v___x_2922_, 0, v___x_2924_);
v___x_2926_ = v___x_2922_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v___x_2924_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
else
{
lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2937_; 
v_a_2930_ = lean_ctor_get(v___x_2920_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2932_ = v___x_2920_;
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2920_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2935_; 
if (v_isShared_2933_ == 0)
{
v___x_2935_ = v___x_2932_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2930_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
}
v___jp_2938_:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2939_ = l_main___boxed__const__2;
v___x_2940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2939_);
return v___x_2940_;
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_3599_, lean_object* v_a_3600_){
_start:
{
lean_object* v_res_3601_; 
v_res_3601_ = _lean_main(v_args_3599_);
return v_res_3601_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1(lean_object* v_as_3602_, lean_object* v_as_x27_3603_, lean_object* v_b_3604_, lean_object* v_a_3605_){
_start:
{
lean_object* v___x_3607_; 
v___x_3607_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_3603_, v_b_3604_);
return v___x_3607_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___boxed(lean_object* v_as_3608_, lean_object* v_as_x27_3609_, lean_object* v_b_3610_, lean_object* v_a_3611_, lean_object* v___y_3612_){
_start:
{
lean_object* v_res_3613_; 
v_res_3613_ = l_List_forIn_x27_loop___at___00main_spec__1(v_as_3608_, v_as_x27_3609_, v_b_3610_, v_a_3611_);
lean_dec(v_as_x27_3609_);
lean_dec(v_as_3608_);
return v_res_3613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16(lean_object* v___y_3614_, lean_object* v___y_3615_){
_start:
{
lean_object* v___x_3617_; 
v___x_3617_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_3615_);
return v___x_3617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___boxed(lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_){
_start:
{
lean_object* v_res_3621_; 
v_res_3621_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16(v___y_3618_, v___y_3619_);
lean_dec(v___y_3619_);
lean_dec_ref(v___y_3618_);
return v_res_3621_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17(lean_object* v_00_u03b2_3622_, lean_object* v_m_3623_, lean_object* v_a_3624_, lean_object* v_fallback_3625_){
_start:
{
lean_object* v___x_3626_; 
v___x_3626_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_m_3623_, v_a_3624_, v_fallback_3625_);
return v___x_3626_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___boxed(lean_object* v_00_u03b2_3627_, lean_object* v_m_3628_, lean_object* v_a_3629_, lean_object* v_fallback_3630_){
_start:
{
lean_object* v_res_3631_; 
v_res_3631_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17(v_00_u03b2_3627_, v_m_3628_, v_a_3629_, v_fallback_3630_);
lean_dec(v_fallback_3630_);
lean_dec_ref(v_a_3629_);
lean_dec_ref(v_m_3628_);
return v_res_3631_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18(lean_object* v_00_u03b2_3632_, lean_object* v_m_3633_, lean_object* v_a_3634_, lean_object* v_b_3635_){
_start:
{
lean_object* v___x_3636_; 
v___x_3636_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_m_3633_, v_a_3634_, v_b_3635_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21(lean_object* v_n_3637_, lean_object* v_as_3638_, lean_object* v_lo_3639_, lean_object* v_hi_3640_, lean_object* v_w_3641_, lean_object* v_hlo_3642_, lean_object* v_hhi_3643_){
_start:
{
lean_object* v___x_3644_; 
v___x_3644_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_3637_, v_as_3638_, v_lo_3639_, v_hi_3640_);
return v___x_3644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___boxed(lean_object* v_n_3645_, lean_object* v_as_3646_, lean_object* v_lo_3647_, lean_object* v_hi_3648_, lean_object* v_w_3649_, lean_object* v_hlo_3650_, lean_object* v_hhi_3651_){
_start:
{
lean_object* v_res_3652_; 
v_res_3652_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21(v_n_3645_, v_as_3646_, v_lo_3647_, v_hi_3648_, v_w_3649_, v_hlo_3650_, v_hhi_3651_);
lean_dec(v_hi_3648_);
lean_dec(v_n_3645_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21(lean_object* v_00_u03b2_3653_, lean_object* v_a_3654_, lean_object* v_fallback_3655_, lean_object* v_x_3656_){
_start:
{
lean_object* v___x_3657_; 
v___x_3657_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_3654_, v_fallback_3655_, v_x_3656_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___boxed(lean_object* v_00_u03b2_3658_, lean_object* v_a_3659_, lean_object* v_fallback_3660_, lean_object* v_x_3661_){
_start:
{
lean_object* v_res_3662_; 
v_res_3662_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21(v_00_u03b2_3658_, v_a_3659_, v_fallback_3660_, v_x_3661_);
lean_dec(v_x_3661_);
lean_dec(v_fallback_3660_);
lean_dec_ref(v_a_3659_);
return v_res_3662_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23(lean_object* v_00_u03b2_3663_, lean_object* v_a_3664_, lean_object* v_x_3665_){
_start:
{
uint8_t v___x_3666_; 
v___x_3666_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_3664_, v_x_3665_);
return v___x_3666_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___boxed(lean_object* v_00_u03b2_3667_, lean_object* v_a_3668_, lean_object* v_x_3669_){
_start:
{
uint8_t v_res_3670_; lean_object* v_r_3671_; 
v_res_3670_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23(v_00_u03b2_3667_, v_a_3668_, v_x_3669_);
lean_dec(v_x_3669_);
lean_dec_ref(v_a_3668_);
v_r_3671_ = lean_box(v_res_3670_);
return v_r_3671_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24(lean_object* v_00_u03b2_3672_, lean_object* v_data_3673_){
_start:
{
lean_object* v___x_3674_; 
v___x_3674_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(v_data_3673_);
return v___x_3674_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25(lean_object* v_00_u03b2_3675_, lean_object* v_a_3676_, lean_object* v_b_3677_, lean_object* v_x_3678_){
_start:
{
lean_object* v___x_3679_; 
v___x_3679_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_3676_, v_b_3677_, v_x_3678_);
return v___x_3679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31(lean_object* v_n_3680_, lean_object* v_lo_3681_, lean_object* v_hi_3682_, lean_object* v_hhi_3683_, lean_object* v_pivot_3684_, lean_object* v_as_3685_, lean_object* v_i_3686_, lean_object* v_k_3687_, lean_object* v_ilo_3688_, lean_object* v_ik_3689_, lean_object* v_w_3690_){
_start:
{
lean_object* v___x_3691_; 
v___x_3691_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_3682_, v_pivot_3684_, v_as_3685_, v_i_3686_, v_k_3687_);
return v___x_3691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___boxed(lean_object* v_n_3692_, lean_object* v_lo_3693_, lean_object* v_hi_3694_, lean_object* v_hhi_3695_, lean_object* v_pivot_3696_, lean_object* v_as_3697_, lean_object* v_i_3698_, lean_object* v_k_3699_, lean_object* v_ilo_3700_, lean_object* v_ik_3701_, lean_object* v_w_3702_){
_start:
{
lean_object* v_res_3703_; 
v_res_3703_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31(v_n_3692_, v_lo_3693_, v_hi_3694_, v_hhi_3695_, v_pivot_3696_, v_as_3697_, v_i_3698_, v_k_3699_, v_ilo_3700_, v_ik_3701_, v_w_3702_);
lean_dec_ref(v_pivot_3696_);
lean_dec(v_hi_3694_);
lean_dec(v_lo_3693_);
lean_dec(v_n_3692_);
return v_res_3703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40(lean_object* v_as_3704_, size_t v_sz_3705_, size_t v_i_3706_, lean_object* v_b_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_){
_start:
{
lean_object* v___x_3711_; 
v___x_3711_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_3704_, v_sz_3705_, v_i_3706_, v_b_3707_, v___y_3708_);
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___boxed(lean_object* v_as_3712_, lean_object* v_sz_3713_, lean_object* v_i_3714_, lean_object* v_b_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_){
_start:
{
size_t v_sz_boxed_3719_; size_t v_i_boxed_3720_; lean_object* v_res_3721_; 
v_sz_boxed_3719_ = lean_unbox_usize(v_sz_3713_);
lean_dec(v_sz_3713_);
v_i_boxed_3720_ = lean_unbox_usize(v_i_3714_);
lean_dec(v_i_3714_);
v_res_3721_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40(v_as_3712_, v_sz_boxed_3719_, v_i_boxed_3720_, v_b_3715_, v___y_3716_, v___y_3717_);
lean_dec(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec_ref(v_as_3712_);
return v_res_3721_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35(lean_object* v_00_u03b2_3722_, lean_object* v_i_3723_, lean_object* v_source_3724_, lean_object* v_target_3725_){
_start:
{
lean_object* v___x_3726_; 
v___x_3726_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(v_i_3723_, v_source_3724_, v_target_3725_);
return v___x_3726_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42(uint8_t v___x_3727_, lean_object* v_as_3728_, size_t v_sz_3729_, size_t v_i_3730_, lean_object* v_b_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_){
_start:
{
lean_object* v___x_3735_; 
v___x_3735_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_3727_, v_as_3728_, v_sz_3729_, v_i_3730_, v_b_3731_, v___y_3732_);
return v___x_3735_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___boxed(lean_object* v___x_3736_, lean_object* v_as_3737_, lean_object* v_sz_3738_, lean_object* v_i_3739_, lean_object* v_b_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_){
_start:
{
uint8_t v___x_40450__boxed_3744_; size_t v_sz_boxed_3745_; size_t v_i_boxed_3746_; lean_object* v_res_3747_; 
v___x_40450__boxed_3744_ = lean_unbox(v___x_3736_);
v_sz_boxed_3745_ = lean_unbox_usize(v_sz_3738_);
lean_dec(v_sz_3738_);
v_i_boxed_3746_ = lean_unbox_usize(v_i_3739_);
lean_dec(v_i_3739_);
v_res_3747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42(v___x_40450__boxed_3744_, v_as_3737_, v_sz_boxed_3745_, v_i_boxed_3746_, v_b_3740_, v___y_3741_, v___y_3742_);
lean_dec(v___y_3742_);
lean_dec_ref(v___y_3741_);
lean_dec_ref(v_as_3737_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51(lean_object* v_as_3748_, size_t v_sz_3749_, size_t v_i_3750_, lean_object* v_b_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_){
_start:
{
lean_object* v___x_3755_; 
v___x_3755_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_3748_, v_sz_3749_, v_i_3750_, v_b_3751_, v___y_3752_);
return v___x_3755_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___boxed(lean_object* v_as_3756_, lean_object* v_sz_3757_, lean_object* v_i_3758_, lean_object* v_b_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_){
_start:
{
size_t v_sz_boxed_3763_; size_t v_i_boxed_3764_; lean_object* v_res_3765_; 
v_sz_boxed_3763_ = lean_unbox_usize(v_sz_3757_);
lean_dec(v_sz_3757_);
v_i_boxed_3764_ = lean_unbox_usize(v_i_3758_);
lean_dec(v_i_3758_);
v_res_3765_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51(v_as_3756_, v_sz_boxed_3763_, v_i_boxed_3764_, v_b_3759_, v___y_3760_, v___y_3761_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
lean_dec_ref(v_as_3756_);
return v_res_3765_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44(lean_object* v_00_u03b2_3766_, lean_object* v_x_3767_, lean_object* v_x_3768_){
_start:
{
lean_object* v___x_3769_; 
v___x_3769_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(v_x_3767_, v_x_3768_);
return v___x_3769_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49(uint8_t v___x_3770_, lean_object* v_as_3771_, size_t v_sz_3772_, size_t v_i_3773_, lean_object* v_b_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_){
_start:
{
lean_object* v___x_3778_; 
v___x_3778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_3770_, v_as_3771_, v_sz_3772_, v_i_3773_, v_b_3774_, v___y_3775_);
return v___x_3778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___boxed(lean_object* v___x_3779_, lean_object* v_as_3780_, lean_object* v_sz_3781_, lean_object* v_i_3782_, lean_object* v_b_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_){
_start:
{
uint8_t v___x_40481__boxed_3787_; size_t v_sz_boxed_3788_; size_t v_i_boxed_3789_; lean_object* v_res_3790_; 
v___x_40481__boxed_3787_ = lean_unbox(v___x_3779_);
v_sz_boxed_3788_ = lean_unbox_usize(v_sz_3781_);
lean_dec(v_sz_3781_);
v_i_boxed_3789_ = lean_unbox_usize(v_i_3782_);
lean_dec(v_i_3782_);
v_res_3790_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49(v___x_40481__boxed_3787_, v_as_3780_, v_sz_boxed_3788_, v_i_boxed_3789_, v_b_3783_, v___y_3784_, v___y_3785_);
lean_dec(v___y_3785_);
lean_dec_ref(v___y_3784_);
lean_dec_ref(v_as_3780_);
return v_res_3790_;
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
