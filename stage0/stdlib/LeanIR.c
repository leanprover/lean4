// Lean compiler output
// Module: LeanIR
// Imports: public import Init public meta import Init import Lean.CoreM import Lean.Util.ForEachExpr import all Lean.Util.Path import all Lean.Environment import Lean.Compiler.Options import Lean.Compiler.IR.CompilerM import Lean.Compiler.ModPkgExt import all Lean.Compiler.CSimpAttr import Lean.Compiler.LCNF.EmitC import Lean.Language.Lean import Lean.Compiler.LCNF.PhaseExt import Lean.Compiler.LCNF.Main
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
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_Compiler_LCNF_resumeCompilation(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_output;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_serve;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint64_t l_String_instHashableRaw_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* l_String_Slice_toName(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecls();
lean_object* l_Lean_Language_Lean_setOption(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_ir_export_entries(lean_object*);
lean_object* l_Lean_mkModuleData(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_get_ir_extra_const_names(lean_object*, uint8_t, uint8_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
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
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_io_get_num_heartbeats();
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Compiler_LCNF_emitC(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_io_prim_handle_write(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_display_cumulative_profiling_times();
lean_object* l_Lean_Environment_displayStats(lean_object*);
lean_object* l_Lean_Core_getAndEmptyMessageLog___redArg(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
extern lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
lean_object* l_Lean_PersistentEnvExtension_setState___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__8___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_main___lam__1(lean_object*, lean_object*, uint16_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_main___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "--stat"};
static const lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_boxed"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__12(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__23(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0(uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35_spec__44___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__39(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__39___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0;
static lean_once_cell_t l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1;
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__37(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_main___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l_main___closed__14;
static const lean_string_object l_main___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "failed to create '"};
static const lean_object* l_main___closed__15 = (const lean_object*)&l_main___closed__15_value;
static const lean_string_object l_main___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "LeanIR"};
static const lean_object* l_main___closed__16 = (const lean_object*)&l_main___closed__16_value;
static const lean_string_object l_main___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "main"};
static const lean_object* l_main___closed__17 = (const lean_object*)&l_main___closed__17_value;
static const lean_string_object l_main___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_main___closed__18 = (const lean_object*)&l_main___closed__18_value;
static lean_once_cell_t l_main___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__19;
static const lean_string_object l_main___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "import"};
static const lean_object* l_main___closed__20 = (const lean_object*)&l_main___closed__20_value;
static lean_once_cell_t l_main___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__21;
static lean_once_cell_t l_main___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__22;
static const lean_string_object l_main___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l_main___closed__23 = (const lean_object*)&l_main___closed__23_value;
static const lean_ctor_object l_main___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__23_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l_main___closed__24 = (const lean_object*)&l_main___closed__24_value;
static const lean_ctor_object l_main___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_main___closed__24_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_main___closed__25 = (const lean_object*)&l_main___closed__25_value;
static lean_once_cell_t l_main___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__26;
static lean_once_cell_t l_main___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__27;
static lean_once_cell_t l_main___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__28;
static lean_once_cell_t l_main___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__29;
static const lean_array_object l_main___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_main___closed__30 = (const lean_object*)&l_main___closed__30_value;
static lean_once_cell_t l_main___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__31;
static lean_once_cell_t l_main___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__32;
static const lean_array_object l_main___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_main___closed__33 = (const lean_object*)&l_main___closed__33_value;
static const lean_string_object l_main___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "module '"};
static const lean_object* l_main___closed__34 = (const lean_object*)&l_main___closed__34_value;
static const lean_string_object l_main___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "' not found"};
static const lean_object* l_main___closed__35 = (const lean_object*)&l_main___closed__35_value;
static lean_once_cell_t l_main___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_main___closed__36;
LEAN_EXPORT lean_object* l_main___boxed__const__1;
LEAN_EXPORT lean_object* l_main___boxed__const__2;
LEAN_EXPORT lean_object* _lean_main(lean_object*);
LEAN_EXPORT lean_object* l_main___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35_spec__44(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_359_; lean_object* v___x_18888__overap_360_; lean_object* v___x_361_; 
v___x_359_ = lean_obj_once(&l_panic___at___00main_spec__5___closed__0, &l_panic___at___00main_spec__5___closed__0_once, _init_l_panic___at___00main_spec__5___closed__0);
v___x_18888__overap_360_ = lean_panic_fn_borrowed(v___x_359_, v_msg_357_);
v___x_361_ = lean_apply_1(v___x_18888__overap_360_, lean_box(0));
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__8(lean_object* v_opts_365_, lean_object* v_opt_366_){
_start:
{
lean_object* v_name_367_; lean_object* v_defValue_368_; lean_object* v_map_369_; lean_object* v___x_370_; 
v_name_367_ = lean_ctor_get(v_opt_366_, 0);
v_defValue_368_ = lean_ctor_get(v_opt_366_, 1);
v_map_369_ = lean_ctor_get(v_opts_365_, 0);
v___x_370_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_369_, v_name_367_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_inc(v_defValue_368_);
return v_defValue_368_;
}
else
{
lean_object* v_val_371_; 
v_val_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_val_371_);
lean_dec_ref_known(v___x_370_, 1);
if (lean_obj_tag(v_val_371_) == 3)
{
lean_object* v_v_372_; 
v_v_372_ = lean_ctor_get(v_val_371_, 0);
lean_inc(v_v_372_);
lean_dec_ref_known(v_val_371_, 1);
return v_v_372_;
}
else
{
lean_dec(v_val_371_);
lean_inc(v_defValue_368_);
return v_defValue_368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__8___boxed(lean_object* v_opts_373_, lean_object* v_opt_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Lean_Option_get___at___00main_spec__8(v_opts_373_, v_opt_374_);
lean_dec_ref(v_opt_374_);
lean_dec_ref(v_opts_373_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(lean_object* v_a_376_, lean_object* v_x_377_){
_start:
{
if (lean_obj_tag(v_x_377_) == 0)
{
lean_dec(v_a_376_);
return v_x_377_;
}
else
{
lean_object* v_key_378_; lean_object* v_value_379_; lean_object* v_tail_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_413_; 
v_key_378_ = lean_ctor_get(v_x_377_, 0);
v_value_379_ = lean_ctor_get(v_x_377_, 1);
v_tail_380_ = lean_ctor_get(v_x_377_, 2);
v_isSharedCheck_413_ = !lean_is_exclusive(v_x_377_);
if (v_isSharedCheck_413_ == 0)
{
v___x_382_ = v_x_377_;
v_isShared_383_ = v_isSharedCheck_413_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_tail_380_);
lean_inc(v_value_379_);
lean_inc(v_key_378_);
lean_dec(v_x_377_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_413_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
uint8_t v___x_384_; 
v___x_384_ = lean_name_eq(v_key_378_, v_a_376_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_385_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(v_a_376_, v_tail_380_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 2, v___x_385_);
v___x_387_ = v___x_382_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_key_378_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v_value_379_);
lean_ctor_set(v_reuseFailAlloc_388_, 2, v___x_385_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
else
{
lean_object* v_toEffectiveImport_389_; lean_object* v_parts_390_; lean_object* v_irParts_391_; uint8_t v_needsIRTrans_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_412_; 
lean_dec(v_key_378_);
v_toEffectiveImport_389_ = lean_ctor_get(v_value_379_, 0);
v_parts_390_ = lean_ctor_get(v_value_379_, 1);
v_irParts_391_ = lean_ctor_get(v_value_379_, 2);
v_needsIRTrans_392_ = lean_ctor_get_uint8(v_value_379_, sizeof(void*)*3);
v_isSharedCheck_412_ = !lean_is_exclusive(v_value_379_);
if (v_isSharedCheck_412_ == 0)
{
v___x_394_ = v_value_379_;
v_isShared_395_ = v_isSharedCheck_412_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_irParts_391_);
lean_inc(v_parts_390_);
lean_inc(v_toEffectiveImport_389_);
lean_dec(v_value_379_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_412_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v_toImport_396_; uint8_t v_hasData_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_411_; 
v_toImport_396_ = lean_ctor_get(v_toEffectiveImport_389_, 0);
v_hasData_397_ = lean_ctor_get_uint8(v_toEffectiveImport_389_, sizeof(void*)*1 + 1);
v_isSharedCheck_411_ = !lean_is_exclusive(v_toEffectiveImport_389_);
if (v_isSharedCheck_411_ == 0)
{
v___x_399_ = v_toEffectiveImport_389_;
v_isShared_400_ = v_isSharedCheck_411_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_toImport_396_);
lean_dec(v_toEffectiveImport_389_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_411_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
uint8_t v___x_401_; lean_object* v___x_403_; 
v___x_401_ = 0;
if (v_isShared_400_ == 0)
{
v___x_403_ = v___x_399_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_toImport_396_);
lean_ctor_set_uint8(v_reuseFailAlloc_410_, sizeof(void*)*1 + 1, v_hasData_397_);
v___x_403_ = v_reuseFailAlloc_410_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_405_; 
lean_ctor_set_uint8(v___x_403_, sizeof(void*)*1, v___x_401_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v___x_403_);
v___x_405_ = v___x_394_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_403_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v_parts_390_);
lean_ctor_set(v_reuseFailAlloc_409_, 2, v_irParts_391_);
lean_ctor_set_uint8(v_reuseFailAlloc_409_, sizeof(void*)*3, v_needsIRTrans_392_);
v___x_405_ = v_reuseFailAlloc_409_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_407_; 
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 1, v___x_405_);
lean_ctor_set(v___x_382_, 0, v_a_376_);
v___x_407_ = v___x_382_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_376_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v___x_405_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v_tail_380_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(lean_object* v_m_414_, lean_object* v_a_415_){
_start:
{
lean_object* v_size_416_; lean_object* v_buckets_417_; lean_object* v___x_418_; uint64_t v___y_420_; 
v_size_416_ = lean_ctor_get(v_m_414_, 0);
v_buckets_417_ = lean_ctor_get(v_m_414_, 1);
v___x_418_ = lean_array_get_size(v_buckets_417_);
if (lean_obj_tag(v_a_415_) == 0)
{
uint64_t v___x_447_; 
v___x_447_ = 1723ULL;
v___y_420_ = v___x_447_;
goto v___jp_419_;
}
else
{
uint64_t v_hash_448_; 
v_hash_448_ = lean_ctor_get_uint64(v_a_415_, sizeof(void*)*2);
v___y_420_ = v_hash_448_;
goto v___jp_419_;
}
v___jp_419_:
{
uint64_t v___x_421_; uint64_t v___x_422_; uint64_t v_fold_423_; uint64_t v___x_424_; uint64_t v___x_425_; uint64_t v___x_426_; size_t v___x_427_; size_t v___x_428_; size_t v___x_429_; size_t v___x_430_; size_t v___x_431_; lean_object* v_bucket_432_; uint8_t v___x_433_; 
v___x_421_ = 32ULL;
v___x_422_ = lean_uint64_shift_right(v___y_420_, v___x_421_);
v_fold_423_ = lean_uint64_xor(v___y_420_, v___x_422_);
v___x_424_ = 16ULL;
v___x_425_ = lean_uint64_shift_right(v_fold_423_, v___x_424_);
v___x_426_ = lean_uint64_xor(v_fold_423_, v___x_425_);
v___x_427_ = lean_uint64_to_usize(v___x_426_);
v___x_428_ = lean_usize_of_nat(v___x_418_);
v___x_429_ = ((size_t)1ULL);
v___x_430_ = lean_usize_sub(v___x_428_, v___x_429_);
v___x_431_ = lean_usize_land(v___x_427_, v___x_430_);
v_bucket_432_ = lean_array_uget_borrowed(v_buckets_417_, v___x_431_);
v___x_433_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_a_415_, v_bucket_432_);
if (v___x_433_ == 0)
{
lean_dec(v_a_415_);
return v_m_414_;
}
else
{
lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_444_; 
lean_inc(v_bucket_432_);
lean_inc_ref(v_buckets_417_);
lean_inc(v_size_416_);
v_isSharedCheck_444_ = !lean_is_exclusive(v_m_414_);
if (v_isSharedCheck_444_ == 0)
{
lean_object* v_unused_445_; lean_object* v_unused_446_; 
v_unused_445_ = lean_ctor_get(v_m_414_, 1);
lean_dec(v_unused_445_);
v_unused_446_ = lean_ctor_get(v_m_414_, 0);
lean_dec(v_unused_446_);
v___x_435_ = v_m_414_;
v_isShared_436_ = v_isSharedCheck_444_;
goto v_resetjp_434_;
}
else
{
lean_dec(v_m_414_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_444_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_437_; lean_object* v_buckets_438_; lean_object* v_bucket_439_; lean_object* v___x_440_; lean_object* v___x_442_; 
v___x_437_ = lean_box(0);
v_buckets_438_ = lean_array_uset(v_buckets_417_, v___x_431_, v___x_437_);
v_bucket_439_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(v_a_415_, v_bucket_432_);
v___x_440_ = lean_array_uset(v_buckets_438_, v___x_431_, v_bucket_439_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 1, v___x_440_);
v___x_442_ = v___x_435_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_size_416_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v___x_440_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__0(lean_object* v___x_449_, lean_object* v___x_450_, uint8_t v___x_451_, lean_object* v_importArts_452_, uint8_t v___y_453_, uint8_t v___x_454_, lean_object* v_name_455_, uint8_t v___x_456_, lean_object* v___x_457_, uint8_t v___x_458_){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = lean_st_mk_ref(v___x_449_);
v___x_461_ = l_Lean_importModulesCore(v___x_450_, v___x_451_, v_importArts_452_, v___y_453_, v___x_454_, v___x_460_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v___x_462_; lean_object* v_moduleNameMap_463_; lean_object* v_moduleNames_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_478_; 
lean_dec_ref_known(v___x_461_, 1);
v___x_462_ = lean_st_ref_get(v___x_460_);
lean_dec(v___x_460_);
v_moduleNameMap_463_ = lean_ctor_get(v___x_462_, 0);
v_moduleNames_464_ = lean_ctor_get(v___x_462_, 1);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_478_ == 0)
{
v___x_466_ = v___x_462_;
v_isShared_467_ = v_isSharedCheck_478_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_moduleNames_464_);
lean_inc(v_moduleNameMap_463_);
lean_dec(v___x_462_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_478_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_468_; lean_object* v___x_470_; 
v___x_468_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(v_moduleNameMap_463_, v_name_455_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 0, v___x_468_);
v___x_470_ = v___x_466_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_468_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_moduleNames_464_);
v___x_470_ = v_reuseFailAlloc_477_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
uint32_t v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_471_ = 0;
v___x_472_ = l_Lean_OLeanLevel_ctorIdx(v___x_451_);
v___x_473_ = l_Lean_OLeanLevel_ctorIdx(v___x_456_);
v___x_474_ = lean_nat_dec_eq(v___x_472_, v___x_473_);
lean_dec(v___x_473_);
lean_dec(v___x_472_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; 
v___x_475_ = l_Lean_finalizeImport(v___x_470_, v___x_450_, v___x_457_, v___x_471_, v___x_454_, v___x_458_, v___x_451_, v___x_454_, v___x_454_);
lean_dec_ref(v___x_470_);
return v___x_475_;
}
else
{
lean_object* v___x_476_; 
v___x_476_ = l_Lean_finalizeImport(v___x_470_, v___x_450_, v___x_457_, v___x_471_, v___x_454_, v___x_458_, v___x_451_, v___x_458_, v___x_454_);
lean_dec_ref(v___x_470_);
return v___x_476_;
}
}
}
}
else
{
lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_486_; 
lean_dec(v___x_460_);
lean_dec_ref(v___x_457_);
lean_dec(v_name_455_);
lean_dec_ref(v___x_450_);
v_a_479_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_486_ == 0)
{
v___x_481_ = v___x_461_;
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_461_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_484_; 
if (v_isShared_482_ == 0)
{
v___x_484_ = v___x_481_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_a_479_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__0___boxed(lean_object* v___x_487_, lean_object* v___x_488_, lean_object* v___x_489_, lean_object* v_importArts_490_, lean_object* v___y_491_, lean_object* v___x_492_, lean_object* v_name_493_, lean_object* v___x_494_, lean_object* v___x_495_, lean_object* v___x_496_, lean_object* v___y_497_){
_start:
{
uint8_t v___x_35926__boxed_498_; uint8_t v___y_35927__boxed_499_; uint8_t v___x_35928__boxed_500_; uint8_t v___x_35929__boxed_501_; uint8_t v___x_35931__boxed_502_; lean_object* v_res_503_; 
v___x_35926__boxed_498_ = lean_unbox(v___x_489_);
v___y_35927__boxed_499_ = lean_unbox(v___y_491_);
v___x_35928__boxed_500_ = lean_unbox(v___x_492_);
v___x_35929__boxed_501_ = lean_unbox(v___x_494_);
v___x_35931__boxed_502_ = lean_unbox(v___x_496_);
v_res_503_ = l_main___lam__0(v___x_487_, v___x_488_, v___x_35926__boxed_498_, v_importArts_490_, v___y_35927__boxed_499_, v___x_35928__boxed_500_, v_name_493_, v___x_35929__boxed_501_, v___x_495_, v___x_35931__boxed_502_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_main___lam__1(lean_object* v___x_507_, lean_object* v___x_508_, uint16_t v___x_509_, lean_object* v_name_510_, lean_object* v_a_511_, uint8_t v___x_512_, lean_object* v___x_513_, lean_object* v_head_514_, lean_object* v___x_515_, lean_object* v___x_516_, lean_object* v___x_517_, lean_object* v___x_518_, lean_object* v___x_519_, lean_object* v___x_520_, lean_object* v___x_521_, lean_object* v___x_522_, uint8_t v___x_523_, uint8_t v___x_524_){
_start:
{
lean_object* v_a_527_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v_fileName_533_; lean_object* v_fileMap_534_; lean_object* v_currNamespace_535_; lean_object* v_openDecls_536_; lean_object* v_initHeartbeats_537_; lean_object* v_maxHeartbeats_538_; lean_object* v_quotContext_539_; lean_object* v_currMacroScope_540_; lean_object* v_cancelTk_x3f_541_; lean_object* v_inheritedTraceOptions_542_; lean_object* v_currRecDepth_543_; lean_object* v_ref_544_; uint8_t v_suppressElabErrors_545_; uint8_t v_isRecordingDeps_546_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; uint8_t v___y_582_; uint8_t v___y_604_; uint8_t v___y_605_; lean_object* v_env_606_; uint8_t v___x_607_; uint8_t v___y_609_; uint16_t v___x_610_; uint16_t v___x_611_; uint16_t v___x_612_; uint8_t v___x_613_; 
v___x_530_ = lean_io_get_num_heartbeats();
v___x_531_ = lean_st_mk_ref(v___x_507_);
v___x_578_ = l_Lean_inheritedTraceOptions;
v___x_579_ = lean_st_ref_get(v___x_578_);
v___x_580_ = lean_st_ref_get(v___x_531_);
v_env_606_ = lean_ctor_get(v___x_580_, 0);
lean_inc_ref(v_env_606_);
lean_dec(v___x_580_);
v___x_607_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_606_);
lean_dec_ref(v_env_606_);
v___x_610_ = 512;
v___x_611_ = lean_uint16_land(v___x_509_, v___x_610_);
v___x_612_ = 0;
v___x_613_ = lean_uint16_dec_eq(v___x_611_, v___x_612_);
if (v___x_613_ == 0)
{
v___y_609_ = v___x_512_;
goto v___jp_608_;
}
else
{
v___y_609_ = v___x_524_;
goto v___jp_608_;
}
v___jp_526_:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_mk_io_user_error(v_a_527_);
v___x_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
return v___x_529_;
}
v___jp_532_:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_547_ = l_Lean_maxRecDepth;
v___x_548_ = l_Lean_Option_get___at___00main_spec__8(v___x_508_, v___x_547_);
v___x_549_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_549_, 0, v_fileName_533_);
lean_ctor_set(v___x_549_, 1, v_fileMap_534_);
lean_ctor_set(v___x_549_, 2, v___x_508_);
lean_ctor_set(v___x_549_, 3, v___x_548_);
lean_ctor_set(v___x_549_, 4, v_currNamespace_535_);
lean_ctor_set(v___x_549_, 5, v_openDecls_536_);
lean_ctor_set(v___x_549_, 6, v_initHeartbeats_537_);
lean_ctor_set(v___x_549_, 7, v_maxHeartbeats_538_);
lean_ctor_set(v___x_549_, 8, v_quotContext_539_);
lean_ctor_set(v___x_549_, 9, v_currMacroScope_540_);
lean_ctor_set(v___x_549_, 10, v_cancelTk_x3f_541_);
lean_ctor_set(v___x_549_, 11, v_inheritedTraceOptions_542_);
v___x_550_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_550_, 0, v___x_549_);
lean_ctor_set(v___x_550_, 1, v_currRecDepth_543_);
lean_ctor_set(v___x_550_, 2, v_ref_544_);
lean_ctor_set_uint16(v___x_550_, sizeof(void*)*3, v___x_509_);
lean_ctor_set_uint8(v___x_550_, sizeof(void*)*3 + 2, v_suppressElabErrors_545_);
lean_ctor_set_uint8(v___x_550_, sizeof(void*)*3 + 3, v_isRecordingDeps_546_);
v___x_551_ = l_Lean_Compiler_LCNF_emitC(v_name_510_, v___x_550_, v___x_531_);
lean_dec_ref_known(v___x_550_, 3);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_a_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v_a_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_a_552_);
lean_dec_ref_known(v___x_551_, 1);
v___x_553_ = lean_st_ref_get(v___x_531_);
lean_dec(v___x_531_);
lean_dec(v___x_553_);
v___x_554_ = lean_string_to_utf8(v_a_552_);
lean_dec(v_a_552_);
v___x_555_ = lean_io_prim_handle_write(v_a_511_, v___x_554_);
lean_dec_ref(v___x_554_);
return v___x_555_;
}
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_577_; 
lean_dec(v___x_531_);
v_a_556_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_577_ == 0)
{
v___x_558_ = v___x_551_;
v_isShared_559_ = v_isSharedCheck_577_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_551_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_577_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
if (lean_obj_tag(v_a_556_) == 0)
{
lean_object* v_msg_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_564_; 
v_msg_560_ = lean_ctor_get(v_a_556_, 1);
lean_inc_ref(v_msg_560_);
lean_dec_ref_known(v_a_556_, 2);
v___x_561_ = l_Lean_MessageData_toString(v_msg_560_);
v___x_562_ = lean_mk_io_user_error(v___x_561_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v___x_562_);
v___x_564_ = v___x_558_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
else
{
lean_object* v_id_566_; lean_object* v___x_567_; 
lean_del_object(v___x_558_);
v_id_566_ = lean_ctor_get(v_a_556_, 0);
lean_inc(v_id_566_);
lean_dec_ref_known(v_a_556_, 2);
v___x_567_ = l_Lean_InternalExceptionId_getName(v_id_566_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
lean_dec(v_id_566_);
v_a_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_a_568_);
lean_dec_ref_known(v___x_567_, 1);
v___x_569_ = ((lean_object*)(l_main___lam__1___closed__0));
v___x_570_ = l_Lean_Name_toString(v_a_568_, v___x_512_);
v___x_571_ = lean_string_append(v___x_569_, v___x_570_);
lean_dec_ref(v___x_570_);
v_a_527_ = v___x_571_;
goto v___jp_526_;
}
else
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
lean_dec_ref_known(v___x_567_, 1);
v___x_572_ = ((lean_object*)(l_main___lam__1___closed__1));
v___x_573_ = l_Nat_reprFast(v_id_566_);
v___x_574_ = lean_string_append(v___x_572_, v___x_573_);
lean_dec_ref(v___x_573_);
v___x_575_ = ((lean_object*)(l_main___lam__1___closed__2));
v___x_576_ = lean_string_append(v___x_574_, v___x_575_);
v_a_527_ = v___x_576_;
goto v___jp_526_;
}
}
}
}
}
v___jp_581_:
{
lean_object* v___x_583_; lean_object* v_env_584_; lean_object* v_nextMacroScope_585_; lean_object* v_ngen_586_; lean_object* v_auxDeclNGen_587_; lean_object* v_traceState_588_; lean_object* v_recordedDeps_589_; lean_object* v_messages_590_; lean_object* v_infoState_591_; lean_object* v_snapshotTasks_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_601_; 
v___x_583_ = lean_st_ref_take(v___x_531_);
v_env_584_ = lean_ctor_get(v___x_583_, 0);
v_nextMacroScope_585_ = lean_ctor_get(v___x_583_, 1);
v_ngen_586_ = lean_ctor_get(v___x_583_, 2);
v_auxDeclNGen_587_ = lean_ctor_get(v___x_583_, 3);
v_traceState_588_ = lean_ctor_get(v___x_583_, 4);
v_recordedDeps_589_ = lean_ctor_get(v___x_583_, 6);
v_messages_590_ = lean_ctor_get(v___x_583_, 7);
v_infoState_591_ = lean_ctor_get(v___x_583_, 8);
v_snapshotTasks_592_ = lean_ctor_get(v___x_583_, 9);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_601_ == 0)
{
lean_object* v_unused_602_; 
v_unused_602_ = lean_ctor_get(v___x_583_, 5);
lean_dec(v_unused_602_);
v___x_594_ = v___x_583_;
v_isShared_595_ = v_isSharedCheck_601_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_snapshotTasks_592_);
lean_inc(v_infoState_591_);
lean_inc(v_messages_590_);
lean_inc(v_recordedDeps_589_);
lean_inc(v_traceState_588_);
lean_inc(v_auxDeclNGen_587_);
lean_inc(v_ngen_586_);
lean_inc(v_nextMacroScope_585_);
lean_inc(v_env_584_);
lean_dec(v___x_583_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_601_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; lean_object* v___x_598_; 
v___x_596_ = l_Lean_Kernel_enableDiag(v_env_584_, v___y_582_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 5, v___x_513_);
lean_ctor_set(v___x_594_, 0, v___x_596_);
v___x_598_ = v___x_594_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v_nextMacroScope_585_);
lean_ctor_set(v_reuseFailAlloc_600_, 2, v_ngen_586_);
lean_ctor_set(v_reuseFailAlloc_600_, 3, v_auxDeclNGen_587_);
lean_ctor_set(v_reuseFailAlloc_600_, 4, v_traceState_588_);
lean_ctor_set(v_reuseFailAlloc_600_, 5, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_600_, 6, v_recordedDeps_589_);
lean_ctor_set(v_reuseFailAlloc_600_, 7, v_messages_590_);
lean_ctor_set(v_reuseFailAlloc_600_, 8, v_infoState_591_);
lean_ctor_set(v_reuseFailAlloc_600_, 9, v_snapshotTasks_592_);
v___x_598_ = v_reuseFailAlloc_600_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v___x_599_; 
v___x_599_ = lean_st_ref_put(v___x_531_, v___x_598_);
lean_inc(v___x_516_);
v_fileName_533_ = v_head_514_;
v_fileMap_534_ = v___x_515_;
v_currNamespace_535_ = v___x_516_;
v_openDecls_536_ = v___x_517_;
v_initHeartbeats_537_ = v___x_530_;
v_maxHeartbeats_538_ = v___x_518_;
v_quotContext_539_ = v___x_516_;
v_currMacroScope_540_ = v___x_519_;
v_cancelTk_x3f_541_ = v___x_520_;
v_inheritedTraceOptions_542_ = v___x_579_;
v_currRecDepth_543_ = v___x_521_;
v_ref_544_ = v___x_522_;
v_suppressElabErrors_545_ = v___x_523_;
v_isRecordingDeps_546_ = v___x_523_;
goto v___jp_532_;
}
}
}
v___jp_603_:
{
if (v___y_605_ == 0)
{
v___y_582_ = v___y_604_;
goto v___jp_581_;
}
else
{
lean_dec_ref(v___x_513_);
lean_inc(v___x_516_);
v_fileName_533_ = v_head_514_;
v_fileMap_534_ = v___x_515_;
v_currNamespace_535_ = v___x_516_;
v_openDecls_536_ = v___x_517_;
v_initHeartbeats_537_ = v___x_530_;
v_maxHeartbeats_538_ = v___x_518_;
v_quotContext_539_ = v___x_516_;
v_currMacroScope_540_ = v___x_519_;
v_cancelTk_x3f_541_ = v___x_520_;
v_inheritedTraceOptions_542_ = v___x_579_;
v_currRecDepth_543_ = v___x_521_;
v_ref_544_ = v___x_522_;
v_suppressElabErrors_545_ = v___x_523_;
v_isRecordingDeps_546_ = v___x_523_;
goto v___jp_532_;
}
}
v___jp_608_:
{
if (v___y_609_ == 0)
{
if (v___x_607_ == 0)
{
v___y_604_ = v___y_609_;
v___y_605_ = v___x_512_;
goto v___jp_603_;
}
else
{
v___y_582_ = v___y_609_;
goto v___jp_581_;
}
}
else
{
v___y_604_ = v___y_609_;
v___y_605_ = v___x_607_;
goto v___jp_603_;
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__1___boxed(lean_object** _args){
lean_object* v___x_614_ = _args[0];
lean_object* v___x_615_ = _args[1];
lean_object* v___x_616_ = _args[2];
lean_object* v_name_617_ = _args[3];
lean_object* v_a_618_ = _args[4];
lean_object* v___x_619_ = _args[5];
lean_object* v___x_620_ = _args[6];
lean_object* v_head_621_ = _args[7];
lean_object* v___x_622_ = _args[8];
lean_object* v___x_623_ = _args[9];
lean_object* v___x_624_ = _args[10];
lean_object* v___x_625_ = _args[11];
lean_object* v___x_626_ = _args[12];
lean_object* v___x_627_ = _args[13];
lean_object* v___x_628_ = _args[14];
lean_object* v___x_629_ = _args[15];
lean_object* v___x_630_ = _args[16];
lean_object* v___x_631_ = _args[17];
lean_object* v___y_632_ = _args[18];
_start:
{
uint16_t v___x_36010__boxed_633_; uint8_t v___x_36012__boxed_634_; uint8_t v___x_36023__boxed_635_; uint8_t v___x_36024__boxed_636_; lean_object* v_res_637_; 
v___x_36010__boxed_633_ = lean_unbox(v___x_616_);
v___x_36012__boxed_634_ = lean_unbox(v___x_619_);
v___x_36023__boxed_635_ = lean_unbox(v___x_630_);
v___x_36024__boxed_636_ = lean_unbox(v___x_631_);
v_res_637_ = l_main___lam__1(v___x_614_, v___x_615_, v___x_36010__boxed_633_, v_name_617_, v_a_618_, v___x_36012__boxed_634_, v___x_620_, v_head_621_, v___x_622_, v___x_623_, v___x_624_, v___x_625_, v___x_626_, v___x_627_, v___x_628_, v___x_629_, v___x_36023__boxed_635_, v___x_36024__boxed_636_);
lean_dec(v_a_618_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(lean_object* v_x2_638_, lean_object* v_as_639_, size_t v_i_640_, size_t v_stop_641_, lean_object* v_b_642_){
_start:
{
uint8_t v___x_643_; 
v___x_643_ = lean_usize_dec_eq(v_i_640_, v_stop_641_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; lean_object* v___x_645_; size_t v___x_646_; size_t v___x_647_; 
v___x_644_ = lean_array_uget_borrowed(v_as_639_, v_i_640_);
lean_inc_ref(v_x2_638_);
lean_inc(v___x_644_);
v___x_645_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_644_, v_x2_638_, v_b_642_);
v___x_646_ = ((size_t)1ULL);
v___x_647_ = lean_usize_add(v_i_640_, v___x_646_);
v_i_640_ = v___x_647_;
v_b_642_ = v___x_645_;
goto _start;
}
else
{
lean_dec_ref(v_x2_638_);
return v_b_642_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2___boxed(lean_object* v_x2_649_, lean_object* v_as_650_, lean_object* v_i_651_, lean_object* v_stop_652_, lean_object* v_b_653_){
_start:
{
size_t v_i_boxed_654_; size_t v_stop_boxed_655_; lean_object* v_res_656_; 
v_i_boxed_654_ = lean_unbox_usize(v_i_651_);
lean_dec(v_i_651_);
v_stop_boxed_655_ = lean_unbox_usize(v_stop_652_);
lean_dec(v_stop_652_);
v_res_656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v_x2_649_, v_as_650_, v_i_boxed_654_, v_stop_boxed_655_, v_b_653_);
lean_dec_ref(v_as_650_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(lean_object* v_as_657_, size_t v_i_658_, size_t v_stop_659_, lean_object* v_b_660_){
_start:
{
lean_object* v___y_662_; uint8_t v___x_666_; 
v___x_666_ = lean_usize_dec_eq(v_i_658_, v_stop_659_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; lean_object* v_declNames_668_; lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
v___x_667_ = lean_array_uget_borrowed(v_as_657_, v_i_658_);
v_declNames_668_ = lean_ctor_get(v___x_667_, 0);
v___x_669_ = lean_unsigned_to_nat(0u);
v___x_670_ = lean_array_get_size(v_declNames_668_);
v___x_671_ = lean_nat_dec_lt(v___x_669_, v___x_670_);
if (v___x_671_ == 0)
{
v___y_662_ = v_b_660_;
goto v___jp_661_;
}
else
{
uint8_t v___x_672_; 
v___x_672_ = lean_nat_dec_le(v___x_670_, v___x_670_);
if (v___x_672_ == 0)
{
if (v___x_671_ == 0)
{
v___y_662_ = v_b_660_;
goto v___jp_661_;
}
else
{
size_t v___x_673_; size_t v___x_674_; lean_object* v___x_675_; 
v___x_673_ = ((size_t)0ULL);
v___x_674_ = lean_usize_of_nat(v___x_670_);
lean_inc(v___x_667_);
v___x_675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_667_, v_declNames_668_, v___x_673_, v___x_674_, v_b_660_);
v___y_662_ = v___x_675_;
goto v___jp_661_;
}
}
else
{
size_t v___x_676_; size_t v___x_677_; lean_object* v___x_678_; 
v___x_676_ = ((size_t)0ULL);
v___x_677_ = lean_usize_of_nat(v___x_670_);
lean_inc(v___x_667_);
v___x_678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_667_, v_declNames_668_, v___x_676_, v___x_677_, v_b_660_);
v___y_662_ = v___x_678_;
goto v___jp_661_;
}
}
}
else
{
return v_b_660_;
}
v___jp_661_:
{
size_t v___x_663_; size_t v___x_664_; 
v___x_663_ = ((size_t)1ULL);
v___x_664_ = lean_usize_add(v_i_658_, v___x_663_);
v_i_658_ = v___x_664_;
v_b_660_ = v___y_662_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14___boxed(lean_object* v_as_679_, lean_object* v_i_680_, lean_object* v_stop_681_, lean_object* v_b_682_){
_start:
{
size_t v_i_boxed_683_; size_t v_stop_boxed_684_; lean_object* v_res_685_; 
v_i_boxed_683_ = lean_unbox_usize(v_i_680_);
lean_dec(v_i_680_);
v_stop_boxed_684_ = lean_unbox_usize(v_stop_681_);
lean_dec(v_stop_681_);
v_res_685_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(v_as_679_, v_i_boxed_683_, v_stop_boxed_684_, v_b_682_);
lean_dec_ref(v_as_679_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(lean_object* v_s_686_){
_start:
{
lean_object* v___x_688_; lean_object* v_putStr_689_; lean_object* v___x_690_; 
v___x_688_ = lean_get_stderr();
v_putStr_689_ = lean_ctor_get(v___x_688_, 4);
lean_inc_ref(v_putStr_689_);
lean_dec_ref(v___x_688_);
v___x_690_ = lean_apply_2(v_putStr_689_, v_s_686_, lean_box(0));
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8___boxed(lean_object* v_s_691_, lean_object* v_a_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v_s_691_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6(lean_object* v_s_694_){
_start:
{
uint32_t v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_696_ = 10;
v___x_697_ = lean_string_push(v_s_694_, v___x_696_);
v___x_698_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v___x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6___boxed(lean_object* v_s_699_, lean_object* v_a_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_IO_eprintln___at___00main_spec__6(v_s_699_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(lean_object* v_o_705_, lean_object* v_k_706_, lean_object* v_v_707_){
_start:
{
lean_object* v_map_708_; uint8_t v_hasTrace_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_723_; 
v_map_708_ = lean_ctor_get(v_o_705_, 0);
v_hasTrace_709_ = lean_ctor_get_uint8(v_o_705_, sizeof(void*)*1);
v_isSharedCheck_723_ = !lean_is_exclusive(v_o_705_);
if (v_isSharedCheck_723_ == 0)
{
v___x_711_ = v_o_705_;
v_isShared_712_ = v_isSharedCheck_723_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_map_708_);
lean_dec(v_o_705_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_723_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_713_, 0, v_v_707_);
lean_inc(v_k_706_);
v___x_714_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_706_, v___x_713_, v_map_708_);
if (v_hasTrace_709_ == 0)
{
lean_object* v___x_715_; uint8_t v___x_716_; lean_object* v___x_718_; 
v___x_715_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_716_ = l_Lean_Name_isPrefixOf(v___x_715_, v_k_706_);
lean_dec(v_k_706_);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 0, v___x_714_);
v___x_718_ = v___x_711_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_714_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
lean_ctor_set_uint8(v___x_718_, sizeof(void*)*1, v___x_716_);
return v___x_718_;
}
}
else
{
lean_object* v___x_721_; 
lean_dec(v_k_706_);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 0, v___x_714_);
v___x_721_ = v___x_711_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_714_);
lean_ctor_set_uint8(v_reuseFailAlloc_722_, sizeof(void*)*1, v_hasTrace_709_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00main_spec__3(lean_object* v_opts_724_, lean_object* v_opt_725_, lean_object* v_val_726_){
_start:
{
lean_object* v_name_727_; lean_object* v___x_728_; 
v_name_727_ = lean_ctor_get(v_opt_725_, 0);
lean_inc(v_name_727_);
lean_dec_ref(v_opt_725_);
v___x_728_ = l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(v_opts_724_, v_name_727_, v_val_726_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(lean_object* v_as_729_, size_t v_i_730_, size_t v_stop_731_, lean_object* v_b_732_){
_start:
{
uint8_t v___x_733_; 
v___x_733_ = lean_usize_dec_eq(v_i_730_, v_stop_731_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; lean_object* v_name_735_; lean_object* v___x_736_; size_t v___x_737_; size_t v___x_738_; 
v___x_734_ = lean_array_uget_borrowed(v_as_729_, v_i_730_);
v_name_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_name_735_);
v___x_736_ = l_Lean_Compiler_LCNF_setDeclPublic(v_b_732_, v_name_735_);
v___x_737_ = ((size_t)1ULL);
v___x_738_ = lean_usize_add(v_i_730_, v___x_737_);
v_i_730_ = v___x_738_;
v_b_732_ = v___x_736_;
goto _start;
}
else
{
return v_b_732_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___boxed(lean_object* v_as_740_, lean_object* v_i_741_, lean_object* v_stop_742_, lean_object* v_b_743_){
_start:
{
size_t v_i_boxed_744_; size_t v_stop_boxed_745_; lean_object* v_res_746_; 
v_i_boxed_744_ = lean_unbox_usize(v_i_741_);
lean_dec(v_i_741_);
v_stop_boxed_745_ = lean_unbox_usize(v_stop_742_);
lean_dec(v_stop_742_);
v_res_746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v_as_740_, v_i_boxed_744_, v_stop_boxed_745_, v_b_743_);
lean_dec_ref(v_as_740_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg(lean_object* v_as_x27_748_, lean_object* v_b_749_){
_start:
{
if (lean_obj_tag(v_as_x27_748_) == 0)
{
lean_object* v___x_751_; 
v___x_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_751_, 0, v_b_749_);
return v___x_751_;
}
else
{
lean_object* v_head_752_; lean_object* v_tail_753_; lean_object* v_fst_754_; lean_object* v_snd_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_780_; 
v_head_752_ = lean_ctor_get(v_as_x27_748_, 0);
v_tail_753_ = lean_ctor_get(v_as_x27_748_, 1);
v_fst_754_ = lean_ctor_get(v_b_749_, 0);
v_snd_755_ = lean_ctor_get(v_b_749_, 1);
v_isSharedCheck_780_ = !lean_is_exclusive(v_b_749_);
if (v_isSharedCheck_780_ == 0)
{
v___x_757_ = v_b_749_;
v_isShared_758_ = v_isSharedCheck_780_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_snd_755_);
lean_inc(v_fst_754_);
lean_dec(v_b_749_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_780_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_759_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0));
v___x_760_ = lean_string_dec_eq(v_head_752_, v___x_759_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; 
lean_inc(v_head_752_);
v___x_761_ = l___private_LeanIR_0__setConfigOption(v_snd_755_, v_head_752_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_764_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_a_762_);
lean_dec_ref_known(v___x_761_, 1);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 1, v_a_762_);
v___x_764_ = v___x_757_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_fst_754_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v_a_762_);
v___x_764_ = v_reuseFailAlloc_766_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
v_as_x27_748_ = v_tail_753_;
v_b_749_ = v___x_764_;
goto _start;
}
}
else
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
lean_del_object(v___x_757_);
lean_dec(v_fst_754_);
v_a_767_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_761_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_761_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_767_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
else
{
lean_object* v___x_775_; lean_object* v___x_777_; 
lean_dec(v_fst_754_);
v___x_775_ = lean_box(v___x_760_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 0, v___x_775_);
v___x_777_ = v___x_757_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_775_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_snd_755_);
v___x_777_ = v_reuseFailAlloc_779_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
v_as_x27_748_ = v_tail_753_;
v_b_749_ = v___x_777_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg___boxed(lean_object* v_as_x27_781_, lean_object* v_b_782_, lean_object* v___y_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_781_, v_b_782_);
lean_dec(v_as_x27_781_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(lean_object* v_a_785_, lean_object* v_as_786_, size_t v_i_787_, size_t v_stop_788_, lean_object* v_b_789_){
_start:
{
lean_object* v___y_791_; uint8_t v___x_795_; 
v___x_795_ = lean_usize_dec_eq(v_i_787_, v_stop_788_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; lean_object* v_name_797_; uint8_t v___x_798_; 
v___x_796_ = lean_array_uget_borrowed(v_as_786_, v_i_787_);
v_name_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_name_797_);
lean_inc_ref(v_a_785_);
v___x_798_ = l_Lean_isExtern(v_a_785_, v_name_797_);
if (v___x_798_ == 0)
{
v___y_791_ = v_b_789_;
goto v___jp_790_;
}
else
{
lean_object* v___x_799_; 
lean_inc(v___x_796_);
v___x_799_ = lean_array_push(v_b_789_, v___x_796_);
v___y_791_ = v___x_799_;
goto v___jp_790_;
}
}
else
{
lean_dec_ref(v_a_785_);
return v_b_789_;
}
v___jp_790_:
{
size_t v___x_792_; size_t v___x_793_; 
v___x_792_ = ((size_t)1ULL);
v___x_793_ = lean_usize_add(v_i_787_, v___x_792_);
v_i_787_ = v___x_793_;
v_b_789_ = v___y_791_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18___boxed(lean_object* v_a_800_, lean_object* v_as_801_, lean_object* v_i_802_, lean_object* v_stop_803_, lean_object* v_b_804_){
_start:
{
size_t v_i_boxed_805_; size_t v_stop_boxed_806_; lean_object* v_res_807_; 
v_i_boxed_805_ = lean_unbox_usize(v_i_802_);
lean_dec(v_i_802_);
v_stop_boxed_806_ = lean_unbox_usize(v_stop_803_);
lean_dec(v_stop_803_);
v_res_807_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_a_800_, v_as_801_, v_i_boxed_805_, v_stop_boxed_806_, v_b_804_);
lean_dec_ref(v_as_801_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(lean_object* v_as_808_, size_t v_i_809_, size_t v_stop_810_, lean_object* v_b_811_){
_start:
{
uint8_t v___x_812_; 
v___x_812_ = lean_usize_dec_eq(v_i_809_, v_stop_810_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; lean_object* v_toEnvExtension_814_; lean_object* v_asyncMode_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; size_t v___x_819_; size_t v___x_820_; 
v___x_813_ = l_Lean_Compiler_LCNF_impureSigExt;
v_toEnvExtension_814_ = lean_ctor_get(v___x_813_, 0);
v_asyncMode_815_ = lean_ctor_get(v_toEnvExtension_814_, 2);
v___x_816_ = lean_box(0);
v___x_817_ = lean_array_uget_borrowed(v_as_808_, v_i_809_);
lean_inc(v___x_817_);
v___x_818_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_813_, v_b_811_, v___x_817_, v_asyncMode_815_, v___x_816_);
v___x_819_ = ((size_t)1ULL);
v___x_820_ = lean_usize_add(v_i_809_, v___x_819_);
v_i_809_ = v___x_820_;
v_b_811_ = v___x_818_;
goto _start;
}
else
{
return v_b_811_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___boxed(lean_object* v_as_822_, lean_object* v_i_823_, lean_object* v_stop_824_, lean_object* v_b_825_){
_start:
{
size_t v_i_boxed_826_; size_t v_stop_boxed_827_; lean_object* v_res_828_; 
v_i_boxed_826_ = lean_unbox_usize(v_i_823_);
lean_dec(v_i_823_);
v_stop_boxed_827_ = lean_unbox_usize(v_stop_824_);
lean_dec(v_stop_824_);
v_res_828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v_as_822_, v_i_boxed_826_, v_stop_boxed_827_, v_b_825_);
lean_dec_ref(v_as_822_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(lean_object* v___y_830_, lean_object* v_as_831_, size_t v_i_832_, size_t v_stop_833_, lean_object* v_b_834_){
_start:
{
lean_object* v___y_836_; uint8_t v___x_840_; 
v___x_840_ = lean_usize_dec_eq(v_i_832_, v_stop_833_);
if (v___x_840_ == 0)
{
lean_object* v_fst_841_; lean_object* v_snd_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___y_846_; 
v_fst_841_ = lean_ctor_get(v_b_834_, 0);
v_snd_842_ = lean_ctor_get(v_b_834_, 1);
v___x_843_ = lean_array_uget_borrowed(v_as_831_, v_i_832_);
v___x_844_ = l_Lean_IR_Decl_name(v___x_843_);
if (lean_obj_tag(v___x_844_) == 1)
{
lean_object* v_pre_859_; lean_object* v_str_860_; lean_object* v___x_861_; uint8_t v___x_862_; 
v_pre_859_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_pre_859_);
v_str_860_ = lean_ctor_get(v___x_844_, 1);
lean_inc_ref(v_str_860_);
v___x_861_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___closed__0));
v___x_862_ = lean_string_dec_eq(v_str_860_, v___x_861_);
lean_dec_ref(v_str_860_);
if (v___x_862_ == 0)
{
lean_dec(v_pre_859_);
lean_inc_ref(v___x_844_);
v___y_846_ = v___x_844_;
goto v___jp_845_;
}
else
{
v___y_846_ = v_pre_859_;
goto v___jp_845_;
}
}
else
{
lean_inc(v___x_844_);
v___y_846_ = v___x_844_;
goto v___jp_845_;
}
v___jp_845_:
{
uint8_t v___x_847_; 
lean_inc_ref(v___y_830_);
v___x_847_ = l_Lean_isExtern(v___y_830_, v___y_846_);
if (v___x_847_ == 0)
{
lean_dec(v___x_844_);
v___y_836_ = v_b_834_;
goto v___jp_835_;
}
else
{
lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_856_; 
lean_inc(v_snd_842_);
lean_inc(v_fst_841_);
v_isSharedCheck_856_ = !lean_is_exclusive(v_b_834_);
if (v_isSharedCheck_856_ == 0)
{
lean_object* v_unused_857_; lean_object* v_unused_858_; 
v_unused_857_ = lean_ctor_get(v_b_834_, 1);
lean_dec(v_unused_857_);
v_unused_858_ = lean_ctor_get(v_b_834_, 0);
lean_dec(v_unused_858_);
v___x_849_ = v_b_834_;
v_isShared_850_ = v_isSharedCheck_856_;
goto v_resetjp_848_;
}
else
{
lean_dec(v_b_834_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_856_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_854_; 
lean_inc_n(v___x_843_, 2);
v___x_851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_843_);
lean_ctor_set(v___x_851_, 1, v_fst_841_);
v___x_852_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(v_snd_842_, v___x_844_, v___x_843_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 1, v___x_852_);
lean_ctor_set(v___x_849_, 0, v___x_851_);
v___x_854_ = v___x_849_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_851_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v___x_852_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
v___y_836_ = v___x_854_;
goto v___jp_835_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_830_);
return v_b_834_;
}
v___jp_835_:
{
size_t v___x_837_; size_t v___x_838_; 
v___x_837_ = ((size_t)1ULL);
v___x_838_ = lean_usize_add(v_i_832_, v___x_837_);
v_i_832_ = v___x_838_;
v_b_834_ = v___y_836_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___boxed(lean_object* v___y_863_, lean_object* v_as_864_, lean_object* v_i_865_, lean_object* v_stop_866_, lean_object* v_b_867_){
_start:
{
size_t v_i_boxed_868_; size_t v_stop_boxed_869_; lean_object* v_res_870_; 
v_i_boxed_868_ = lean_unbox_usize(v_i_865_);
lean_dec(v_i_865_);
v_stop_boxed_869_ = lean_unbox_usize(v_stop_866_);
lean_dec(v_stop_866_);
v_res_870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_863_, v_as_864_, v_i_boxed_868_, v_stop_boxed_869_, v_b_867_);
lean_dec_ref(v_as_864_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27(lean_object* v_as_874_, size_t v_sz_875_, size_t v_i_876_, lean_object* v_b_877_){
_start:
{
uint8_t v___x_879_; 
v___x_879_ = lean_usize_dec_lt(v_i_876_, v_sz_875_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; 
v___x_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_880_, 0, v_b_877_);
return v___x_880_;
}
else
{
uint8_t v___x_881_; lean_object* v_a_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
lean_dec_ref(v_b_877_);
v___x_881_ = 0;
v_a_882_ = lean_array_uget_borrowed(v_as_874_, v_i_876_);
lean_inc(v_a_882_);
v___x_883_ = l_Lean_Message_toString(v_a_882_, v___x_881_);
v___x_884_ = l_IO_eprintln___at___00main_spec__6(v___x_883_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v___x_885_; size_t v___x_886_; size_t v___x_887_; 
lean_dec_ref_known(v___x_884_, 1);
v___x_885_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___closed__0));
v___x_886_ = ((size_t)1ULL);
v___x_887_ = lean_usize_add(v_i_876_, v___x_886_);
v_i_876_ = v___x_887_;
v_b_877_ = v___x_885_;
goto _start;
}
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
v_a_889_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_884_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_884_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___boxed(lean_object* v_as_897_, lean_object* v_sz_898_, lean_object* v_i_899_, lean_object* v_b_900_, lean_object* v___y_901_){
_start:
{
size_t v_sz_boxed_902_; size_t v_i_boxed_903_; lean_object* v_res_904_; 
v_sz_boxed_902_ = lean_unbox_usize(v_sz_898_);
lean_dec(v_sz_898_);
v_i_boxed_903_ = lean_unbox_usize(v_i_899_);
lean_dec(v_i_899_);
v_res_904_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27(v_as_897_, v_sz_boxed_902_, v_i_boxed_903_, v_b_900_);
lean_dec_ref(v_as_897_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(lean_object* v_as_905_, size_t v_sz_906_, size_t v_i_907_, lean_object* v_b_908_){
_start:
{
uint8_t v___x_910_; 
v___x_910_ = lean_usize_dec_lt(v_i_907_, v_sz_906_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; 
v___x_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_911_, 0, v_b_908_);
return v___x_911_;
}
else
{
uint8_t v___x_912_; lean_object* v_a_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
lean_dec_ref(v_b_908_);
v___x_912_ = 0;
v_a_913_ = lean_array_uget_borrowed(v_as_905_, v_i_907_);
lean_inc(v_a_913_);
v___x_914_ = l_Lean_Message_toString(v_a_913_, v___x_912_);
v___x_915_ = l_IO_eprintln___at___00main_spec__6(v___x_914_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v___x_916_; size_t v___x_917_; size_t v___x_918_; lean_object* v___x_919_; 
lean_dec_ref_known(v___x_915_, 1);
v___x_916_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___closed__0));
v___x_917_ = ((size_t)1ULL);
v___x_918_ = lean_usize_add(v_i_907_, v___x_917_);
v___x_919_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27(v_as_905_, v_sz_906_, v___x_918_, v___x_916_);
return v___x_919_;
}
else
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
v_a_920_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_915_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_915_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13___boxed(lean_object* v_as_928_, lean_object* v_sz_929_, lean_object* v_i_930_, lean_object* v_b_931_, lean_object* v___y_932_){
_start:
{
size_t v_sz_boxed_933_; size_t v_i_boxed_934_; lean_object* v_res_935_; 
v_sz_boxed_933_ = lean_unbox_usize(v_sz_929_);
lean_dec(v_sz_929_);
v_i_boxed_934_ = lean_unbox_usize(v_i_930_);
lean_dec(v_i_930_);
v_res_935_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_as_928_, v_sz_boxed_933_, v_i_boxed_934_, v_b_931_);
lean_dec_ref(v_as_928_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(lean_object* v_init_936_, lean_object* v_n_937_, lean_object* v_b_938_){
_start:
{
if (lean_obj_tag(v_n_937_) == 0)
{
lean_object* v_cs_940_; lean_object* v___x_941_; lean_object* v___x_942_; size_t v_sz_943_; size_t v___x_944_; lean_object* v___x_945_; 
v_cs_940_ = lean_ctor_get(v_n_937_, 0);
v___x_941_ = lean_box(0);
v___x_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
lean_ctor_set(v___x_942_, 1, v_b_938_);
v_sz_943_ = lean_array_size(v_cs_940_);
v___x_944_ = ((size_t)0ULL);
v___x_945_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__12(v_init_936_, v_cs_940_, v_sz_943_, v___x_944_, v___x_942_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_960_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_960_ == 0)
{
v___x_948_ = v___x_945_;
v_isShared_949_ = v_isSharedCheck_960_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_945_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_960_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v_fst_950_; 
v_fst_950_ = lean_ctor_get(v_a_946_, 0);
if (lean_obj_tag(v_fst_950_) == 0)
{
lean_object* v_snd_951_; lean_object* v___x_952_; lean_object* v___x_954_; 
v_snd_951_ = lean_ctor_get(v_a_946_, 1);
lean_inc(v_snd_951_);
lean_dec(v_a_946_);
v___x_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_952_, 0, v_snd_951_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 0, v___x_952_);
v___x_954_ = v___x_948_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_952_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
else
{
lean_object* v_val_956_; lean_object* v___x_958_; 
lean_inc_ref(v_fst_950_);
lean_dec(v_a_946_);
v_val_956_ = lean_ctor_get(v_fst_950_, 0);
lean_inc(v_val_956_);
lean_dec_ref_known(v_fst_950_, 1);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 0, v_val_956_);
v___x_958_ = v___x_948_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_val_956_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
else
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
v_a_961_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_968_ == 0)
{
v___x_963_ = v___x_945_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_945_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_961_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
else
{
lean_object* v_vs_969_; lean_object* v___x_970_; lean_object* v___x_971_; size_t v_sz_972_; size_t v___x_973_; lean_object* v___x_974_; 
v_vs_969_ = lean_ctor_get(v_n_937_, 0);
v___x_970_ = lean_box(0);
v___x_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
lean_ctor_set(v___x_971_, 1, v_b_938_);
v_sz_972_ = lean_array_size(v_vs_969_);
v___x_973_ = ((size_t)0ULL);
v___x_974_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_vs_969_, v_sz_972_, v___x_973_, v___x_971_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_989_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_989_ == 0)
{
v___x_977_ = v___x_974_;
v_isShared_978_ = v_isSharedCheck_989_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_974_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_989_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v_fst_979_; 
v_fst_979_ = lean_ctor_get(v_a_975_, 0);
if (lean_obj_tag(v_fst_979_) == 0)
{
lean_object* v_snd_980_; lean_object* v___x_981_; lean_object* v___x_983_; 
v_snd_980_ = lean_ctor_get(v_a_975_, 1);
lean_inc(v_snd_980_);
lean_dec(v_a_975_);
v___x_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_981_, 0, v_snd_980_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v___x_981_);
v___x_983_ = v___x_977_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_981_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
else
{
lean_object* v_val_985_; lean_object* v___x_987_; 
lean_inc_ref(v_fst_979_);
lean_dec(v_a_975_);
v_val_985_ = lean_ctor_get(v_fst_979_, 0);
lean_inc(v_val_985_);
lean_dec_ref_known(v_fst_979_, 1);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v_val_985_);
v___x_987_ = v___x_977_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_val_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
else
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
v_a_990_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_974_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_974_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_990_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__12(lean_object* v_init_998_, lean_object* v_as_999_, size_t v_sz_1000_, size_t v_i_1001_, lean_object* v_b_1002_){
_start:
{
uint8_t v___x_1004_; 
v___x_1004_ = lean_usize_dec_lt(v_i_1001_, v_sz_1000_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; 
v___x_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1005_, 0, v_b_1002_);
return v___x_1005_;
}
else
{
lean_object* v_snd_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1040_; 
v_snd_1006_ = lean_ctor_get(v_b_1002_, 1);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_b_1002_);
if (v_isSharedCheck_1040_ == 0)
{
lean_object* v_unused_1041_; 
v_unused_1041_ = lean_ctor_get(v_b_1002_, 0);
lean_dec(v_unused_1041_);
v___x_1008_ = v_b_1002_;
v_isShared_1009_ = v_isSharedCheck_1040_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_snd_1006_);
lean_dec(v_b_1002_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1040_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; lean_object* v_a_1011_; lean_object* v___x_1012_; 
v___x_1010_ = lean_box(0);
v_a_1011_ = lean_array_uget_borrowed(v_as_999_, v_i_1001_);
lean_inc(v_snd_1006_);
v___x_1012_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_998_, v_a_1011_, v_snd_1006_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1031_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1015_ = v___x_1012_;
v_isShared_1016_ = v_isSharedCheck_1031_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_1012_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1031_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
if (lean_obj_tag(v_a_1013_) == 0)
{
lean_object* v___x_1017_; lean_object* v___x_1019_; 
v___x_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1017_, 0, v_a_1013_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1017_);
v___x_1019_ = v___x_1008_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1017_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v_snd_1006_);
v___x_1019_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1021_; 
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 0, v___x_1019_);
v___x_1021_ = v___x_1015_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1019_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; 
lean_del_object(v___x_1015_);
lean_dec(v_snd_1006_);
v_a_1024_ = lean_ctor_get(v_a_1013_, 0);
lean_inc(v_a_1024_);
lean_dec_ref_known(v_a_1013_, 1);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 1, v_a_1024_);
lean_ctor_set(v___x_1008_, 0, v___x_1010_);
v___x_1026_ = v___x_1008_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v_a_1024_);
v___x_1026_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
size_t v___x_1027_; size_t v___x_1028_; 
v___x_1027_ = ((size_t)1ULL);
v___x_1028_ = lean_usize_add(v_i_1001_, v___x_1027_);
v_i_1001_ = v___x_1028_;
v_b_1002_ = v___x_1026_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_del_object(v___x_1008_);
lean_dec(v_snd_1006_);
v_a_1032_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_1012_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1012_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__12___boxed(lean_object* v_init_1042_, lean_object* v_as_1043_, lean_object* v_sz_1044_, lean_object* v_i_1045_, lean_object* v_b_1046_, lean_object* v___y_1047_){
_start:
{
size_t v_sz_boxed_1048_; size_t v_i_boxed_1049_; lean_object* v_res_1050_; 
v_sz_boxed_1048_ = lean_unbox_usize(v_sz_1044_);
lean_dec(v_sz_1044_);
v_i_boxed_1049_ = lean_unbox_usize(v_i_1045_);
lean_dec(v_i_1045_);
v_res_1050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__12(v_init_1042_, v_as_1043_, v_sz_boxed_1048_, v_i_boxed_1049_, v_b_1046_);
lean_dec_ref(v_as_1043_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10___boxed(lean_object* v_init_1051_, lean_object* v_n_1052_, lean_object* v_b_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_1051_, v_n_1052_, v_b_1053_);
lean_dec_ref(v_n_1052_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15(lean_object* v_as_1059_, size_t v_sz_1060_, size_t v_i_1061_, lean_object* v_b_1062_){
_start:
{
uint8_t v___x_1064_; 
v___x_1064_ = lean_usize_dec_lt(v_i_1061_, v_sz_1060_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; 
v___x_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1065_, 0, v_b_1062_);
return v___x_1065_;
}
else
{
uint8_t v___x_1066_; lean_object* v_a_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
lean_dec_ref(v_b_1062_);
v___x_1066_ = 0;
v_a_1067_ = lean_array_uget_borrowed(v_as_1059_, v_i_1061_);
lean_inc(v_a_1067_);
v___x_1068_ = l_Lean_Message_toString(v_a_1067_, v___x_1066_);
v___x_1069_ = l_IO_eprintln___at___00main_spec__6(v___x_1068_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v___x_1070_; size_t v___x_1071_; size_t v___x_1072_; 
lean_dec_ref_known(v___x_1069_, 1);
v___x_1070_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___closed__0));
v___x_1071_ = ((size_t)1ULL);
v___x_1072_ = lean_usize_add(v_i_1061_, v___x_1071_);
v_i_1061_ = v___x_1072_;
v_b_1062_ = v___x_1070_;
goto _start;
}
else
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
v_a_1074_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1076_ = v___x_1069_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1069_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1074_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___boxed(lean_object* v_as_1082_, lean_object* v_sz_1083_, lean_object* v_i_1084_, lean_object* v_b_1085_, lean_object* v___y_1086_){
_start:
{
size_t v_sz_boxed_1087_; size_t v_i_boxed_1088_; lean_object* v_res_1089_; 
v_sz_boxed_1087_ = lean_unbox_usize(v_sz_1083_);
lean_dec(v_sz_1083_);
v_i_boxed_1088_ = lean_unbox_usize(v_i_1084_);
lean_dec(v_i_1084_);
v_res_1089_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15(v_as_1082_, v_sz_boxed_1087_, v_i_boxed_1088_, v_b_1085_);
lean_dec_ref(v_as_1082_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(lean_object* v_as_1090_, size_t v_sz_1091_, size_t v_i_1092_, lean_object* v_b_1093_){
_start:
{
uint8_t v___x_1095_; 
v___x_1095_ = lean_usize_dec_lt(v_i_1092_, v_sz_1091_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; 
v___x_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1096_, 0, v_b_1093_);
return v___x_1096_;
}
else
{
uint8_t v___x_1097_; lean_object* v_a_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
lean_dec_ref(v_b_1093_);
v___x_1097_ = 0;
v_a_1098_ = lean_array_uget_borrowed(v_as_1090_, v_i_1092_);
lean_inc(v_a_1098_);
v___x_1099_ = l_Lean_Message_toString(v_a_1098_, v___x_1097_);
v___x_1100_ = l_IO_eprintln___at___00main_spec__6(v___x_1099_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v___x_1101_; size_t v___x_1102_; size_t v___x_1103_; lean_object* v___x_1104_; 
lean_dec_ref_known(v___x_1100_, 1);
v___x_1101_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___closed__0));
v___x_1102_ = ((size_t)1ULL);
v___x_1103_ = lean_usize_add(v_i_1092_, v___x_1102_);
v___x_1104_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15(v_as_1090_, v_sz_1091_, v___x_1103_, v___x_1101_);
return v___x_1104_;
}
else
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
v_a_1105_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_1100_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1100_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11___boxed(lean_object* v_as_1113_, lean_object* v_sz_1114_, lean_object* v_i_1115_, lean_object* v_b_1116_, lean_object* v___y_1117_){
_start:
{
size_t v_sz_boxed_1118_; size_t v_i_boxed_1119_; lean_object* v_res_1120_; 
v_sz_boxed_1118_ = lean_unbox_usize(v_sz_1114_);
lean_dec(v_sz_1114_);
v_i_boxed_1119_ = lean_unbox_usize(v_i_1115_);
lean_dec(v_i_1115_);
v_res_1120_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_as_1113_, v_sz_boxed_1118_, v_i_boxed_1119_, v_b_1116_);
lean_dec_ref(v_as_1113_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7(lean_object* v_t_1121_, lean_object* v_init_1122_){
_start:
{
lean_object* v_root_1124_; lean_object* v_tail_1125_; lean_object* v___x_1126_; 
v_root_1124_ = lean_ctor_get(v_t_1121_, 0);
v_tail_1125_ = lean_ctor_get(v_t_1121_, 1);
v___x_1126_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_1122_, v_root_1124_, v_init_1122_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1163_; 
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1129_ = v___x_1126_;
v_isShared_1130_ = v_isSharedCheck_1163_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1126_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1163_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
if (lean_obj_tag(v_a_1127_) == 0)
{
lean_object* v_a_1131_; lean_object* v___x_1133_; 
v_a_1131_ = lean_ctor_get(v_a_1127_, 0);
lean_inc(v_a_1131_);
lean_dec_ref_known(v_a_1127_, 1);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 0, v_a_1131_);
v___x_1133_ = v___x_1129_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1131_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; size_t v_sz_1138_; size_t v___x_1139_; lean_object* v___x_1140_; 
lean_del_object(v___x_1129_);
v_a_1135_ = lean_ctor_get(v_a_1127_, 0);
lean_inc(v_a_1135_);
lean_dec_ref_known(v_a_1127_, 1);
v___x_1136_ = lean_box(0);
v___x_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
lean_ctor_set(v___x_1137_, 1, v_a_1135_);
v_sz_1138_ = lean_array_size(v_tail_1125_);
v___x_1139_ = ((size_t)0ULL);
v___x_1140_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_tail_1125_, v_sz_1138_, v___x_1139_, v___x_1137_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1154_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1143_ = v___x_1140_;
v_isShared_1144_ = v_isSharedCheck_1154_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1140_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1154_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v_fst_1145_; 
v_fst_1145_ = lean_ctor_get(v_a_1141_, 0);
if (lean_obj_tag(v_fst_1145_) == 0)
{
lean_object* v_snd_1146_; lean_object* v___x_1148_; 
v_snd_1146_ = lean_ctor_get(v_a_1141_, 1);
lean_inc(v_snd_1146_);
lean_dec(v_a_1141_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 0, v_snd_1146_);
v___x_1148_ = v___x_1143_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_snd_1146_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
else
{
lean_object* v_val_1150_; lean_object* v___x_1152_; 
lean_inc_ref(v_fst_1145_);
lean_dec(v_a_1141_);
v_val_1150_ = lean_ctor_get(v_fst_1145_, 0);
lean_inc(v_val_1150_);
lean_dec_ref_known(v_fst_1145_, 1);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 0, v_val_1150_);
v___x_1152_ = v___x_1143_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_val_1150_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
else
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
v_a_1155_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_1140_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1140_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
}
}
else
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
v_a_1164_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1166_ = v___x_1126_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1126_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1164_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7___boxed(lean_object* v_t_1172_, lean_object* v_init_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_t_1172_, v_init_1173_);
lean_dec_ref(v_t_1172_);
return v_res_1175_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0(uint8_t v_suppressElabErrors_1183_, uint8_t v___y_1184_, lean_object* v_x_1185_){
_start:
{
if (lean_obj_tag(v_x_1185_) == 1)
{
lean_object* v_pre_1186_; 
v_pre_1186_ = lean_ctor_get(v_x_1185_, 0);
switch(lean_obj_tag(v_pre_1186_))
{
case 1:
{
lean_object* v_pre_1187_; 
v_pre_1187_ = lean_ctor_get(v_pre_1186_, 0);
switch(lean_obj_tag(v_pre_1187_))
{
case 0:
{
lean_object* v_str_1188_; lean_object* v_str_1189_; lean_object* v___x_1190_; uint8_t v___x_1191_; 
v_str_1188_ = lean_ctor_get(v_x_1185_, 1);
v_str_1189_ = lean_ctor_get(v_pre_1186_, 1);
v___x_1190_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__0));
v___x_1191_ = lean_string_dec_eq(v_str_1189_, v___x_1190_);
if (v___x_1191_ == 0)
{
lean_object* v___x_1192_; uint8_t v___x_1193_; 
v___x_1192_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__1));
v___x_1193_ = lean_string_dec_eq(v_str_1189_, v___x_1192_);
if (v___x_1193_ == 0)
{
return v___x_1193_;
}
else
{
lean_object* v___x_1194_; uint8_t v___x_1195_; 
v___x_1194_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__2));
v___x_1195_ = lean_string_dec_eq(v_str_1188_, v___x_1194_);
if (v___x_1195_ == 0)
{
return v___x_1195_;
}
else
{
return v_suppressElabErrors_1183_;
}
}
}
else
{
lean_object* v___x_1196_; uint8_t v___x_1197_; 
v___x_1196_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__3));
v___x_1197_ = lean_string_dec_eq(v_str_1188_, v___x_1196_);
if (v___x_1197_ == 0)
{
return v___x_1197_;
}
else
{
return v_suppressElabErrors_1183_;
}
}
}
case 1:
{
lean_object* v_pre_1198_; 
v_pre_1198_ = lean_ctor_get(v_pre_1187_, 0);
if (lean_obj_tag(v_pre_1198_) == 0)
{
lean_object* v_str_1199_; lean_object* v_str_1200_; lean_object* v_str_1201_; lean_object* v___x_1202_; uint8_t v___x_1203_; 
v_str_1199_ = lean_ctor_get(v_x_1185_, 1);
v_str_1200_ = lean_ctor_get(v_pre_1186_, 1);
v_str_1201_ = lean_ctor_get(v_pre_1187_, 1);
v___x_1202_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__4));
v___x_1203_ = lean_string_dec_eq(v_str_1201_, v___x_1202_);
if (v___x_1203_ == 0)
{
return v___x_1203_;
}
else
{
lean_object* v___x_1204_; uint8_t v___x_1205_; 
v___x_1204_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__5));
v___x_1205_ = lean_string_dec_eq(v_str_1200_, v___x_1204_);
if (v___x_1205_ == 0)
{
return v___x_1205_;
}
else
{
lean_object* v___x_1206_; uint8_t v___x_1207_; 
v___x_1206_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__6));
v___x_1207_ = lean_string_dec_eq(v_str_1199_, v___x_1206_);
if (v___x_1207_ == 0)
{
return v___x_1207_;
}
else
{
return v_suppressElabErrors_1183_;
}
}
}
}
else
{
return v___y_1184_;
}
}
default: 
{
return v___y_1184_;
}
}
}
case 0:
{
lean_object* v_str_1208_; lean_object* v___x_1209_; uint8_t v___x_1210_; 
v_str_1208_ = lean_ctor_get(v_x_1185_, 1);
v___x_1209_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_1210_ = lean_string_dec_eq(v_str_1208_, v___x_1209_);
if (v___x_1210_ == 0)
{
return v___x_1210_;
}
else
{
return v_suppressElabErrors_1183_;
}
}
default: 
{
return v___y_1184_;
}
}
}
else
{
return v___y_1184_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___boxed(lean_object* v_suppressElabErrors_1211_, lean_object* v___y_1212_, lean_object* v_x_1213_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1214_; uint8_t v___y_36940__boxed_1215_; uint8_t v_res_1216_; lean_object* v_r_1217_; 
v_suppressElabErrors_boxed_1214_ = lean_unbox(v_suppressElabErrors_1211_);
v___y_36940__boxed_1215_ = lean_unbox(v___y_1212_);
v_res_1216_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0(v_suppressElabErrors_boxed_1214_, v___y_36940__boxed_1215_, v_x_1213_);
lean_dec(v_x_1213_);
v_r_1217_ = lean_box(v_res_1216_);
return v_r_1217_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(lean_object* v_opts_1218_, lean_object* v_opt_1219_){
_start:
{
lean_object* v_name_1220_; lean_object* v_defValue_1221_; lean_object* v_map_1222_; lean_object* v___x_1223_; 
v_name_1220_ = lean_ctor_get(v_opt_1219_, 0);
v_defValue_1221_ = lean_ctor_get(v_opt_1219_, 1);
v_map_1222_ = lean_ctor_get(v_opts_1218_, 0);
v___x_1223_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1222_, v_name_1220_);
if (lean_obj_tag(v___x_1223_) == 0)
{
uint8_t v___x_1224_; 
v___x_1224_ = lean_unbox(v_defValue_1221_);
return v___x_1224_;
}
else
{
lean_object* v_val_1225_; 
v_val_1225_ = lean_ctor_get(v___x_1223_, 0);
lean_inc(v_val_1225_);
lean_dec_ref_known(v___x_1223_, 1);
if (lean_obj_tag(v_val_1225_) == 1)
{
uint8_t v_v_1226_; 
v_v_1226_ = lean_ctor_get_uint8(v_val_1225_, 0);
lean_dec_ref_known(v_val_1225_, 0);
return v_v_1226_;
}
else
{
uint8_t v___x_1227_; 
lean_dec(v_val_1225_);
v___x_1227_ = lean_unbox(v_defValue_1221_);
return v___x_1227_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___boxed(lean_object* v_opts_1228_, lean_object* v_opt_1229_){
_start:
{
uint8_t v_res_1230_; lean_object* v_r_1231_; 
v_res_1230_ = l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(v_opts_1228_, v_opt_1229_);
lean_dec_ref(v_opt_1229_);
lean_dec_ref(v_opts_1228_);
v_r_1231_ = lean_box(v_res_1230_);
return v_r_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44(lean_object* v_ref_1233_, lean_object* v_msgData_1234_, uint8_t v_severity_1235_, uint8_t v_isSilent_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
uint8_t v___y_1241_; lean_object* v___y_1242_; uint8_t v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v_toCold_1248_; lean_object* v___y_1249_; lean_object* v___y_1278_; lean_object* v___y_1279_; uint8_t v___y_1280_; lean_object* v___y_1281_; uint8_t v___y_1282_; uint8_t v___y_1283_; lean_object* v___y_1284_; lean_object* v___y_1285_; uint8_t v___y_1305_; lean_object* v___y_1306_; lean_object* v___y_1307_; uint8_t v___y_1308_; lean_object* v___y_1309_; uint8_t v___y_1310_; lean_object* v___y_1311_; uint8_t v___y_1315_; uint8_t v___y_1316_; uint8_t v___y_1317_; uint8_t v___x_1328_; uint8_t v___y_1330_; uint8_t v___y_1331_; uint8_t v___y_1332_; uint8_t v___y_1334_; uint8_t v___x_1342_; 
v___x_1328_ = 2;
v___x_1342_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1235_, v___x_1328_);
if (v___x_1342_ == 0)
{
v___y_1334_ = v___x_1342_;
goto v___jp_1333_;
}
else
{
uint8_t v___x_1343_; 
lean_inc_ref(v_msgData_1234_);
v___x_1343_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1234_);
v___y_1334_ = v___x_1343_;
goto v___jp_1333_;
}
v___jp_1240_:
{
lean_object* v_currNamespace_1250_; lean_object* v_openDecls_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v_env_1256_; lean_object* v_nextMacroScope_1257_; lean_object* v_ngen_1258_; lean_object* v_auxDeclNGen_1259_; lean_object* v_traceState_1260_; lean_object* v_cache_1261_; lean_object* v_recordedDeps_1262_; lean_object* v_messages_1263_; lean_object* v_infoState_1264_; lean_object* v_snapshotTasks_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1276_; 
v_currNamespace_1250_ = lean_ctor_get(v_toCold_1248_, 4);
v_openDecls_1251_ = lean_ctor_get(v_toCold_1248_, 5);
lean_inc(v_openDecls_1251_);
lean_inc(v_currNamespace_1250_);
v___x_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1252_, 0, v_currNamespace_1250_);
lean_ctor_set(v___x_1252_, 1, v_openDecls_1251_);
v___x_1253_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
lean_ctor_set(v___x_1253_, 1, v___y_1245_);
lean_inc_ref(v___y_1244_);
lean_inc_ref(v___y_1246_);
v___x_1254_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1254_, 0, v___y_1246_);
lean_ctor_set(v___x_1254_, 1, v___y_1242_);
lean_ctor_set(v___x_1254_, 2, v___y_1247_);
lean_ctor_set(v___x_1254_, 3, v___y_1244_);
lean_ctor_set(v___x_1254_, 4, v___x_1253_);
lean_ctor_set_uint8(v___x_1254_, sizeof(void*)*5, v___y_1243_);
lean_ctor_set_uint8(v___x_1254_, sizeof(void*)*5 + 1, v___y_1241_);
lean_ctor_set_uint8(v___x_1254_, sizeof(void*)*5 + 2, v_isSilent_1236_);
v___x_1255_ = lean_st_ref_take(v___y_1249_);
v_env_1256_ = lean_ctor_get(v___x_1255_, 0);
v_nextMacroScope_1257_ = lean_ctor_get(v___x_1255_, 1);
v_ngen_1258_ = lean_ctor_get(v___x_1255_, 2);
v_auxDeclNGen_1259_ = lean_ctor_get(v___x_1255_, 3);
v_traceState_1260_ = lean_ctor_get(v___x_1255_, 4);
v_cache_1261_ = lean_ctor_get(v___x_1255_, 5);
v_recordedDeps_1262_ = lean_ctor_get(v___x_1255_, 6);
v_messages_1263_ = lean_ctor_get(v___x_1255_, 7);
v_infoState_1264_ = lean_ctor_get(v___x_1255_, 8);
v_snapshotTasks_1265_ = lean_ctor_get(v___x_1255_, 9);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1267_ = v___x_1255_;
v_isShared_1268_ = v_isSharedCheck_1276_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_snapshotTasks_1265_);
lean_inc(v_infoState_1264_);
lean_inc(v_messages_1263_);
lean_inc(v_recordedDeps_1262_);
lean_inc(v_cache_1261_);
lean_inc(v_traceState_1260_);
lean_inc(v_auxDeclNGen_1259_);
lean_inc(v_ngen_1258_);
lean_inc(v_nextMacroScope_1257_);
lean_inc(v_env_1256_);
lean_dec(v___x_1255_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1276_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1272_; 
v___x_1269_ = lean_box(0);
v___x_1270_ = l_Lean_MessageLog_add(v___x_1254_, v_messages_1263_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 7, v___x_1270_);
v___x_1272_ = v___x_1267_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_env_1256_);
lean_ctor_set(v_reuseFailAlloc_1275_, 1, v_nextMacroScope_1257_);
lean_ctor_set(v_reuseFailAlloc_1275_, 2, v_ngen_1258_);
lean_ctor_set(v_reuseFailAlloc_1275_, 3, v_auxDeclNGen_1259_);
lean_ctor_set(v_reuseFailAlloc_1275_, 4, v_traceState_1260_);
lean_ctor_set(v_reuseFailAlloc_1275_, 5, v_cache_1261_);
lean_ctor_set(v_reuseFailAlloc_1275_, 6, v_recordedDeps_1262_);
lean_ctor_set(v_reuseFailAlloc_1275_, 7, v___x_1270_);
lean_ctor_set(v_reuseFailAlloc_1275_, 8, v_infoState_1264_);
lean_ctor_set(v_reuseFailAlloc_1275_, 9, v_snapshotTasks_1265_);
v___x_1272_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1273_ = lean_st_ref_put(v___y_1249_, v___x_1272_);
v___x_1274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1269_);
return v___x_1274_;
}
}
}
v___jp_1277_:
{
lean_object* v_fileName_1286_; lean_object* v_fileMap_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1303_; 
v_fileName_1286_ = lean_ctor_get(v___y_1284_, 0);
v_fileMap_1287_ = lean_ctor_get(v___y_1284_, 1);
v___x_1288_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1234_);
v___x_1289_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(v___x_1288_, v___y_1237_, v___y_1238_);
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1292_ = v___x_1289_;
v_isShared_1293_ = v_isSharedCheck_1303_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1289_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1303_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
lean_inc_ref_n(v_fileMap_1287_, 2);
v___x_1294_ = l_Lean_FileMap_toPosition(v_fileMap_1287_, v___y_1281_);
lean_dec(v___y_1281_);
v___x_1295_ = l_Lean_FileMap_toPosition(v_fileMap_1287_, v___y_1285_);
lean_dec(v___y_1285_);
v___x_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1295_);
v___x_1297_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___closed__0));
if (v___y_1282_ == 0)
{
lean_del_object(v___x_1292_);
lean_dec_ref(v___y_1279_);
v___y_1241_ = v___y_1280_;
v___y_1242_ = v___x_1294_;
v___y_1243_ = v___y_1283_;
v___y_1244_ = v___x_1297_;
v___y_1245_ = v_a_1290_;
v___y_1246_ = v_fileName_1286_;
v___y_1247_ = v___x_1296_;
v_toCold_1248_ = v___y_1278_;
v___y_1249_ = v___y_1238_;
goto v___jp_1240_;
}
else
{
uint8_t v___x_1298_; 
lean_inc(v_a_1290_);
v___x_1298_ = l_Lean_MessageData_hasTag(v___y_1279_, v_a_1290_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; lean_object* v___x_1301_; 
lean_dec_ref_known(v___x_1296_, 1);
lean_dec_ref(v___x_1294_);
lean_dec(v_a_1290_);
v___x_1299_ = lean_box(0);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 0, v___x_1299_);
v___x_1301_ = v___x_1292_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
else
{
lean_del_object(v___x_1292_);
v___y_1241_ = v___y_1280_;
v___y_1242_ = v___x_1294_;
v___y_1243_ = v___y_1283_;
v___y_1244_ = v___x_1297_;
v___y_1245_ = v_a_1290_;
v___y_1246_ = v_fileName_1286_;
v___y_1247_ = v___x_1296_;
v_toCold_1248_ = v___y_1278_;
v___y_1249_ = v___y_1238_;
goto v___jp_1240_;
}
}
}
}
v___jp_1304_:
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Lean_Syntax_getTailPos_x3f(v___y_1309_, v___y_1310_);
lean_dec(v___y_1309_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_inc(v___y_1311_);
v___y_1278_ = v___y_1306_;
v___y_1279_ = v___y_1307_;
v___y_1280_ = v___y_1308_;
v___y_1281_ = v___y_1311_;
v___y_1282_ = v___y_1305_;
v___y_1283_ = v___y_1310_;
v___y_1284_ = v___y_1306_;
v___y_1285_ = v___y_1311_;
goto v___jp_1277_;
}
else
{
lean_object* v_val_1313_; 
v_val_1313_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_val_1313_);
lean_dec_ref_known(v___x_1312_, 1);
v___y_1278_ = v___y_1306_;
v___y_1279_ = v___y_1307_;
v___y_1280_ = v___y_1308_;
v___y_1281_ = v___y_1311_;
v___y_1282_ = v___y_1305_;
v___y_1283_ = v___y_1310_;
v___y_1284_ = v___y_1306_;
v___y_1285_ = v_val_1313_;
goto v___jp_1277_;
}
}
v___jp_1314_:
{
lean_object* v_toCold_1318_; lean_object* v_ref_1319_; uint8_t v_suppressElabErrors_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___f_1323_; lean_object* v_ref_1324_; lean_object* v___x_1325_; 
v_toCold_1318_ = lean_ctor_get(v___y_1237_, 0);
v_ref_1319_ = lean_ctor_get(v___y_1237_, 2);
v_suppressElabErrors_1320_ = lean_ctor_get_uint8(v___y_1237_, sizeof(void*)*3 + 2);
v___x_1321_ = lean_box(v_suppressElabErrors_1320_);
v___x_1322_ = lean_box(v___y_1315_);
v___f_1323_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1323_, 0, v___x_1321_);
lean_closure_set(v___f_1323_, 1, v___x_1322_);
v_ref_1324_ = l_Lean_replaceRef(v_ref_1233_, v_ref_1319_);
v___x_1325_ = l_Lean_Syntax_getPos_x3f(v_ref_1324_, v___y_1316_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v___x_1326_; 
v___x_1326_ = lean_unsigned_to_nat(0u);
v___y_1305_ = v_suppressElabErrors_1320_;
v___y_1306_ = v_toCold_1318_;
v___y_1307_ = v___f_1323_;
v___y_1308_ = v___y_1317_;
v___y_1309_ = v_ref_1324_;
v___y_1310_ = v___y_1316_;
v___y_1311_ = v___x_1326_;
goto v___jp_1304_;
}
else
{
lean_object* v_val_1327_; 
v_val_1327_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_val_1327_);
lean_dec_ref_known(v___x_1325_, 1);
v___y_1305_ = v_suppressElabErrors_1320_;
v___y_1306_ = v_toCold_1318_;
v___y_1307_ = v___f_1323_;
v___y_1308_ = v___y_1317_;
v___y_1309_ = v_ref_1324_;
v___y_1310_ = v___y_1316_;
v___y_1311_ = v_val_1327_;
goto v___jp_1304_;
}
}
v___jp_1329_:
{
if (v___y_1332_ == 0)
{
v___y_1315_ = v___y_1330_;
v___y_1316_ = v___y_1331_;
v___y_1317_ = v_severity_1235_;
goto v___jp_1314_;
}
else
{
v___y_1315_ = v___y_1330_;
v___y_1316_ = v___y_1331_;
v___y_1317_ = v___x_1328_;
goto v___jp_1314_;
}
}
v___jp_1333_:
{
if (v___y_1334_ == 0)
{
uint8_t v___x_1335_; uint8_t v___x_1336_; 
v___x_1335_ = 1;
v___x_1336_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1235_, v___x_1335_);
if (v___x_1336_ == 0)
{
v___y_1330_ = v___y_1334_;
v___y_1331_ = v___y_1334_;
v___y_1332_ = v___x_1336_;
goto v___jp_1329_;
}
else
{
lean_object* v___x_1337_; lean_object* v___x_1338_; uint8_t v___x_1339_; 
v___x_1337_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1237_);
v___x_1338_ = l_Lean_warningAsError;
v___x_1339_ = l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(v___x_1337_, v___x_1338_);
lean_dec_ref(v___x_1337_);
v___y_1330_ = v___y_1334_;
v___y_1331_ = v___y_1334_;
v___y_1332_ = v___x_1339_;
goto v___jp_1329_;
}
}
else
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
lean_dec_ref(v_msgData_1234_);
v___x_1340_ = lean_box(0);
v___x_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
return v___x_1341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___boxed(lean_object* v_ref_1344_, lean_object* v_msgData_1345_, lean_object* v_severity_1346_, lean_object* v_isSilent_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
uint8_t v_severity_boxed_1351_; uint8_t v_isSilent_boxed_1352_; lean_object* v_res_1353_; 
v_severity_boxed_1351_ = lean_unbox(v_severity_1346_);
v_isSilent_boxed_1352_ = lean_unbox(v_isSilent_1347_);
v_res_1353_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44(v_ref_1344_, v_msgData_1345_, v_severity_boxed_1351_, v_isSilent_boxed_1352_, v___y_1348_, v___y_1349_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v_ref_1344_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30(lean_object* v_msgData_1354_, uint8_t v_severity_1355_, uint8_t v_isSilent_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v_ref_1360_; lean_object* v___x_1361_; 
v_ref_1360_ = lean_ctor_get(v___y_1357_, 2);
v___x_1361_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44(v_ref_1360_, v_msgData_1354_, v_severity_1355_, v_isSilent_1356_, v___y_1357_, v___y_1358_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30___boxed(lean_object* v_msgData_1362_, lean_object* v_severity_1363_, lean_object* v_isSilent_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
uint8_t v_severity_boxed_1368_; uint8_t v_isSilent_boxed_1369_; lean_object* v_res_1370_; 
v_severity_boxed_1368_ = lean_unbox(v_severity_1363_);
v_isSilent_boxed_1369_ = lean_unbox(v_isSilent_1364_);
v_res_1370_ = l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30(v_msgData_1362_, v_severity_boxed_1368_, v_isSilent_boxed_1369_, v___y_1365_, v___y_1366_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__13(lean_object* v_msgData_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
uint8_t v___x_1375_; uint8_t v___x_1376_; lean_object* v___x_1377_; 
v___x_1375_ = 2;
v___x_1376_ = 0;
v___x_1377_ = l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30(v_msgData_1371_, v___x_1375_, v___x_1376_, v___y_1372_, v___y_1373_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__13___boxed(lean_object* v_msgData_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
lean_object* v_res_1382_; 
v_res_1382_ = l_Lean_logError___at___00main_spec__13(v_msgData_1378_, v___y_1379_, v___y_1380_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14(lean_object* v_opts_1383_, lean_object* v_opt_1384_){
_start:
{
lean_object* v_name_1385_; lean_object* v_map_1386_; lean_object* v___x_1387_; 
v_name_1385_ = lean_ctor_get(v_opt_1384_, 0);
v_map_1386_ = lean_ctor_get(v_opts_1383_, 0);
v___x_1387_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1386_, v_name_1385_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v___x_1388_; 
v___x_1388_ = lean_box(0);
return v___x_1388_;
}
else
{
lean_object* v_val_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1398_; 
v_val_1389_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1391_ = v___x_1387_;
v_isShared_1392_ = v_isSharedCheck_1398_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_val_1389_);
lean_dec(v___x_1387_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1398_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
if (lean_obj_tag(v_val_1389_) == 0)
{
lean_object* v_v_1393_; lean_object* v___x_1395_; 
v_v_1393_ = lean_ctor_get(v_val_1389_, 0);
lean_inc_ref(v_v_1393_);
lean_dec_ref_known(v_val_1389_, 1);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 0, v_v_1393_);
v___x_1395_ = v___x_1391_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_v_1393_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
else
{
lean_object* v___x_1397_; 
lean_del_object(v___x_1391_);
lean_dec(v_val_1389_);
v___x_1397_ = lean_box(0);
return v___x_1397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___boxed(lean_object* v_opts_1399_, lean_object* v_opt_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14(v_opts_1399_, v_opt_1400_);
lean_dec_ref(v_opt_1400_);
lean_dec_ref(v_opts_1399_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22(lean_object* v_x_1402_, lean_object* v_x_1403_){
_start:
{
if (lean_obj_tag(v_x_1403_) == 0)
{
return v_x_1402_;
}
else
{
lean_object* v_key_1404_; lean_object* v_value_1405_; lean_object* v_tail_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v_key_1404_ = lean_ctor_get(v_x_1403_, 0);
v_value_1405_ = lean_ctor_get(v_x_1403_, 1);
v_tail_1406_ = lean_ctor_get(v_x_1403_, 2);
lean_inc(v_value_1405_);
lean_inc(v_key_1404_);
v___x_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1407_, 0, v_key_1404_);
lean_ctor_set(v___x_1407_, 1, v_value_1405_);
v___x_1408_ = lean_array_push(v_x_1402_, v___x_1407_);
v_x_1402_ = v___x_1408_;
v_x_1403_ = v_tail_1406_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22___boxed(lean_object* v_x_1410_, lean_object* v_x_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22(v_x_1410_, v_x_1411_);
lean_dec(v_x_1411_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__23(lean_object* v_as_1413_, size_t v_i_1414_, size_t v_stop_1415_, lean_object* v_b_1416_){
_start:
{
uint8_t v___x_1417_; 
v___x_1417_ = lean_usize_dec_eq(v_i_1414_, v_stop_1415_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1418_; lean_object* v___x_1419_; size_t v___x_1420_; size_t v___x_1421_; 
v___x_1418_ = lean_array_uget_borrowed(v_as_1413_, v_i_1414_);
v___x_1419_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22(v_b_1416_, v___x_1418_);
v___x_1420_ = ((size_t)1ULL);
v___x_1421_ = lean_usize_add(v_i_1414_, v___x_1420_);
v_i_1414_ = v___x_1421_;
v_b_1416_ = v___x_1419_;
goto _start;
}
else
{
return v_b_1416_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__23___boxed(lean_object* v_as_1423_, lean_object* v_i_1424_, lean_object* v_stop_1425_, lean_object* v_b_1426_){
_start:
{
size_t v_i_boxed_1427_; size_t v_stop_boxed_1428_; lean_object* v_res_1429_; 
v_i_boxed_1427_ = lean_unbox_usize(v_i_1424_);
lean_dec(v_i_1424_);
v_stop_boxed_1428_ = lean_unbox_usize(v_stop_1425_);
lean_dec(v_stop_1425_);
v_res_1429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__23(v_as_1423_, v_i_boxed_1427_, v_stop_boxed_1428_, v_b_1426_);
lean_dec_ref(v_as_1423_);
return v_res_1429_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(lean_object* v_x_1430_, lean_object* v_x_1431_){
_start:
{
lean_object* v_fst_1432_; lean_object* v_fst_1433_; lean_object* v_fst_1434_; lean_object* v_fst_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; uint8_t v___x_1438_; 
v_fst_1432_ = lean_ctor_get(v_x_1430_, 0);
v_fst_1433_ = lean_ctor_get(v_x_1431_, 0);
v_fst_1434_ = lean_ctor_get(v_fst_1432_, 0);
v_fst_1435_ = lean_ctor_get(v_fst_1433_, 0);
v___x_1436_ = lean_unsigned_to_nat(1u);
v___x_1437_ = lean_nat_add(v_fst_1434_, v___x_1436_);
v___x_1438_ = lean_nat_dec_le(v___x_1437_, v_fst_1435_);
lean_dec(v___x_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0___boxed(lean_object* v_x_1439_, lean_object* v_x_1440_){
_start:
{
uint8_t v_res_1441_; lean_object* v_r_1442_; 
v_res_1441_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(v_x_1439_, v_x_1440_);
lean_dec_ref(v_x_1440_);
lean_dec_ref(v_x_1439_);
v_r_1442_ = lean_box(v_res_1441_);
return v_r_1442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg(lean_object* v_hi_1443_, lean_object* v_pivot_1444_, lean_object* v_as_1445_, lean_object* v_i_1446_, lean_object* v_k_1447_){
_start:
{
uint8_t v___x_1448_; 
v___x_1448_ = lean_nat_dec_lt(v_k_1447_, v_hi_1443_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
lean_dec(v_k_1447_);
v___x_1449_ = lean_array_fswap(v_as_1445_, v_i_1446_, v_hi_1443_);
v___x_1450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1450_, 0, v_i_1446_);
lean_ctor_set(v___x_1450_, 1, v___x_1449_);
return v___x_1450_;
}
else
{
lean_object* v___x_1451_; lean_object* v_fst_1452_; lean_object* v_fst_1453_; lean_object* v_fst_1454_; lean_object* v_fst_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; uint8_t v___x_1458_; 
v___x_1451_ = lean_array_fget_borrowed(v_as_1445_, v_k_1447_);
v_fst_1452_ = lean_ctor_get(v___x_1451_, 0);
v_fst_1453_ = lean_ctor_get(v_pivot_1444_, 0);
v_fst_1454_ = lean_ctor_get(v_fst_1452_, 0);
v_fst_1455_ = lean_ctor_get(v_fst_1453_, 0);
v___x_1456_ = lean_unsigned_to_nat(1u);
v___x_1457_ = lean_nat_add(v_fst_1454_, v___x_1456_);
v___x_1458_ = lean_nat_dec_le(v___x_1457_, v_fst_1455_);
lean_dec(v___x_1457_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1459_; 
v___x_1459_ = lean_nat_add(v_k_1447_, v___x_1456_);
lean_dec(v_k_1447_);
v_k_1447_ = v___x_1459_;
goto _start;
}
else
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1461_ = lean_array_fswap(v_as_1445_, v_i_1446_, v_k_1447_);
v___x_1462_ = lean_nat_add(v_i_1446_, v___x_1456_);
lean_dec(v_i_1446_);
v___x_1463_ = lean_nat_add(v_k_1447_, v___x_1456_);
lean_dec(v_k_1447_);
v_as_1445_ = v___x_1461_;
v_i_1446_ = v___x_1462_;
v_k_1447_ = v___x_1463_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg___boxed(lean_object* v_hi_1465_, lean_object* v_pivot_1466_, lean_object* v_as_1467_, lean_object* v_i_1468_, lean_object* v_k_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg(v_hi_1465_, v_pivot_1466_, v_as_1467_, v_i_1468_, v_k_1469_);
lean_dec_ref(v_pivot_1466_);
lean_dec(v_hi_1465_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(lean_object* v_n_1471_, lean_object* v_as_1472_, lean_object* v_lo_1473_, lean_object* v_hi_1474_){
_start:
{
lean_object* v___y_1476_; uint8_t v___x_1486_; 
v___x_1486_ = lean_nat_dec_lt(v_lo_1473_, v_hi_1474_);
if (v___x_1486_ == 0)
{
lean_dec(v_lo_1473_);
return v_as_1472_;
}
else
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v_mid_1489_; lean_object* v___y_1491_; lean_object* v___y_1497_; lean_object* v___x_1502_; lean_object* v___x_1503_; uint8_t v___x_1504_; 
v___x_1487_ = lean_nat_add(v_lo_1473_, v_hi_1474_);
v___x_1488_ = lean_unsigned_to_nat(1u);
v_mid_1489_ = lean_nat_shiftr(v___x_1487_, v___x_1488_);
lean_dec(v___x_1487_);
v___x_1502_ = lean_array_fget_borrowed(v_as_1472_, v_mid_1489_);
v___x_1503_ = lean_array_fget_borrowed(v_as_1472_, v_lo_1473_);
v___x_1504_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(v___x_1502_, v___x_1503_);
if (v___x_1504_ == 0)
{
v___y_1497_ = v_as_1472_;
goto v___jp_1496_;
}
else
{
lean_object* v___x_1505_; 
v___x_1505_ = lean_array_fswap(v_as_1472_, v_lo_1473_, v_mid_1489_);
v___y_1497_ = v___x_1505_;
goto v___jp_1496_;
}
v___jp_1490_:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; uint8_t v___x_1494_; 
v___x_1492_ = lean_array_fget_borrowed(v___y_1491_, v_mid_1489_);
v___x_1493_ = lean_array_fget_borrowed(v___y_1491_, v_hi_1474_);
v___x_1494_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(v___x_1492_, v___x_1493_);
if (v___x_1494_ == 0)
{
lean_dec(v_mid_1489_);
v___y_1476_ = v___y_1491_;
goto v___jp_1475_;
}
else
{
lean_object* v___x_1495_; 
v___x_1495_ = lean_array_fswap(v___y_1491_, v_mid_1489_, v_hi_1474_);
lean_dec(v_mid_1489_);
v___y_1476_ = v___x_1495_;
goto v___jp_1475_;
}
}
v___jp_1496_:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; uint8_t v___x_1500_; 
v___x_1498_ = lean_array_fget_borrowed(v___y_1497_, v_hi_1474_);
v___x_1499_ = lean_array_fget_borrowed(v___y_1497_, v_lo_1473_);
v___x_1500_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(v___x_1498_, v___x_1499_);
if (v___x_1500_ == 0)
{
v___y_1491_ = v___y_1497_;
goto v___jp_1490_;
}
else
{
lean_object* v___x_1501_; 
v___x_1501_ = lean_array_fswap(v___y_1497_, v_lo_1473_, v_hi_1474_);
v___y_1491_ = v___x_1501_;
goto v___jp_1490_;
}
}
}
v___jp_1475_:
{
lean_object* v_pivot_1477_; lean_object* v___x_1478_; lean_object* v_fst_1479_; lean_object* v_snd_1480_; uint8_t v___x_1481_; 
v_pivot_1477_ = lean_array_fget(v___y_1476_, v_hi_1474_);
lean_inc_n(v_lo_1473_, 2);
v___x_1478_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg(v_hi_1474_, v_pivot_1477_, v___y_1476_, v_lo_1473_, v_lo_1473_);
lean_dec(v_pivot_1477_);
v_fst_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_fst_1479_);
v_snd_1480_ = lean_ctor_get(v___x_1478_, 1);
lean_inc(v_snd_1480_);
lean_dec_ref(v___x_1478_);
v___x_1481_ = lean_nat_dec_le(v_hi_1474_, v_fst_1479_);
if (v___x_1481_ == 0)
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1482_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(v_n_1471_, v_snd_1480_, v_lo_1473_, v_fst_1479_);
v___x_1483_ = lean_unsigned_to_nat(1u);
v___x_1484_ = lean_nat_add(v_fst_1479_, v___x_1483_);
lean_dec(v_fst_1479_);
v_as_1472_ = v___x_1482_;
v_lo_1473_ = v___x_1484_;
goto _start;
}
else
{
lean_dec(v_fst_1479_);
lean_dec(v_lo_1473_);
return v_snd_1480_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___boxed(lean_object* v_n_1506_, lean_object* v_as_1507_, lean_object* v_lo_1508_, lean_object* v_hi_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(v_n_1506_, v_as_1507_, v_lo_1508_, v_hi_1509_);
lean_dec(v_hi_1509_);
lean_dec(v_n_1506_);
return v_res_1510_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0(uint8_t v_suppressElabErrors_1511_, uint8_t v___x_1512_, lean_object* v___x_1513_, lean_object* v_x_1514_){
_start:
{
if (lean_obj_tag(v_x_1514_) == 1)
{
lean_object* v_pre_1515_; 
v_pre_1515_ = lean_ctor_get(v_x_1514_, 0);
switch(lean_obj_tag(v_pre_1515_))
{
case 1:
{
lean_object* v_pre_1516_; 
v_pre_1516_ = lean_ctor_get(v_pre_1515_, 0);
switch(lean_obj_tag(v_pre_1516_))
{
case 0:
{
lean_object* v_str_1517_; lean_object* v_str_1518_; lean_object* v___x_1519_; uint8_t v___x_1520_; 
v_str_1517_ = lean_ctor_get(v_x_1514_, 1);
v_str_1518_ = lean_ctor_get(v_pre_1515_, 1);
v___x_1519_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__0));
v___x_1520_ = lean_string_dec_eq(v_str_1518_, v___x_1519_);
if (v___x_1520_ == 0)
{
lean_object* v___x_1521_; uint8_t v___x_1522_; 
v___x_1521_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__1));
v___x_1522_ = lean_string_dec_eq(v_str_1518_, v___x_1521_);
if (v___x_1522_ == 0)
{
return v___x_1522_;
}
else
{
lean_object* v___x_1523_; uint8_t v___x_1524_; 
v___x_1523_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__2));
v___x_1524_ = lean_string_dec_eq(v_str_1517_, v___x_1523_);
if (v___x_1524_ == 0)
{
return v___x_1524_;
}
else
{
return v_suppressElabErrors_1511_;
}
}
}
else
{
lean_object* v___x_1525_; uint8_t v___x_1526_; 
v___x_1525_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__3));
v___x_1526_ = lean_string_dec_eq(v_str_1517_, v___x_1525_);
if (v___x_1526_ == 0)
{
return v___x_1526_;
}
else
{
return v_suppressElabErrors_1511_;
}
}
}
case 1:
{
lean_object* v_pre_1527_; 
v_pre_1527_ = lean_ctor_get(v_pre_1516_, 0);
if (lean_obj_tag(v_pre_1527_) == 0)
{
lean_object* v_str_1528_; lean_object* v_str_1529_; lean_object* v_str_1530_; lean_object* v___x_1531_; uint8_t v___x_1532_; 
v_str_1528_ = lean_ctor_get(v_x_1514_, 1);
v_str_1529_ = lean_ctor_get(v_pre_1515_, 1);
v_str_1530_ = lean_ctor_get(v_pre_1516_, 1);
v___x_1531_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__4));
v___x_1532_ = lean_string_dec_eq(v_str_1530_, v___x_1531_);
if (v___x_1532_ == 0)
{
return v___x_1532_;
}
else
{
lean_object* v___x_1533_; uint8_t v___x_1534_; 
v___x_1533_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__5));
v___x_1534_ = lean_string_dec_eq(v_str_1529_, v___x_1533_);
if (v___x_1534_ == 0)
{
return v___x_1534_;
}
else
{
lean_object* v___x_1535_; uint8_t v___x_1536_; 
v___x_1535_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__6));
v___x_1536_ = lean_string_dec_eq(v_str_1528_, v___x_1535_);
if (v___x_1536_ == 0)
{
return v___x_1536_;
}
else
{
return v_suppressElabErrors_1511_;
}
}
}
}
else
{
return v___x_1512_;
}
}
default: 
{
return v___x_1512_;
}
}
}
case 0:
{
lean_object* v_str_1537_; uint8_t v___x_1538_; 
v_str_1537_ = lean_ctor_get(v_x_1514_, 1);
v___x_1538_ = lean_string_dec_eq(v_str_1537_, v___x_1513_);
if (v___x_1538_ == 0)
{
return v___x_1538_;
}
else
{
return v_suppressElabErrors_1511_;
}
}
default: 
{
return v___x_1512_;
}
}
}
else
{
return v___x_1512_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0___boxed(lean_object* v_suppressElabErrors_1539_, lean_object* v___x_1540_, lean_object* v___x_1541_, lean_object* v_x_1542_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1543_; uint8_t v___x_37404__boxed_1544_; uint8_t v_res_1545_; lean_object* v_r_1546_; 
v_suppressElabErrors_boxed_1543_ = lean_unbox(v_suppressElabErrors_1539_);
v___x_37404__boxed_1544_ = lean_unbox(v___x_1540_);
v_res_1545_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0(v_suppressElabErrors_boxed_1543_, v___x_37404__boxed_1544_, v___x_1541_, v_x_1542_);
lean_dec(v_x_1542_);
lean_dec_ref(v___x_1541_);
v_r_1546_ = lean_box(v_res_1545_);
return v_r_1546_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0(void){
_start:
{
lean_object* v___x_1547_; double v___x_1548_; 
v___x_1547_ = lean_unsigned_to_nat(0u);
v___x_1548_ = lean_float_of_nat(v___x_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20(uint8_t v___x_1549_, lean_object* v_as_1550_, size_t v_sz_1551_, size_t v_i_1552_, lean_object* v_b_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
lean_object* v_a_1558_; uint8_t v___x_1562_; 
v___x_1562_ = lean_usize_dec_lt(v_i_1552_, v_sz_1551_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1563_; 
v___x_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1563_, 0, v_b_1553_);
return v___x_1563_;
}
else
{
lean_object* v_a_1564_; lean_object* v_fst_1565_; lean_object* v_snd_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1645_; 
v_a_1564_ = lean_array_uget(v_as_1550_, v_i_1552_);
v_fst_1565_ = lean_ctor_get(v_a_1564_, 0);
v_snd_1566_ = lean_ctor_get(v_a_1564_, 1);
v_isSharedCheck_1645_ = !lean_is_exclusive(v_a_1564_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1568_ = v_a_1564_;
v_isShared_1569_ = v_isSharedCheck_1645_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_snd_1566_);
lean_inc(v_fst_1565_);
lean_dec(v_a_1564_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1645_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v_fst_1570_; lean_object* v_snd_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1644_; 
v_fst_1570_ = lean_ctor_get(v_fst_1565_, 0);
v_snd_1571_ = lean_ctor_get(v_fst_1565_, 1);
v_isSharedCheck_1644_ = !lean_is_exclusive(v_fst_1565_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1573_ = v_fst_1565_;
v_isShared_1574_ = v_isSharedCheck_1644_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_snd_1571_);
lean_inc(v_fst_1570_);
lean_dec(v_fst_1565_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1644_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; double v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v_toCold_1580_; uint8_t v_suppressElabErrors_1581_; lean_object* v_fileName_1582_; lean_object* v_fileMap_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1590_; 
v___x_1575_ = lean_box(0);
v___x_1576_ = lean_box(0);
v___x_1577_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0);
v___x_1578_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___closed__0));
v___x_1579_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1579_, 0, v___x_1575_);
lean_ctor_set(v___x_1579_, 1, v___x_1576_);
lean_ctor_set(v___x_1579_, 2, v___x_1578_);
lean_ctor_set_float(v___x_1579_, sizeof(void*)*3, v___x_1577_);
lean_ctor_set_float(v___x_1579_, sizeof(void*)*3 + 8, v___x_1577_);
lean_ctor_set_uint8(v___x_1579_, sizeof(void*)*3 + 16, v___x_1562_);
v_toCold_1580_ = lean_ctor_get(v___y_1554_, 0);
v_suppressElabErrors_1581_ = lean_ctor_get_uint8(v___y_1554_, sizeof(void*)*3 + 2);
v_fileName_1582_ = lean_ctor_get(v_toCold_1580_, 0);
v_fileMap_1583_ = lean_ctor_get(v_toCold_1580_, 1);
v___x_1584_ = lean_box(0);
v___x_1585_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_1586_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_1587_ = l_Lean_MessageData_nil;
v___x_1588_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1579_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
lean_ctor_set(v___x_1588_, 2, v_snd_1566_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set_tag(v___x_1573_, 8);
lean_ctor_set(v___x_1573_, 1, v___x_1588_);
lean_ctor_set(v___x_1573_, 0, v___x_1586_);
v___x_1590_ = v___x_1573_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1586_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v___x_1588_);
v___x_1590_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
uint8_t v___x_1591_; lean_object* v___x_1592_; lean_object* v___y_1594_; lean_object* v___y_1595_; 
v___x_1591_ = 0;
lean_inc_ref(v_fileMap_1583_);
lean_inc_ref(v_fileName_1582_);
v___x_1592_ = l_Lean_Elab_mkMessageCore(v_fileName_1582_, v_fileMap_1583_, v___x_1590_, v___x_1591_, v_fst_1570_, v_snd_1571_);
lean_dec(v_snd_1571_);
lean_dec(v_fst_1570_);
if (v_suppressElabErrors_1581_ == 0)
{
v___y_1594_ = v___y_1554_;
v___y_1595_ = v___y_1555_;
goto v___jp_1593_;
}
else
{
lean_object* v_data_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___f_1641_; uint8_t v___x_1642_; 
v_data_1638_ = lean_ctor_get(v___x_1592_, 4);
lean_inc(v_data_1638_);
v___x_1639_ = lean_box(v_suppressElabErrors_1581_);
v___x_1640_ = lean_box(v___x_1549_);
v___f_1641_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1641_, 0, v___x_1639_);
lean_closure_set(v___f_1641_, 1, v___x_1640_);
lean_closure_set(v___f_1641_, 2, v___x_1585_);
v___x_1642_ = l_Lean_MessageData_hasTag(v___f_1641_, v_data_1638_);
if (v___x_1642_ == 0)
{
lean_dec_ref(v___x_1592_);
lean_del_object(v___x_1568_);
v_a_1558_ = v___x_1584_;
goto v___jp_1557_;
}
else
{
v___y_1594_ = v___y_1554_;
v___y_1595_ = v___y_1555_;
goto v___jp_1593_;
}
}
v___jp_1593_:
{
lean_object* v_toCold_1596_; lean_object* v_fileName_1597_; lean_object* v_pos_1598_; lean_object* v_endPos_1599_; uint8_t v_keepFullRange_1600_; uint8_t v_severity_1601_; uint8_t v_isSilent_1602_; lean_object* v_caption_1603_; lean_object* v_data_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1637_; 
v_toCold_1596_ = lean_ctor_get(v___y_1594_, 0);
v_fileName_1597_ = lean_ctor_get(v___x_1592_, 0);
v_pos_1598_ = lean_ctor_get(v___x_1592_, 1);
v_endPos_1599_ = lean_ctor_get(v___x_1592_, 2);
v_keepFullRange_1600_ = lean_ctor_get_uint8(v___x_1592_, sizeof(void*)*5);
v_severity_1601_ = lean_ctor_get_uint8(v___x_1592_, sizeof(void*)*5 + 1);
v_isSilent_1602_ = lean_ctor_get_uint8(v___x_1592_, sizeof(void*)*5 + 2);
v_caption_1603_ = lean_ctor_get(v___x_1592_, 3);
v_data_1604_ = lean_ctor_get(v___x_1592_, 4);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1606_ = v___x_1592_;
v_isShared_1607_ = v_isSharedCheck_1637_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_data_1604_);
lean_inc(v_caption_1603_);
lean_inc(v_endPos_1599_);
lean_inc(v_pos_1598_);
lean_inc(v_fileName_1597_);
lean_dec(v___x_1592_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1637_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v_currNamespace_1608_; lean_object* v_openDecls_1609_; lean_object* v___x_1611_; 
v_currNamespace_1608_ = lean_ctor_get(v_toCold_1596_, 4);
v_openDecls_1609_ = lean_ctor_get(v_toCold_1596_, 5);
lean_inc(v_openDecls_1609_);
lean_inc(v_currNamespace_1608_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 1, v_openDecls_1609_);
lean_ctor_set(v___x_1568_, 0, v_currNamespace_1608_);
v___x_1611_ = v___x_1568_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_currNamespace_1608_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_openDecls_1609_);
v___x_1611_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
lean_object* v___x_1612_; lean_object* v___x_1614_; 
v___x_1612_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1611_);
lean_ctor_set(v___x_1612_, 1, v_data_1604_);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 4, v___x_1612_);
v___x_1614_ = v___x_1606_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_fileName_1597_);
lean_ctor_set(v_reuseFailAlloc_1635_, 1, v_pos_1598_);
lean_ctor_set(v_reuseFailAlloc_1635_, 2, v_endPos_1599_);
lean_ctor_set(v_reuseFailAlloc_1635_, 3, v_caption_1603_);
lean_ctor_set(v_reuseFailAlloc_1635_, 4, v___x_1612_);
lean_ctor_set_uint8(v_reuseFailAlloc_1635_, sizeof(void*)*5, v_keepFullRange_1600_);
lean_ctor_set_uint8(v_reuseFailAlloc_1635_, sizeof(void*)*5 + 1, v_severity_1601_);
lean_ctor_set_uint8(v_reuseFailAlloc_1635_, sizeof(void*)*5 + 2, v_isSilent_1602_);
v___x_1614_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
lean_object* v___x_1615_; lean_object* v_env_1616_; lean_object* v_nextMacroScope_1617_; lean_object* v_ngen_1618_; lean_object* v_auxDeclNGen_1619_; lean_object* v_traceState_1620_; lean_object* v_cache_1621_; lean_object* v_recordedDeps_1622_; lean_object* v_messages_1623_; lean_object* v_infoState_1624_; lean_object* v_snapshotTasks_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1634_; 
v___x_1615_ = lean_st_ref_take(v___y_1595_);
v_env_1616_ = lean_ctor_get(v___x_1615_, 0);
v_nextMacroScope_1617_ = lean_ctor_get(v___x_1615_, 1);
v_ngen_1618_ = lean_ctor_get(v___x_1615_, 2);
v_auxDeclNGen_1619_ = lean_ctor_get(v___x_1615_, 3);
v_traceState_1620_ = lean_ctor_get(v___x_1615_, 4);
v_cache_1621_ = lean_ctor_get(v___x_1615_, 5);
v_recordedDeps_1622_ = lean_ctor_get(v___x_1615_, 6);
v_messages_1623_ = lean_ctor_get(v___x_1615_, 7);
v_infoState_1624_ = lean_ctor_get(v___x_1615_, 8);
v_snapshotTasks_1625_ = lean_ctor_get(v___x_1615_, 9);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1627_ = v___x_1615_;
v_isShared_1628_ = v_isSharedCheck_1634_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_snapshotTasks_1625_);
lean_inc(v_infoState_1624_);
lean_inc(v_messages_1623_);
lean_inc(v_recordedDeps_1622_);
lean_inc(v_cache_1621_);
lean_inc(v_traceState_1620_);
lean_inc(v_auxDeclNGen_1619_);
lean_inc(v_ngen_1618_);
lean_inc(v_nextMacroScope_1617_);
lean_inc(v_env_1616_);
lean_dec(v___x_1615_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1634_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1629_; lean_object* v___x_1631_; 
v___x_1629_ = l_Lean_MessageLog_add(v___x_1614_, v_messages_1623_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 7, v___x_1629_);
v___x_1631_ = v___x_1627_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_env_1616_);
lean_ctor_set(v_reuseFailAlloc_1633_, 1, v_nextMacroScope_1617_);
lean_ctor_set(v_reuseFailAlloc_1633_, 2, v_ngen_1618_);
lean_ctor_set(v_reuseFailAlloc_1633_, 3, v_auxDeclNGen_1619_);
lean_ctor_set(v_reuseFailAlloc_1633_, 4, v_traceState_1620_);
lean_ctor_set(v_reuseFailAlloc_1633_, 5, v_cache_1621_);
lean_ctor_set(v_reuseFailAlloc_1633_, 6, v_recordedDeps_1622_);
lean_ctor_set(v_reuseFailAlloc_1633_, 7, v___x_1629_);
lean_ctor_set(v_reuseFailAlloc_1633_, 8, v_infoState_1624_);
lean_ctor_set(v_reuseFailAlloc_1633_, 9, v_snapshotTasks_1625_);
v___x_1631_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
lean_object* v___x_1632_; 
v___x_1632_ = lean_st_ref_put(v___y_1595_, v___x_1631_);
v_a_1558_ = v___x_1584_;
goto v___jp_1557_;
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
v___jp_1557_:
{
size_t v___x_1559_; size_t v___x_1560_; 
v___x_1559_ = ((size_t)1ULL);
v___x_1560_ = lean_usize_add(v_i_1552_, v___x_1559_);
v_i_1552_ = v___x_1560_;
v_b_1553_ = v_a_1558_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___boxed(lean_object* v___x_1646_, lean_object* v_as_1647_, lean_object* v_sz_1648_, lean_object* v_i_1649_, lean_object* v_b_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
uint8_t v___x_37469__boxed_1654_; size_t v_sz_boxed_1655_; size_t v_i_boxed_1656_; lean_object* v_res_1657_; 
v___x_37469__boxed_1654_ = lean_unbox(v___x_1646_);
v_sz_boxed_1655_ = lean_unbox_usize(v_sz_1648_);
lean_dec(v_sz_1648_);
v_i_boxed_1656_ = lean_unbox_usize(v_i_1649_);
lean_dec(v_i_1649_);
v_res_1657_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20(v___x_37469__boxed_1654_, v_as_1647_, v_sz_boxed_1655_, v_i_boxed_1656_, v_b_1650_, v___y_1651_, v___y_1652_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec_ref(v_as_1647_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg(lean_object* v_a_1658_, lean_object* v_fallback_1659_, lean_object* v_x_1660_){
_start:
{
if (lean_obj_tag(v_x_1660_) == 0)
{
lean_inc(v_fallback_1659_);
return v_fallback_1659_;
}
else
{
lean_object* v_key_1661_; lean_object* v_value_1662_; lean_object* v_tail_1663_; lean_object* v_fst_1664_; lean_object* v_snd_1665_; lean_object* v_fst_1666_; lean_object* v_snd_1667_; uint8_t v_decide_1668_; 
v_key_1661_ = lean_ctor_get(v_x_1660_, 0);
v_value_1662_ = lean_ctor_get(v_x_1660_, 1);
v_tail_1663_ = lean_ctor_get(v_x_1660_, 2);
v_fst_1664_ = lean_ctor_get(v_key_1661_, 0);
v_snd_1665_ = lean_ctor_get(v_key_1661_, 1);
v_fst_1666_ = lean_ctor_get(v_a_1658_, 0);
v_snd_1667_ = lean_ctor_get(v_a_1658_, 1);
v_decide_1668_ = lean_nat_dec_eq(v_fst_1664_, v_fst_1666_);
if (v_decide_1668_ == 0)
{
v_x_1660_ = v_tail_1663_;
goto _start;
}
else
{
uint8_t v_decide_1670_; 
v_decide_1670_ = lean_nat_dec_eq(v_snd_1665_, v_snd_1667_);
if (v_decide_1670_ == 0)
{
v_x_1660_ = v_tail_1663_;
goto _start;
}
else
{
lean_inc(v_value_1662_);
return v_value_1662_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg___boxed(lean_object* v_a_1672_, lean_object* v_fallback_1673_, lean_object* v_x_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg(v_a_1672_, v_fallback_1673_, v_x_1674_);
lean_dec(v_x_1674_);
lean_dec(v_fallback_1673_);
lean_dec_ref(v_a_1672_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(lean_object* v_m_1676_, lean_object* v_a_1677_, lean_object* v_fallback_1678_){
_start:
{
lean_object* v_buckets_1679_; lean_object* v_fst_1680_; lean_object* v_snd_1681_; lean_object* v___x_1682_; uint64_t v___x_1683_; uint64_t v___x_1684_; uint64_t v___x_1685_; uint64_t v___x_1686_; uint64_t v___x_1687_; uint64_t v_fold_1688_; uint64_t v___x_1689_; uint64_t v___x_1690_; uint64_t v___x_1691_; size_t v___x_1692_; size_t v___x_1693_; size_t v___x_1694_; size_t v___x_1695_; size_t v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v_buckets_1679_ = lean_ctor_get(v_m_1676_, 1);
v_fst_1680_ = lean_ctor_get(v_a_1677_, 0);
v_snd_1681_ = lean_ctor_get(v_a_1677_, 1);
v___x_1682_ = lean_array_get_size(v_buckets_1679_);
v___x_1683_ = l_String_instHashableRaw_hash(v_fst_1680_);
v___x_1684_ = l_String_instHashableRaw_hash(v_snd_1681_);
v___x_1685_ = lean_uint64_mix_hash(v___x_1683_, v___x_1684_);
v___x_1686_ = 32ULL;
v___x_1687_ = lean_uint64_shift_right(v___x_1685_, v___x_1686_);
v_fold_1688_ = lean_uint64_xor(v___x_1685_, v___x_1687_);
v___x_1689_ = 16ULL;
v___x_1690_ = lean_uint64_shift_right(v_fold_1688_, v___x_1689_);
v___x_1691_ = lean_uint64_xor(v_fold_1688_, v___x_1690_);
v___x_1692_ = lean_uint64_to_usize(v___x_1691_);
v___x_1693_ = lean_usize_of_nat(v___x_1682_);
v___x_1694_ = ((size_t)1ULL);
v___x_1695_ = lean_usize_sub(v___x_1693_, v___x_1694_);
v___x_1696_ = lean_usize_land(v___x_1692_, v___x_1695_);
v___x_1697_ = lean_array_uget_borrowed(v_buckets_1679_, v___x_1696_);
v___x_1698_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg(v_a_1677_, v_fallback_1678_, v___x_1697_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg___boxed(lean_object* v_m_1699_, lean_object* v_a_1700_, lean_object* v_fallback_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_m_1699_, v_a_1700_, v_fallback_1701_);
lean_dec(v_fallback_1701_);
lean_dec_ref(v_a_1700_);
lean_dec_ref(v_m_1699_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35_spec__44___redArg(lean_object* v_x_1703_, lean_object* v_x_1704_){
_start:
{
if (lean_obj_tag(v_x_1704_) == 0)
{
return v_x_1703_;
}
else
{
lean_object* v_key_1705_; lean_object* v_value_1706_; lean_object* v_tail_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1734_; 
v_key_1705_ = lean_ctor_get(v_x_1704_, 0);
v_value_1706_ = lean_ctor_get(v_x_1704_, 1);
v_tail_1707_ = lean_ctor_get(v_x_1704_, 2);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_x_1704_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1709_ = v_x_1704_;
v_isShared_1710_ = v_isSharedCheck_1734_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_tail_1707_);
lean_inc(v_value_1706_);
lean_inc(v_key_1705_);
lean_dec(v_x_1704_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1734_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v_fst_1711_; lean_object* v_snd_1712_; lean_object* v___x_1713_; uint64_t v___x_1714_; uint64_t v___x_1715_; uint64_t v___x_1716_; uint64_t v___x_1717_; uint64_t v___x_1718_; uint64_t v_fold_1719_; uint64_t v___x_1720_; uint64_t v___x_1721_; uint64_t v___x_1722_; size_t v___x_1723_; size_t v___x_1724_; size_t v___x_1725_; size_t v___x_1726_; size_t v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1730_; 
v_fst_1711_ = lean_ctor_get(v_key_1705_, 0);
v_snd_1712_ = lean_ctor_get(v_key_1705_, 1);
v___x_1713_ = lean_array_get_size(v_x_1703_);
v___x_1714_ = l_String_instHashableRaw_hash(v_fst_1711_);
v___x_1715_ = l_String_instHashableRaw_hash(v_snd_1712_);
v___x_1716_ = lean_uint64_mix_hash(v___x_1714_, v___x_1715_);
v___x_1717_ = 32ULL;
v___x_1718_ = lean_uint64_shift_right(v___x_1716_, v___x_1717_);
v_fold_1719_ = lean_uint64_xor(v___x_1716_, v___x_1718_);
v___x_1720_ = 16ULL;
v___x_1721_ = lean_uint64_shift_right(v_fold_1719_, v___x_1720_);
v___x_1722_ = lean_uint64_xor(v_fold_1719_, v___x_1721_);
v___x_1723_ = lean_uint64_to_usize(v___x_1722_);
v___x_1724_ = lean_usize_of_nat(v___x_1713_);
v___x_1725_ = ((size_t)1ULL);
v___x_1726_ = lean_usize_sub(v___x_1724_, v___x_1725_);
v___x_1727_ = lean_usize_land(v___x_1723_, v___x_1726_);
v___x_1728_ = lean_array_uget_borrowed(v_x_1703_, v___x_1727_);
lean_inc(v___x_1728_);
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 2, v___x_1728_);
v___x_1730_ = v___x_1709_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_key_1705_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v_value_1706_);
lean_ctor_set(v_reuseFailAlloc_1733_, 2, v___x_1728_);
v___x_1730_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
lean_object* v___x_1731_; 
v___x_1731_ = lean_array_uset(v_x_1703_, v___x_1727_, v___x_1730_);
v_x_1703_ = v___x_1731_;
v_x_1704_ = v_tail_1707_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35___redArg(lean_object* v_i_1735_, lean_object* v_source_1736_, lean_object* v_target_1737_){
_start:
{
lean_object* v___x_1738_; uint8_t v___x_1739_; 
v___x_1738_ = lean_array_get_size(v_source_1736_);
v___x_1739_ = lean_nat_dec_lt(v_i_1735_, v___x_1738_);
if (v___x_1739_ == 0)
{
lean_dec_ref(v_source_1736_);
lean_dec(v_i_1735_);
return v_target_1737_;
}
else
{
lean_object* v_es_1740_; lean_object* v___x_1741_; lean_object* v_source_1742_; lean_object* v_target_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v_es_1740_ = lean_array_fget(v_source_1736_, v_i_1735_);
v___x_1741_ = lean_box(0);
v_source_1742_ = lean_array_fset(v_source_1736_, v_i_1735_, v___x_1741_);
v_target_1743_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35_spec__44___redArg(v_target_1737_, v_es_1740_);
v___x_1744_ = lean_unsigned_to_nat(1u);
v___x_1745_ = lean_nat_add(v_i_1735_, v___x_1744_);
lean_dec(v_i_1735_);
v_i_1735_ = v___x_1745_;
v_source_1736_ = v_source_1742_;
v_target_1737_ = v_target_1743_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24___redArg(lean_object* v_data_1747_){
_start:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v_nbuckets_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1748_ = lean_array_get_size(v_data_1747_);
v___x_1749_ = lean_unsigned_to_nat(2u);
v_nbuckets_1750_ = lean_nat_mul(v___x_1748_, v___x_1749_);
v___x_1751_ = lean_unsigned_to_nat(0u);
v___x_1752_ = lean_box(0);
v___x_1753_ = lean_mk_array(v_nbuckets_1750_, v___x_1752_);
v___x_1754_ = lean_array_propagate_mark(v_data_1747_, v___x_1753_);
v___x_1755_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35___redArg(v___x_1751_, v_data_1747_, v___x_1754_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25___redArg(lean_object* v_a_1756_, lean_object* v_b_1757_, lean_object* v_x_1758_){
_start:
{
if (lean_obj_tag(v_x_1758_) == 0)
{
lean_dec(v_b_1757_);
lean_dec_ref(v_a_1756_);
return v_x_1758_;
}
else
{
lean_object* v_key_1759_; lean_object* v_value_1760_; lean_object* v_tail_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1777_; 
v_key_1759_ = lean_ctor_get(v_x_1758_, 0);
v_value_1760_ = lean_ctor_get(v_x_1758_, 1);
v_tail_1761_ = lean_ctor_get(v_x_1758_, 2);
v_isSharedCheck_1777_ = !lean_is_exclusive(v_x_1758_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1763_ = v_x_1758_;
v_isShared_1764_ = v_isSharedCheck_1777_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_tail_1761_);
lean_inc(v_value_1760_);
lean_inc(v_key_1759_);
lean_dec(v_x_1758_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1777_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v_fst_1770_; lean_object* v_snd_1771_; lean_object* v_fst_1772_; lean_object* v_snd_1773_; uint8_t v_decide_1774_; 
v_fst_1770_ = lean_ctor_get(v_key_1759_, 0);
v_snd_1771_ = lean_ctor_get(v_key_1759_, 1);
v_fst_1772_ = lean_ctor_get(v_a_1756_, 0);
v_snd_1773_ = lean_ctor_get(v_a_1756_, 1);
v_decide_1774_ = lean_nat_dec_eq(v_fst_1770_, v_fst_1772_);
if (v_decide_1774_ == 0)
{
goto v___jp_1765_;
}
else
{
uint8_t v_decide_1775_; 
v_decide_1775_ = lean_nat_dec_eq(v_snd_1771_, v_snd_1773_);
if (v_decide_1775_ == 0)
{
goto v___jp_1765_;
}
else
{
lean_object* v___x_1776_; 
lean_del_object(v___x_1763_);
lean_dec(v_value_1760_);
lean_dec(v_key_1759_);
v___x_1776_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1776_, 0, v_a_1756_);
lean_ctor_set(v___x_1776_, 1, v_b_1757_);
lean_ctor_set(v___x_1776_, 2, v_tail_1761_);
return v___x_1776_;
}
}
v___jp_1765_:
{
lean_object* v___x_1766_; lean_object* v___x_1768_; 
v___x_1766_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25___redArg(v_a_1756_, v_b_1757_, v_tail_1761_);
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 2, v___x_1766_);
v___x_1768_ = v___x_1763_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_key_1759_);
lean_ctor_set(v_reuseFailAlloc_1769_, 1, v_value_1760_);
lean_ctor_set(v_reuseFailAlloc_1769_, 2, v___x_1766_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg(lean_object* v_a_1778_, lean_object* v_x_1779_){
_start:
{
if (lean_obj_tag(v_x_1779_) == 0)
{
uint8_t v___x_1780_; 
v___x_1780_ = 0;
return v___x_1780_;
}
else
{
lean_object* v_key_1781_; lean_object* v_tail_1782_; lean_object* v_fst_1783_; lean_object* v_snd_1784_; lean_object* v_fst_1785_; lean_object* v_snd_1786_; uint8_t v_decide_1787_; 
v_key_1781_ = lean_ctor_get(v_x_1779_, 0);
v_tail_1782_ = lean_ctor_get(v_x_1779_, 2);
v_fst_1783_ = lean_ctor_get(v_key_1781_, 0);
v_snd_1784_ = lean_ctor_get(v_key_1781_, 1);
v_fst_1785_ = lean_ctor_get(v_a_1778_, 0);
v_snd_1786_ = lean_ctor_get(v_a_1778_, 1);
v_decide_1787_ = lean_nat_dec_eq(v_fst_1783_, v_fst_1785_);
if (v_decide_1787_ == 0)
{
v_x_1779_ = v_tail_1782_;
goto _start;
}
else
{
uint8_t v_decide_1789_; 
v_decide_1789_ = lean_nat_dec_eq(v_snd_1784_, v_snd_1786_);
if (v_decide_1789_ == 0)
{
v_x_1779_ = v_tail_1782_;
goto _start;
}
else
{
return v_decide_1789_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg___boxed(lean_object* v_a_1791_, lean_object* v_x_1792_){
_start:
{
uint8_t v_res_1793_; lean_object* v_r_1794_; 
v_res_1793_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg(v_a_1791_, v_x_1792_);
lean_dec(v_x_1792_);
lean_dec_ref(v_a_1791_);
v_r_1794_ = lean_box(v_res_1793_);
return v_r_1794_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(lean_object* v_m_1795_, lean_object* v_a_1796_, lean_object* v_b_1797_){
_start:
{
lean_object* v_size_1798_; lean_object* v_buckets_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1846_; 
v_size_1798_ = lean_ctor_get(v_m_1795_, 0);
v_buckets_1799_ = lean_ctor_get(v_m_1795_, 1);
v_isSharedCheck_1846_ = !lean_is_exclusive(v_m_1795_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1801_ = v_m_1795_;
v_isShared_1802_ = v_isSharedCheck_1846_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_buckets_1799_);
lean_inc(v_size_1798_);
lean_dec(v_m_1795_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1846_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v_fst_1803_; lean_object* v_snd_1804_; lean_object* v___x_1805_; uint64_t v___x_1806_; uint64_t v___x_1807_; uint64_t v___x_1808_; uint64_t v___x_1809_; uint64_t v___x_1810_; uint64_t v_fold_1811_; uint64_t v___x_1812_; uint64_t v___x_1813_; uint64_t v___x_1814_; size_t v___x_1815_; size_t v___x_1816_; size_t v___x_1817_; size_t v___x_1818_; size_t v___x_1819_; lean_object* v_bkt_1820_; uint8_t v___x_1821_; 
v_fst_1803_ = lean_ctor_get(v_a_1796_, 0);
v_snd_1804_ = lean_ctor_get(v_a_1796_, 1);
v___x_1805_ = lean_array_get_size(v_buckets_1799_);
v___x_1806_ = l_String_instHashableRaw_hash(v_fst_1803_);
v___x_1807_ = l_String_instHashableRaw_hash(v_snd_1804_);
v___x_1808_ = lean_uint64_mix_hash(v___x_1806_, v___x_1807_);
v___x_1809_ = 32ULL;
v___x_1810_ = lean_uint64_shift_right(v___x_1808_, v___x_1809_);
v_fold_1811_ = lean_uint64_xor(v___x_1808_, v___x_1810_);
v___x_1812_ = 16ULL;
v___x_1813_ = lean_uint64_shift_right(v_fold_1811_, v___x_1812_);
v___x_1814_ = lean_uint64_xor(v_fold_1811_, v___x_1813_);
v___x_1815_ = lean_uint64_to_usize(v___x_1814_);
v___x_1816_ = lean_usize_of_nat(v___x_1805_);
v___x_1817_ = ((size_t)1ULL);
v___x_1818_ = lean_usize_sub(v___x_1816_, v___x_1817_);
v___x_1819_ = lean_usize_land(v___x_1815_, v___x_1818_);
v_bkt_1820_ = lean_array_uget_borrowed(v_buckets_1799_, v___x_1819_);
v___x_1821_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg(v_a_1796_, v_bkt_1820_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; lean_object* v_size_x27_1823_; lean_object* v___x_1824_; lean_object* v_buckets_x27_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; uint8_t v___x_1831_; 
v___x_1822_ = lean_unsigned_to_nat(1u);
v_size_x27_1823_ = lean_nat_add(v_size_1798_, v___x_1822_);
lean_dec(v_size_1798_);
lean_inc(v_bkt_1820_);
v___x_1824_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1824_, 0, v_a_1796_);
lean_ctor_set(v___x_1824_, 1, v_b_1797_);
lean_ctor_set(v___x_1824_, 2, v_bkt_1820_);
v_buckets_x27_1825_ = lean_array_uset(v_buckets_1799_, v___x_1819_, v___x_1824_);
v___x_1826_ = lean_unsigned_to_nat(4u);
v___x_1827_ = lean_nat_mul(v_size_x27_1823_, v___x_1826_);
v___x_1828_ = lean_unsigned_to_nat(3u);
v___x_1829_ = lean_nat_div(v___x_1827_, v___x_1828_);
lean_dec(v___x_1827_);
v___x_1830_ = lean_array_get_size(v_buckets_x27_1825_);
v___x_1831_ = lean_nat_dec_le(v___x_1829_, v___x_1830_);
lean_dec(v___x_1829_);
if (v___x_1831_ == 0)
{
lean_object* v_val_1832_; lean_object* v___x_1834_; 
v_val_1832_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24___redArg(v_buckets_x27_1825_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 1, v_val_1832_);
lean_ctor_set(v___x_1801_, 0, v_size_x27_1823_);
v___x_1834_ = v___x_1801_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_size_x27_1823_);
lean_ctor_set(v_reuseFailAlloc_1835_, 1, v_val_1832_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
else
{
lean_object* v___x_1837_; 
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 1, v_buckets_x27_1825_);
lean_ctor_set(v___x_1801_, 0, v_size_x27_1823_);
v___x_1837_ = v___x_1801_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_size_x27_1823_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v_buckets_x27_1825_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
else
{
lean_object* v___x_1839_; lean_object* v_buckets_x27_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1844_; 
lean_inc(v_bkt_1820_);
v___x_1839_ = lean_box(0);
v_buckets_x27_1840_ = lean_array_uset(v_buckets_1799_, v___x_1819_, v___x_1839_);
v___x_1841_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25___redArg(v_a_1796_, v_b_1797_, v_bkt_1820_);
v___x_1842_ = lean_array_uset(v_buckets_x27_1840_, v___x_1819_, v___x_1841_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 1, v___x_1842_);
v___x_1844_ = v___x_1801_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_size_1798_);
lean_ctor_set(v_reuseFailAlloc_1845_, 1, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg(uint8_t v___x_1849_, lean_object* v_as_1850_, size_t v_sz_1851_, size_t v_i_1852_, lean_object* v_b_1853_, lean_object* v___y_1854_){
_start:
{
uint8_t v___x_1856_; 
v___x_1856_ = lean_usize_dec_lt(v_i_1852_, v_sz_1851_);
if (v___x_1856_ == 0)
{
lean_object* v___x_1857_; 
v___x_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1857_, 0, v_b_1853_);
return v___x_1857_;
}
else
{
lean_object* v_snd_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1895_; 
v_snd_1858_ = lean_ctor_get(v_b_1853_, 1);
v_isSharedCheck_1895_ = !lean_is_exclusive(v_b_1853_);
if (v_isSharedCheck_1895_ == 0)
{
lean_object* v_unused_1896_; 
v_unused_1896_ = lean_ctor_get(v_b_1853_, 0);
lean_dec(v_unused_1896_);
v___x_1860_ = v_b_1853_;
v_isShared_1861_ = v_isSharedCheck_1895_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_snd_1858_);
lean_dec(v_b_1853_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1895_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v_ref_1862_; lean_object* v_a_1863_; lean_object* v_ref_1864_; lean_object* v_msg_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1894_; 
v_ref_1862_ = lean_ctor_get(v___y_1854_, 2);
v_a_1863_ = lean_array_uget(v_as_1850_, v_i_1852_);
v_ref_1864_ = lean_ctor_get(v_a_1863_, 0);
v_msg_1865_ = lean_ctor_get(v_a_1863_, 1);
v_isSharedCheck_1894_ = !lean_is_exclusive(v_a_1863_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1867_ = v_a_1863_;
v_isShared_1868_ = v_isSharedCheck_1894_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_msg_1865_);
lean_inc(v_ref_1864_);
lean_dec(v_a_1863_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1894_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1869_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v_ref_1886_; lean_object* v___y_1888_; lean_object* v___x_1891_; 
v___x_1869_ = lean_box(0);
v_ref_1886_ = l_Lean_replaceRef(v_ref_1864_, v_ref_1862_);
lean_dec(v_ref_1864_);
v___x_1891_ = l_Lean_Syntax_getPos_x3f(v_ref_1886_, v___x_1849_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v___x_1892_; 
v___x_1892_ = lean_unsigned_to_nat(0u);
v___y_1888_ = v___x_1892_;
goto v___jp_1887_;
}
else
{
lean_object* v_val_1893_; 
v_val_1893_ = lean_ctor_get(v___x_1891_, 0);
lean_inc(v_val_1893_);
lean_dec_ref_known(v___x_1891_, 1);
v___y_1888_ = v_val_1893_;
goto v___jp_1887_;
}
v___jp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1861_ == 0)
{
lean_ctor_set(v___x_1860_, 1, v___y_1872_);
lean_ctor_set(v___x_1860_, 0, v___y_1871_);
v___x_1874_ = v___x_1860_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___y_1871_);
lean_ctor_set(v_reuseFailAlloc_1885_, 1, v___y_1872_);
v___x_1874_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v_pos2traces_1878_; lean_object* v___x_1880_; 
v___x_1875_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1876_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_1858_, v___x_1874_, v___x_1875_);
v___x_1877_ = lean_array_push(v___x_1876_, v_msg_1865_);
v_pos2traces_1878_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(v_snd_1858_, v___x_1874_, v___x_1877_);
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 1, v_pos2traces_1878_);
lean_ctor_set(v___x_1867_, 0, v___x_1869_);
v___x_1880_ = v___x_1867_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1869_);
lean_ctor_set(v_reuseFailAlloc_1884_, 1, v_pos2traces_1878_);
v___x_1880_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
size_t v___x_1881_; size_t v___x_1882_; 
v___x_1881_ = ((size_t)1ULL);
v___x_1882_ = lean_usize_add(v_i_1852_, v___x_1881_);
v_i_1852_ = v___x_1882_;
v_b_1853_ = v___x_1880_;
goto _start;
}
}
}
v___jp_1887_:
{
lean_object* v___x_1889_; 
v___x_1889_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1886_, v___x_1849_);
lean_dec(v_ref_1886_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_inc(v___y_1888_);
v___y_1871_ = v___y_1888_;
v___y_1872_ = v___y_1888_;
goto v___jp_1870_;
}
else
{
lean_object* v_val_1890_; 
v_val_1890_ = lean_ctor_get(v___x_1889_, 0);
lean_inc(v_val_1890_);
lean_dec_ref_known(v___x_1889_, 1);
v___y_1871_ = v___y_1888_;
v___y_1872_ = v_val_1890_;
goto v___jp_1870_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___boxed(lean_object* v___x_1897_, lean_object* v_as_1898_, lean_object* v_sz_1899_, lean_object* v_i_1900_, lean_object* v_b_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
uint8_t v___x_37915__boxed_1904_; size_t v_sz_boxed_1905_; size_t v_i_boxed_1906_; lean_object* v_res_1907_; 
v___x_37915__boxed_1904_ = lean_unbox(v___x_1897_);
v_sz_boxed_1905_ = lean_unbox_usize(v_sz_1899_);
lean_dec(v_sz_1899_);
v_i_boxed_1906_ = lean_unbox_usize(v_i_1900_);
lean_dec(v_i_1900_);
v_res_1907_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg(v___x_37915__boxed_1904_, v_as_1898_, v_sz_boxed_1905_, v_i_boxed_1906_, v_b_1901_, v___y_1902_);
lean_dec_ref(v___y_1902_);
lean_dec_ref(v_as_1898_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40(uint8_t v___x_1908_, lean_object* v_as_1909_, size_t v_sz_1910_, size_t v_i_1911_, lean_object* v_b_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
uint8_t v___x_1916_; 
v___x_1916_ = lean_usize_dec_lt(v_i_1911_, v_sz_1910_);
if (v___x_1916_ == 0)
{
lean_object* v___x_1917_; 
v___x_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1917_, 0, v_b_1912_);
return v___x_1917_;
}
else
{
lean_object* v_snd_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1955_; 
v_snd_1918_ = lean_ctor_get(v_b_1912_, 1);
v_isSharedCheck_1955_ = !lean_is_exclusive(v_b_1912_);
if (v_isSharedCheck_1955_ == 0)
{
lean_object* v_unused_1956_; 
v_unused_1956_ = lean_ctor_get(v_b_1912_, 0);
lean_dec(v_unused_1956_);
v___x_1920_ = v_b_1912_;
v_isShared_1921_ = v_isSharedCheck_1955_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_snd_1918_);
lean_dec(v_b_1912_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1955_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v_ref_1922_; lean_object* v_a_1923_; lean_object* v_ref_1924_; lean_object* v_msg_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1954_; 
v_ref_1922_ = lean_ctor_get(v___y_1913_, 2);
v_a_1923_ = lean_array_uget(v_as_1909_, v_i_1911_);
v_ref_1924_ = lean_ctor_get(v_a_1923_, 0);
v_msg_1925_ = lean_ctor_get(v_a_1923_, 1);
v_isSharedCheck_1954_ = !lean_is_exclusive(v_a_1923_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1927_ = v_a_1923_;
v_isShared_1928_ = v_isSharedCheck_1954_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_msg_1925_);
lean_inc(v_ref_1924_);
lean_dec(v_a_1923_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1954_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1929_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v_ref_1946_; lean_object* v___y_1948_; lean_object* v___x_1951_; 
v___x_1929_ = lean_box(0);
v_ref_1946_ = l_Lean_replaceRef(v_ref_1924_, v_ref_1922_);
lean_dec(v_ref_1924_);
v___x_1951_ = l_Lean_Syntax_getPos_x3f(v_ref_1946_, v___x_1908_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v___x_1952_; 
v___x_1952_ = lean_unsigned_to_nat(0u);
v___y_1948_ = v___x_1952_;
goto v___jp_1947_;
}
else
{
lean_object* v_val_1953_; 
v_val_1953_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_val_1953_);
lean_dec_ref_known(v___x_1951_, 1);
v___y_1948_ = v_val_1953_;
goto v___jp_1947_;
}
v___jp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 1, v___y_1932_);
lean_ctor_set(v___x_1920_, 0, v___y_1931_);
v___x_1934_ = v___x_1920_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v___y_1931_);
lean_ctor_set(v_reuseFailAlloc_1945_, 1, v___y_1932_);
v___x_1934_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v_pos2traces_1938_; lean_object* v___x_1940_; 
v___x_1935_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1936_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_1918_, v___x_1934_, v___x_1935_);
v___x_1937_ = lean_array_push(v___x_1936_, v_msg_1925_);
v_pos2traces_1938_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(v_snd_1918_, v___x_1934_, v___x_1937_);
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 1, v_pos2traces_1938_);
lean_ctor_set(v___x_1927_, 0, v___x_1929_);
v___x_1940_ = v___x_1927_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1929_);
lean_ctor_set(v_reuseFailAlloc_1944_, 1, v_pos2traces_1938_);
v___x_1940_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
size_t v___x_1941_; size_t v___x_1942_; lean_object* v___x_1943_; 
v___x_1941_ = ((size_t)1ULL);
v___x_1942_ = lean_usize_add(v_i_1911_, v___x_1941_);
v___x_1943_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg(v___x_1908_, v_as_1909_, v_sz_1910_, v___x_1942_, v___x_1940_, v___y_1913_);
return v___x_1943_;
}
}
}
v___jp_1947_:
{
lean_object* v___x_1949_; 
v___x_1949_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1946_, v___x_1908_);
lean_dec(v_ref_1946_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_inc(v___y_1948_);
v___y_1931_ = v___y_1948_;
v___y_1932_ = v___y_1948_;
goto v___jp_1930_;
}
else
{
lean_object* v_val_1950_; 
v_val_1950_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_val_1950_);
lean_dec_ref_known(v___x_1949_, 1);
v___y_1931_ = v___y_1948_;
v___y_1932_ = v_val_1950_;
goto v___jp_1930_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40___boxed(lean_object* v___x_1957_, lean_object* v_as_1958_, lean_object* v_sz_1959_, lean_object* v_i_1960_, lean_object* v_b_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
uint8_t v___x_37996__boxed_1965_; size_t v_sz_boxed_1966_; size_t v_i_boxed_1967_; lean_object* v_res_1968_; 
v___x_37996__boxed_1965_ = lean_unbox(v___x_1957_);
v_sz_boxed_1966_ = lean_unbox_usize(v_sz_1959_);
lean_dec(v_sz_1959_);
v_i_boxed_1967_ = lean_unbox_usize(v_i_1960_);
lean_dec(v_i_1960_);
v_res_1968_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40(v___x_37996__boxed_1965_, v_as_1958_, v_sz_boxed_1966_, v_i_boxed_1967_, v_b_1961_, v___y_1962_, v___y_1963_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec_ref(v_as_1958_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27(lean_object* v_init_1969_, uint8_t v___x_1970_, lean_object* v_n_1971_, lean_object* v_b_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
if (lean_obj_tag(v_n_1971_) == 0)
{
lean_object* v_cs_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; size_t v_sz_1979_; size_t v___x_1980_; lean_object* v___x_1981_; 
v_cs_1976_ = lean_ctor_get(v_n_1971_, 0);
v___x_1977_ = lean_box(0);
v___x_1978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1977_);
lean_ctor_set(v___x_1978_, 1, v_b_1972_);
v_sz_1979_ = lean_array_size(v_cs_1976_);
v___x_1980_ = ((size_t)0ULL);
v___x_1981_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__39(v_init_1969_, v___x_1970_, v_cs_1976_, v_sz_1979_, v___x_1980_, v___x_1978_, v___y_1973_, v___y_1974_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1996_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1984_ = v___x_1981_;
v_isShared_1985_ = v_isSharedCheck_1996_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1981_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1996_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v_fst_1986_; 
v_fst_1986_ = lean_ctor_get(v_a_1982_, 0);
if (lean_obj_tag(v_fst_1986_) == 0)
{
lean_object* v_snd_1987_; lean_object* v___x_1988_; lean_object* v___x_1990_; 
v_snd_1987_ = lean_ctor_get(v_a_1982_, 1);
lean_inc(v_snd_1987_);
lean_dec(v_a_1982_);
v___x_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1988_, 0, v_snd_1987_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 0, v___x_1988_);
v___x_1990_ = v___x_1984_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1988_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
else
{
lean_object* v_val_1992_; lean_object* v___x_1994_; 
lean_inc_ref(v_fst_1986_);
lean_dec(v_a_1982_);
v_val_1992_ = lean_ctor_get(v_fst_1986_, 0);
lean_inc(v_val_1992_);
lean_dec_ref_known(v_fst_1986_, 1);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 0, v_val_1992_);
v___x_1994_ = v___x_1984_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_val_1992_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
else
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2004_; 
v_a_1997_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1999_ = v___x_1981_;
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1981_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_2000_ == 0)
{
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_a_1997_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
else
{
lean_object* v_vs_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; size_t v_sz_2008_; size_t v___x_2009_; lean_object* v___x_2010_; 
v_vs_2005_ = lean_ctor_get(v_n_1971_, 0);
v___x_2006_ = lean_box(0);
v___x_2007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2006_);
lean_ctor_set(v___x_2007_, 1, v_b_1972_);
v_sz_2008_ = lean_array_size(v_vs_2005_);
v___x_2009_ = ((size_t)0ULL);
v___x_2010_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40(v___x_1970_, v_vs_2005_, v_sz_2008_, v___x_2009_, v___x_2007_, v___y_1973_, v___y_1974_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2025_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2013_ = v___x_2010_;
v_isShared_2014_ = v_isSharedCheck_2025_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_2010_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2025_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v_fst_2015_; 
v_fst_2015_ = lean_ctor_get(v_a_2011_, 0);
if (lean_obj_tag(v_fst_2015_) == 0)
{
lean_object* v_snd_2016_; lean_object* v___x_2017_; lean_object* v___x_2019_; 
v_snd_2016_ = lean_ctor_get(v_a_2011_, 1);
lean_inc(v_snd_2016_);
lean_dec(v_a_2011_);
v___x_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2017_, 0, v_snd_2016_);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 0, v___x_2017_);
v___x_2019_ = v___x_2013_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2017_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
else
{
lean_object* v_val_2021_; lean_object* v___x_2023_; 
lean_inc_ref(v_fst_2015_);
lean_dec(v_a_2011_);
v_val_2021_ = lean_ctor_get(v_fst_2015_, 0);
lean_inc(v_val_2021_);
lean_dec_ref_known(v_fst_2015_, 1);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 0, v_val_2021_);
v___x_2023_ = v___x_2013_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_val_2021_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
v_a_2026_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_2010_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_2010_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__39(lean_object* v_init_2034_, uint8_t v___x_2035_, lean_object* v_as_2036_, size_t v_sz_2037_, size_t v_i_2038_, lean_object* v_b_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
uint8_t v___x_2043_; 
v___x_2043_ = lean_usize_dec_lt(v_i_2038_, v_sz_2037_);
if (v___x_2043_ == 0)
{
lean_object* v___x_2044_; 
v___x_2044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2044_, 0, v_b_2039_);
return v___x_2044_;
}
else
{
lean_object* v_snd_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2079_; 
v_snd_2045_ = lean_ctor_get(v_b_2039_, 1);
v_isSharedCheck_2079_ = !lean_is_exclusive(v_b_2039_);
if (v_isSharedCheck_2079_ == 0)
{
lean_object* v_unused_2080_; 
v_unused_2080_ = lean_ctor_get(v_b_2039_, 0);
lean_dec(v_unused_2080_);
v___x_2047_ = v_b_2039_;
v_isShared_2048_ = v_isSharedCheck_2079_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_snd_2045_);
lean_dec(v_b_2039_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2079_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2049_; lean_object* v_a_2050_; lean_object* v___x_2051_; 
v___x_2049_ = lean_box(0);
v_a_2050_ = lean_array_uget_borrowed(v_as_2036_, v_i_2038_);
lean_inc(v_snd_2045_);
v___x_2051_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27(v_init_2034_, v___x_2035_, v_a_2050_, v_snd_2045_, v___y_2040_, v___y_2041_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2070_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2054_ = v___x_2051_;
v_isShared_2055_ = v_isSharedCheck_2070_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2051_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2070_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
if (lean_obj_tag(v_a_2052_) == 0)
{
lean_object* v___x_2056_; lean_object* v___x_2058_; 
v___x_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2056_, 0, v_a_2052_);
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 0, v___x_2056_);
v___x_2058_ = v___x_2047_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v___x_2056_);
lean_ctor_set(v_reuseFailAlloc_2062_, 1, v_snd_2045_);
v___x_2058_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
lean_object* v___x_2060_; 
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 0, v___x_2058_);
v___x_2060_ = v___x_2054_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2058_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; 
lean_del_object(v___x_2054_);
lean_dec(v_snd_2045_);
v_a_2063_ = lean_ctor_get(v_a_2052_, 0);
lean_inc(v_a_2063_);
lean_dec_ref_known(v_a_2052_, 1);
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 1, v_a_2063_);
lean_ctor_set(v___x_2047_, 0, v___x_2049_);
v___x_2065_ = v___x_2047_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2049_);
lean_ctor_set(v_reuseFailAlloc_2069_, 1, v_a_2063_);
v___x_2065_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
size_t v___x_2066_; size_t v___x_2067_; 
v___x_2066_ = ((size_t)1ULL);
v___x_2067_ = lean_usize_add(v_i_2038_, v___x_2066_);
v_i_2038_ = v___x_2067_;
v_b_2039_ = v___x_2065_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
lean_del_object(v___x_2047_);
lean_dec(v_snd_2045_);
v_a_2071_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2073_ = v___x_2051_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2051_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2074_ == 0)
{
v___x_2076_ = v___x_2073_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2071_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__39___boxed(lean_object* v_init_2081_, lean_object* v___x_2082_, lean_object* v_as_2083_, lean_object* v_sz_2084_, lean_object* v_i_2085_, lean_object* v_b_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
uint8_t v___x_38077__boxed_2090_; size_t v_sz_boxed_2091_; size_t v_i_boxed_2092_; lean_object* v_res_2093_; 
v___x_38077__boxed_2090_ = lean_unbox(v___x_2082_);
v_sz_boxed_2091_ = lean_unbox_usize(v_sz_2084_);
lean_dec(v_sz_2084_);
v_i_boxed_2092_ = lean_unbox_usize(v_i_2085_);
lean_dec(v_i_2085_);
v_res_2093_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__39(v_init_2081_, v___x_38077__boxed_2090_, v_as_2083_, v_sz_boxed_2091_, v_i_boxed_2092_, v_b_2086_, v___y_2087_, v___y_2088_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec_ref(v_as_2083_);
lean_dec_ref(v_init_2081_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27___boxed(lean_object* v_init_2094_, lean_object* v___x_2095_, lean_object* v_n_2096_, lean_object* v_b_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
uint8_t v___x_38097__boxed_2101_; lean_object* v_res_2102_; 
v___x_38097__boxed_2101_ = lean_unbox(v___x_2095_);
v_res_2102_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27(v_init_2094_, v___x_38097__boxed_2101_, v_n_2096_, v_b_2097_, v___y_2098_, v___y_2099_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec_ref(v_n_2096_);
lean_dec_ref(v_init_2094_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg(uint8_t v___x_2103_, lean_object* v_as_2104_, size_t v_sz_2105_, size_t v_i_2106_, lean_object* v_b_2107_, lean_object* v___y_2108_){
_start:
{
uint8_t v___x_2110_; 
v___x_2110_ = lean_usize_dec_lt(v_i_2106_, v_sz_2105_);
if (v___x_2110_ == 0)
{
lean_object* v___x_2111_; 
v___x_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2111_, 0, v_b_2107_);
return v___x_2111_;
}
else
{
lean_object* v_snd_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2149_; 
v_snd_2112_ = lean_ctor_get(v_b_2107_, 1);
v_isSharedCheck_2149_ = !lean_is_exclusive(v_b_2107_);
if (v_isSharedCheck_2149_ == 0)
{
lean_object* v_unused_2150_; 
v_unused_2150_ = lean_ctor_get(v_b_2107_, 0);
lean_dec(v_unused_2150_);
v___x_2114_ = v_b_2107_;
v_isShared_2115_ = v_isSharedCheck_2149_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_snd_2112_);
lean_dec(v_b_2107_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2149_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v_ref_2116_; lean_object* v_a_2117_; lean_object* v_ref_2118_; lean_object* v_msg_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2148_; 
v_ref_2116_ = lean_ctor_get(v___y_2108_, 2);
v_a_2117_ = lean_array_uget(v_as_2104_, v_i_2106_);
v_ref_2118_ = lean_ctor_get(v_a_2117_, 0);
v_msg_2119_ = lean_ctor_get(v_a_2117_, 1);
v_isSharedCheck_2148_ = !lean_is_exclusive(v_a_2117_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2121_ = v_a_2117_;
v_isShared_2122_ = v_isSharedCheck_2148_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_msg_2119_);
lean_inc(v_ref_2118_);
lean_dec(v_a_2117_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2148_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2123_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v_ref_2140_; lean_object* v___y_2142_; lean_object* v___x_2145_; 
v___x_2123_ = lean_box(0);
v_ref_2140_ = l_Lean_replaceRef(v_ref_2118_, v_ref_2116_);
lean_dec(v_ref_2118_);
v___x_2145_ = l_Lean_Syntax_getPos_x3f(v_ref_2140_, v___x_2103_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v___x_2146_; 
v___x_2146_ = lean_unsigned_to_nat(0u);
v___y_2142_ = v___x_2146_;
goto v___jp_2141_;
}
else
{
lean_object* v_val_2147_; 
v_val_2147_ = lean_ctor_get(v___x_2145_, 0);
lean_inc(v_val_2147_);
lean_dec_ref_known(v___x_2145_, 1);
v___y_2142_ = v_val_2147_;
goto v___jp_2141_;
}
v___jp_2124_:
{
lean_object* v___x_2128_; 
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 1, v___y_2126_);
lean_ctor_set(v___x_2114_, 0, v___y_2125_);
v___x_2128_ = v___x_2114_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___y_2125_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v___y_2126_);
v___x_2128_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v_pos2traces_2132_; lean_object* v___x_2134_; 
v___x_2129_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_2130_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_2112_, v___x_2128_, v___x_2129_);
v___x_2131_ = lean_array_push(v___x_2130_, v_msg_2119_);
v_pos2traces_2132_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(v_snd_2112_, v___x_2128_, v___x_2131_);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 1, v_pos2traces_2132_);
lean_ctor_set(v___x_2121_, 0, v___x_2123_);
v___x_2134_ = v___x_2121_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___x_2123_);
lean_ctor_set(v_reuseFailAlloc_2138_, 1, v_pos2traces_2132_);
v___x_2134_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
size_t v___x_2135_; size_t v___x_2136_; 
v___x_2135_ = ((size_t)1ULL);
v___x_2136_ = lean_usize_add(v_i_2106_, v___x_2135_);
v_i_2106_ = v___x_2136_;
v_b_2107_ = v___x_2134_;
goto _start;
}
}
}
v___jp_2141_:
{
lean_object* v___x_2143_; 
v___x_2143_ = l_Lean_Syntax_getTailPos_x3f(v_ref_2140_, v___x_2103_);
lean_dec(v_ref_2140_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_inc(v___y_2142_);
v___y_2125_ = v___y_2142_;
v___y_2126_ = v___y_2142_;
goto v___jp_2124_;
}
else
{
lean_object* v_val_2144_; 
v_val_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_val_2144_);
lean_dec_ref_known(v___x_2143_, 1);
v___y_2125_ = v___y_2142_;
v___y_2126_ = v_val_2144_;
goto v___jp_2124_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg___boxed(lean_object* v___x_2151_, lean_object* v_as_2152_, lean_object* v_sz_2153_, lean_object* v_i_2154_, lean_object* v_b_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_){
_start:
{
uint8_t v___x_38280__boxed_2158_; size_t v_sz_boxed_2159_; size_t v_i_boxed_2160_; lean_object* v_res_2161_; 
v___x_38280__boxed_2158_ = lean_unbox(v___x_2151_);
v_sz_boxed_2159_ = lean_unbox_usize(v_sz_2153_);
lean_dec(v_sz_2153_);
v_i_boxed_2160_ = lean_unbox_usize(v_i_2154_);
lean_dec(v_i_2154_);
v_res_2161_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg(v___x_38280__boxed_2158_, v_as_2152_, v_sz_boxed_2159_, v_i_boxed_2160_, v_b_2155_, v___y_2156_);
lean_dec_ref(v___y_2156_);
lean_dec_ref(v_as_2152_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28(uint8_t v___x_2162_, lean_object* v_as_2163_, size_t v_sz_2164_, size_t v_i_2165_, lean_object* v_b_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
uint8_t v___x_2170_; 
v___x_2170_ = lean_usize_dec_lt(v_i_2165_, v_sz_2164_);
if (v___x_2170_ == 0)
{
lean_object* v___x_2171_; 
v___x_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2171_, 0, v_b_2166_);
return v___x_2171_;
}
else
{
lean_object* v_snd_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2209_; 
v_snd_2172_ = lean_ctor_get(v_b_2166_, 1);
v_isSharedCheck_2209_ = !lean_is_exclusive(v_b_2166_);
if (v_isSharedCheck_2209_ == 0)
{
lean_object* v_unused_2210_; 
v_unused_2210_ = lean_ctor_get(v_b_2166_, 0);
lean_dec(v_unused_2210_);
v___x_2174_ = v_b_2166_;
v_isShared_2175_ = v_isSharedCheck_2209_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_snd_2172_);
lean_dec(v_b_2166_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2209_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v_ref_2176_; lean_object* v_a_2177_; lean_object* v_ref_2178_; lean_object* v_msg_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2208_; 
v_ref_2176_ = lean_ctor_get(v___y_2167_, 2);
v_a_2177_ = lean_array_uget(v_as_2163_, v_i_2165_);
v_ref_2178_ = lean_ctor_get(v_a_2177_, 0);
v_msg_2179_ = lean_ctor_get(v_a_2177_, 1);
v_isSharedCheck_2208_ = !lean_is_exclusive(v_a_2177_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2181_ = v_a_2177_;
v_isShared_2182_ = v_isSharedCheck_2208_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_msg_2179_);
lean_inc(v_ref_2178_);
lean_dec(v_a_2177_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2208_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2183_; lean_object* v___y_2185_; lean_object* v___y_2186_; lean_object* v_ref_2200_; lean_object* v___y_2202_; lean_object* v___x_2205_; 
v___x_2183_ = lean_box(0);
v_ref_2200_ = l_Lean_replaceRef(v_ref_2178_, v_ref_2176_);
lean_dec(v_ref_2178_);
v___x_2205_ = l_Lean_Syntax_getPos_x3f(v_ref_2200_, v___x_2162_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v___x_2206_; 
v___x_2206_ = lean_unsigned_to_nat(0u);
v___y_2202_ = v___x_2206_;
goto v___jp_2201_;
}
else
{
lean_object* v_val_2207_; 
v_val_2207_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_val_2207_);
lean_dec_ref_known(v___x_2205_, 1);
v___y_2202_ = v_val_2207_;
goto v___jp_2201_;
}
v___jp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 1, v___y_2186_);
lean_ctor_set(v___x_2174_, 0, v___y_2185_);
v___x_2188_ = v___x_2174_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___y_2185_);
lean_ctor_set(v_reuseFailAlloc_2199_, 1, v___y_2186_);
v___x_2188_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v_pos2traces_2192_; lean_object* v___x_2194_; 
v___x_2189_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_2190_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_2172_, v___x_2188_, v___x_2189_);
v___x_2191_ = lean_array_push(v___x_2190_, v_msg_2179_);
v_pos2traces_2192_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(v_snd_2172_, v___x_2188_, v___x_2191_);
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 1, v_pos2traces_2192_);
lean_ctor_set(v___x_2181_, 0, v___x_2183_);
v___x_2194_ = v___x_2181_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2183_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v_pos2traces_2192_);
v___x_2194_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
size_t v___x_2195_; size_t v___x_2196_; lean_object* v___x_2197_; 
v___x_2195_ = ((size_t)1ULL);
v___x_2196_ = lean_usize_add(v_i_2165_, v___x_2195_);
v___x_2197_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg(v___x_2162_, v_as_2163_, v_sz_2164_, v___x_2196_, v___x_2194_, v___y_2167_);
return v___x_2197_;
}
}
}
v___jp_2201_:
{
lean_object* v___x_2203_; 
v___x_2203_ = l_Lean_Syntax_getTailPos_x3f(v_ref_2200_, v___x_2162_);
lean_dec(v_ref_2200_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_inc(v___y_2202_);
v___y_2185_ = v___y_2202_;
v___y_2186_ = v___y_2202_;
goto v___jp_2184_;
}
else
{
lean_object* v_val_2204_; 
v_val_2204_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_val_2204_);
lean_dec_ref_known(v___x_2203_, 1);
v___y_2185_ = v___y_2202_;
v___y_2186_ = v_val_2204_;
goto v___jp_2184_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28___boxed(lean_object* v___x_2211_, lean_object* v_as_2212_, lean_object* v_sz_2213_, lean_object* v_i_2214_, lean_object* v_b_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
uint8_t v___x_38360__boxed_2219_; size_t v_sz_boxed_2220_; size_t v_i_boxed_2221_; lean_object* v_res_2222_; 
v___x_38360__boxed_2219_ = lean_unbox(v___x_2211_);
v_sz_boxed_2220_ = lean_unbox_usize(v_sz_2213_);
lean_dec(v_sz_2213_);
v_i_boxed_2221_ = lean_unbox_usize(v_i_2214_);
lean_dec(v_i_2214_);
v_res_2222_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28(v___x_38360__boxed_2219_, v_as_2212_, v_sz_boxed_2220_, v_i_boxed_2221_, v_b_2215_, v___y_2216_, v___y_2217_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec_ref(v_as_2212_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19(uint8_t v___x_2223_, lean_object* v_t_2224_, lean_object* v_init_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
lean_object* v_root_2229_; lean_object* v_tail_2230_; lean_object* v___x_2231_; 
v_root_2229_ = lean_ctor_get(v_t_2224_, 0);
v_tail_2230_ = lean_ctor_get(v_t_2224_, 1);
lean_inc_ref(v_init_2225_);
v___x_2231_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27(v_init_2225_, v___x_2223_, v_root_2229_, v_init_2225_, v___y_2226_, v___y_2227_);
lean_dec_ref(v_init_2225_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2268_; 
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2234_ = v___x_2231_;
v_isShared_2235_ = v_isSharedCheck_2268_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2231_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2268_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
if (lean_obj_tag(v_a_2232_) == 0)
{
lean_object* v_a_2236_; lean_object* v___x_2238_; 
v_a_2236_ = lean_ctor_get(v_a_2232_, 0);
lean_inc(v_a_2236_);
lean_dec_ref_known(v_a_2232_, 1);
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 0, v_a_2236_);
v___x_2238_ = v___x_2234_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2236_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
else
{
lean_object* v_a_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; size_t v_sz_2243_; size_t v___x_2244_; lean_object* v___x_2245_; 
lean_del_object(v___x_2234_);
v_a_2240_ = lean_ctor_get(v_a_2232_, 0);
lean_inc(v_a_2240_);
lean_dec_ref_known(v_a_2232_, 1);
v___x_2241_ = lean_box(0);
v___x_2242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2241_);
lean_ctor_set(v___x_2242_, 1, v_a_2240_);
v_sz_2243_ = lean_array_size(v_tail_2230_);
v___x_2244_ = ((size_t)0ULL);
v___x_2245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28(v___x_2223_, v_tail_2230_, v_sz_2243_, v___x_2244_, v___x_2242_, v___y_2226_, v___y_2227_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2259_; 
v_a_2246_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2248_ = v___x_2245_;
v_isShared_2249_ = v_isSharedCheck_2259_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2245_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2259_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v_fst_2250_; 
v_fst_2250_ = lean_ctor_get(v_a_2246_, 0);
if (lean_obj_tag(v_fst_2250_) == 0)
{
lean_object* v_snd_2251_; lean_object* v___x_2253_; 
v_snd_2251_ = lean_ctor_get(v_a_2246_, 1);
lean_inc(v_snd_2251_);
lean_dec(v_a_2246_);
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 0, v_snd_2251_);
v___x_2253_ = v___x_2248_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_snd_2251_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
else
{
lean_object* v_val_2255_; lean_object* v___x_2257_; 
lean_inc_ref(v_fst_2250_);
lean_dec(v_a_2246_);
v_val_2255_ = lean_ctor_get(v_fst_2250_, 0);
lean_inc(v_val_2255_);
lean_dec_ref_known(v_fst_2250_, 1);
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 0, v_val_2255_);
v___x_2257_ = v___x_2248_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_val_2255_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
}
}
else
{
lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2267_; 
v_a_2260_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2262_ = v___x_2245_;
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v___x_2245_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2265_; 
if (v_isShared_2263_ == 0)
{
v___x_2265_ = v___x_2262_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_a_2260_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
}
}
}
else
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2276_; 
v_a_2269_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2271_ = v___x_2231_;
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2231_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2274_; 
if (v_isShared_2272_ == 0)
{
v___x_2274_ = v___x_2271_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_a_2269_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___boxed(lean_object* v___x_2277_, lean_object* v_t_2278_, lean_object* v_init_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
uint8_t v___x_38441__boxed_2283_; lean_object* v_res_2284_; 
v___x_38441__boxed_2283_ = lean_unbox(v___x_2277_);
v_res_2284_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19(v___x_38441__boxed_2283_, v_t_2278_, v_init_2279_, v___y_2280_, v___y_2281_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec_ref(v_t_2278_);
return v_res_2284_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__0(void){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2285_ = lean_unsigned_to_nat(32u);
v___x_2286_ = lean_mk_empty_array_with_capacity(v___x_2285_);
v___x_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
return v___x_2287_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1(void){
_start:
{
size_t v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2288_ = ((size_t)5ULL);
v___x_2289_ = lean_unsigned_to_nat(0u);
v___x_2290_ = lean_unsigned_to_nat(32u);
v___x_2291_ = lean_mk_empty_array_with_capacity(v___x_2290_);
v___x_2292_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__0);
v___x_2293_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2293_, 0, v___x_2292_);
lean_ctor_set(v___x_2293_, 1, v___x_2291_);
lean_ctor_set(v___x_2293_, 2, v___x_2289_);
lean_ctor_set(v___x_2293_, 3, v___x_2289_);
lean_ctor_set_usize(v___x_2293_, 4, v___x_2288_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(lean_object* v___y_2294_){
_start:
{
lean_object* v___x_2296_; lean_object* v_traceState_2297_; lean_object* v_traces_2298_; lean_object* v___x_2299_; lean_object* v_traceState_2300_; lean_object* v_env_2301_; lean_object* v_nextMacroScope_2302_; lean_object* v_ngen_2303_; lean_object* v_auxDeclNGen_2304_; lean_object* v_cache_2305_; lean_object* v_recordedDeps_2306_; lean_object* v_messages_2307_; lean_object* v_infoState_2308_; lean_object* v_snapshotTasks_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2328_; 
v___x_2296_ = lean_st_ref_get(v___y_2294_);
v_traceState_2297_ = lean_ctor_get(v___x_2296_, 4);
lean_inc_ref(v_traceState_2297_);
lean_dec(v___x_2296_);
v_traces_2298_ = lean_ctor_get(v_traceState_2297_, 0);
lean_inc_ref(v_traces_2298_);
lean_dec_ref(v_traceState_2297_);
v___x_2299_ = lean_st_ref_take(v___y_2294_);
v_traceState_2300_ = lean_ctor_get(v___x_2299_, 4);
v_env_2301_ = lean_ctor_get(v___x_2299_, 0);
v_nextMacroScope_2302_ = lean_ctor_get(v___x_2299_, 1);
v_ngen_2303_ = lean_ctor_get(v___x_2299_, 2);
v_auxDeclNGen_2304_ = lean_ctor_get(v___x_2299_, 3);
v_cache_2305_ = lean_ctor_get(v___x_2299_, 5);
v_recordedDeps_2306_ = lean_ctor_get(v___x_2299_, 6);
v_messages_2307_ = lean_ctor_get(v___x_2299_, 7);
v_infoState_2308_ = lean_ctor_get(v___x_2299_, 8);
v_snapshotTasks_2309_ = lean_ctor_get(v___x_2299_, 9);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2311_ = v___x_2299_;
v_isShared_2312_ = v_isSharedCheck_2328_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_snapshotTasks_2309_);
lean_inc(v_infoState_2308_);
lean_inc(v_messages_2307_);
lean_inc(v_recordedDeps_2306_);
lean_inc(v_cache_2305_);
lean_inc(v_traceState_2300_);
lean_inc(v_auxDeclNGen_2304_);
lean_inc(v_ngen_2303_);
lean_inc(v_nextMacroScope_2302_);
lean_inc(v_env_2301_);
lean_dec(v___x_2299_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2328_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
uint64_t v_tid_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2326_; 
v_tid_2313_ = lean_ctor_get_uint64(v_traceState_2300_, sizeof(void*)*1);
v_isSharedCheck_2326_ = !lean_is_exclusive(v_traceState_2300_);
if (v_isSharedCheck_2326_ == 0)
{
lean_object* v_unused_2327_; 
v_unused_2327_ = lean_ctor_get(v_traceState_2300_, 0);
lean_dec(v_unused_2327_);
v___x_2315_ = v_traceState_2300_;
v_isShared_2316_ = v_isSharedCheck_2326_;
goto v_resetjp_2314_;
}
else
{
lean_dec(v_traceState_2300_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2326_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2317_; lean_object* v___x_2319_; 
v___x_2317_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 0, v___x_2317_);
v___x_2319_ = v___x_2315_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v___x_2317_);
lean_ctor_set_uint64(v_reuseFailAlloc_2325_, sizeof(void*)*1, v_tid_2313_);
v___x_2319_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
lean_object* v___x_2321_; 
if (v_isShared_2312_ == 0)
{
lean_ctor_set(v___x_2311_, 4, v___x_2319_);
v___x_2321_ = v___x_2311_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_env_2301_);
lean_ctor_set(v_reuseFailAlloc_2324_, 1, v_nextMacroScope_2302_);
lean_ctor_set(v_reuseFailAlloc_2324_, 2, v_ngen_2303_);
lean_ctor_set(v_reuseFailAlloc_2324_, 3, v_auxDeclNGen_2304_);
lean_ctor_set(v_reuseFailAlloc_2324_, 4, v___x_2319_);
lean_ctor_set(v_reuseFailAlloc_2324_, 5, v_cache_2305_);
lean_ctor_set(v_reuseFailAlloc_2324_, 6, v_recordedDeps_2306_);
lean_ctor_set(v_reuseFailAlloc_2324_, 7, v_messages_2307_);
lean_ctor_set(v_reuseFailAlloc_2324_, 8, v_infoState_2308_);
lean_ctor_set(v_reuseFailAlloc_2324_, 9, v_snapshotTasks_2309_);
v___x_2321_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2322_ = lean_st_ref_put(v___y_2294_, v___x_2321_);
v___x_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2323_, 0, v_traces_2298_);
return v___x_2323_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___boxed(lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v___y_2329_);
lean_dec(v___y_2329_);
return v_res_2331_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0(void){
_start:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2332_ = lean_box(0);
v___x_2333_ = lean_unsigned_to_nat(16u);
v___x_2334_ = lean_mk_array(v___x_2333_, v___x_2332_);
return v___x_2334_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1(void){
_start:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v_pos2traces_2337_; 
v___x_2335_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0, &l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0);
v___x_2336_ = lean_unsigned_to_nat(0u);
v_pos2traces_2337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos2traces_2337_, 0, v___x_2336_);
lean_ctor_set(v_pos2traces_2337_, 1, v___x_2335_);
return v_pos2traces_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__9(lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
lean_object* v_toCold_2344_; lean_object* v_options_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
v_toCold_2344_ = lean_ctor_get(v___y_2338_, 0);
v_options_2345_ = lean_ctor_get(v_toCold_2344_, 2);
v___x_2346_ = l_Lean_trace_profiler_output;
v___x_2347_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14(v_options_2345_, v___x_2346_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v___x_2348_; uint8_t v___x_2349_; 
v___x_2348_ = l_Lean_trace_profiler_serve;
v___x_2349_ = l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(v_options_2345_, v___x_2348_);
if (v___x_2349_ == 0)
{
lean_object* v___x_2350_; lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2413_; 
v___x_2350_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v___y_2339_);
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2353_ = v___x_2350_;
v_isShared_2354_ = v_isSharedCheck_2413_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2350_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2413_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
uint8_t v___x_2355_; 
v___x_2355_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_2351_);
if (v___x_2355_ == 0)
{
lean_object* v___x_2356_; lean_object* v_pos2traces_2357_; lean_object* v___x_2358_; 
lean_del_object(v___x_2353_);
v___x_2356_ = lean_unsigned_to_nat(0u);
v_pos2traces_2357_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1, &l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1);
v___x_2358_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19(v___x_2355_, v_a_2351_, v_pos2traces_2357_, v___y_2338_, v___y_2339_);
lean_dec(v_a_2351_);
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v_a_2359_; lean_object* v___y_2361_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2387_; lean_object* v_size_2393_; lean_object* v_buckets_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; uint8_t v___x_2397_; 
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
lean_inc(v_a_2359_);
lean_dec_ref_known(v___x_2358_, 1);
v_size_2393_ = lean_ctor_get(v_a_2359_, 0);
lean_inc(v_size_2393_);
v_buckets_2394_ = lean_ctor_get(v_a_2359_, 1);
lean_inc_ref(v_buckets_2394_);
lean_dec(v_a_2359_);
v___x_2395_ = lean_mk_empty_array_with_capacity(v_size_2393_);
lean_dec(v_size_2393_);
v___x_2396_ = lean_array_get_size(v_buckets_2394_);
v___x_2397_ = lean_nat_dec_lt(v___x_2356_, v___x_2396_);
if (v___x_2397_ == 0)
{
lean_dec_ref(v_buckets_2394_);
v___y_2387_ = v___x_2395_;
goto v___jp_2386_;
}
else
{
size_t v___x_2398_; size_t v___x_2399_; lean_object* v___x_2400_; 
v___x_2398_ = ((size_t)0ULL);
v___x_2399_ = lean_usize_of_nat(v___x_2396_);
v___x_2400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__23(v_buckets_2394_, v___x_2398_, v___x_2399_, v___x_2395_);
lean_dec_ref(v_buckets_2394_);
v___y_2387_ = v___x_2400_;
goto v___jp_2386_;
}
v___jp_2360_:
{
lean_object* v___x_2362_; size_t v_sz_2363_; size_t v___x_2364_; lean_object* v___x_2365_; 
v___x_2362_ = lean_box(0);
v_sz_2363_ = lean_array_size(v___y_2361_);
v___x_2364_ = ((size_t)0ULL);
v___x_2365_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20(v___x_2349_, v___y_2361_, v_sz_2363_, v___x_2364_, v___x_2362_, v___y_2338_, v___y_2339_);
lean_dec_ref(v___y_2361_);
if (lean_obj_tag(v___x_2365_) == 0)
{
lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2372_ == 0)
{
lean_object* v_unused_2373_; 
v_unused_2373_ = lean_ctor_get(v___x_2365_, 0);
lean_dec(v_unused_2373_);
v___x_2367_ = v___x_2365_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_dec(v___x_2365_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
lean_ctor_set(v___x_2367_, 0, v___x_2362_);
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v___x_2362_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
else
{
return v___x_2365_;
}
}
v___jp_2374_:
{
lean_object* v___x_2379_; 
v___x_2379_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(v___y_2376_, v___y_2377_, v___y_2375_, v___y_2378_);
lean_dec(v___y_2378_);
lean_dec(v___y_2376_);
v___y_2361_ = v___x_2379_;
goto v___jp_2360_;
}
v___jp_2380_:
{
uint8_t v___x_2385_; 
v___x_2385_ = lean_nat_dec_le(v___y_2384_, v___y_2382_);
if (v___x_2385_ == 0)
{
lean_dec(v___y_2382_);
lean_inc(v___y_2384_);
v___y_2375_ = v___y_2384_;
v___y_2376_ = v___y_2381_;
v___y_2377_ = v___y_2383_;
v___y_2378_ = v___y_2384_;
goto v___jp_2374_;
}
else
{
v___y_2375_ = v___y_2384_;
v___y_2376_ = v___y_2381_;
v___y_2377_ = v___y_2383_;
v___y_2378_ = v___y_2382_;
goto v___jp_2374_;
}
}
v___jp_2386_:
{
lean_object* v___x_2388_; uint8_t v___x_2389_; 
v___x_2388_ = lean_array_get_size(v___y_2387_);
v___x_2389_ = lean_nat_dec_eq(v___x_2388_, v___x_2356_);
if (v___x_2389_ == 0)
{
lean_object* v___x_2390_; lean_object* v___x_2391_; uint8_t v___x_2392_; 
v___x_2390_ = lean_unsigned_to_nat(1u);
v___x_2391_ = lean_nat_sub(v___x_2388_, v___x_2390_);
v___x_2392_ = lean_nat_dec_le(v___x_2356_, v___x_2391_);
if (v___x_2392_ == 0)
{
lean_inc(v___x_2391_);
v___y_2381_ = v___x_2388_;
v___y_2382_ = v___x_2391_;
v___y_2383_ = v___y_2387_;
v___y_2384_ = v___x_2391_;
goto v___jp_2380_;
}
else
{
v___y_2381_ = v___x_2388_;
v___y_2382_ = v___x_2391_;
v___y_2383_ = v___y_2387_;
v___y_2384_ = v___x_2356_;
goto v___jp_2380_;
}
}
else
{
v___y_2361_ = v___y_2387_;
goto v___jp_2360_;
}
}
}
else
{
lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2408_; 
v_a_2401_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2403_ = v___x_2358_;
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v___x_2358_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2406_; 
if (v_isShared_2404_ == 0)
{
v___x_2406_ = v___x_2403_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_a_2401_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
}
else
{
lean_object* v___x_2409_; lean_object* v___x_2411_; 
lean_dec(v_a_2351_);
v___x_2409_ = lean_box(0);
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 0, v___x_2409_);
v___x_2411_ = v___x_2353_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___x_2409_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
else
{
goto v___jp_2341_;
}
}
else
{
lean_dec_ref_known(v___x_2347_, 1);
goto v___jp_2341_;
}
v___jp_2341_:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2342_ = lean_box(0);
v___x_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2342_);
return v___x_2343_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__9___boxed(lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l_Lean_addTraceAsMessages___at___00main_spec__9(v___y_2414_, v___y_2415_);
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
return v_res_2417_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10(lean_object* v_as_2418_, size_t v_sz_2419_, size_t v_i_2420_, lean_object* v_b_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
uint8_t v___x_2425_; 
v___x_2425_ = lean_usize_dec_lt(v_i_2420_, v_sz_2419_);
if (v___x_2425_ == 0)
{
lean_object* v___x_2426_; 
v___x_2426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2426_, 0, v_b_2421_);
return v___x_2426_;
}
else
{
lean_object* v___x_2427_; lean_object* v_a_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
v___x_2427_ = lean_box(0);
v_a_2428_ = lean_array_uget_borrowed(v_as_2418_, v_i_2420_);
v___x_2429_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2422_);
lean_inc(v_a_2428_);
v___x_2430_ = l_Lean_Compiler_LCNF_resumeCompilation(v_a_2428_, v___x_2429_, v___y_2422_, v___y_2423_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v___x_2431_; 
lean_dec_ref_known(v___x_2430_, 1);
v___x_2431_ = l_Lean_addTraceAsMessages___at___00main_spec__9(v___y_2422_, v___y_2423_);
if (lean_obj_tag(v___x_2431_) == 0)
{
size_t v___x_2432_; size_t v___x_2433_; 
lean_dec_ref_known(v___x_2431_, 1);
v___x_2432_ = ((size_t)1ULL);
v___x_2433_ = lean_usize_add(v_i_2420_, v___x_2432_);
v_i_2420_ = v___x_2433_;
v_b_2421_ = v___x_2427_;
goto _start;
}
else
{
return v___x_2431_;
}
}
else
{
lean_object* v_a_2435_; lean_object* v___x_2436_; 
v_a_2435_ = lean_ctor_get(v___x_2430_, 0);
lean_inc(v_a_2435_);
lean_dec_ref_known(v___x_2430_, 1);
v___x_2436_ = l_Lean_addTraceAsMessages___at___00main_spec__9(v___y_2422_, v___y_2423_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2443_ == 0)
{
lean_object* v_unused_2444_; 
v_unused_2444_ = lean_ctor_get(v___x_2436_, 0);
lean_dec(v_unused_2444_);
v___x_2438_ = v___x_2436_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_dec(v___x_2436_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
lean_ctor_set_tag(v___x_2438_, 1);
lean_ctor_set(v___x_2438_, 0, v_a_2435_);
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2435_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
else
{
lean_dec(v_a_2435_);
return v___x_2436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10___boxed(lean_object* v_as_2445_, lean_object* v_sz_2446_, lean_object* v_i_2447_, lean_object* v_b_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
size_t v_sz_boxed_2452_; size_t v_i_boxed_2453_; lean_object* v_res_2454_; 
v_sz_boxed_2452_ = lean_unbox_usize(v_sz_2446_);
lean_dec(v_sz_2446_);
v_i_boxed_2453_ = lean_unbox_usize(v_i_2447_);
lean_dec(v_i_2447_);
v_res_2454_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10(v_as_2445_, v_sz_boxed_2452_, v_i_boxed_2453_, v_b_2448_, v___y_2449_, v___y_2450_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec_ref(v_as_2445_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg(lean_object* v_as_2455_, size_t v_sz_2456_, size_t v_i_2457_, lean_object* v_b_2458_, lean_object* v___y_2459_){
_start:
{
uint8_t v___x_2461_; 
v___x_2461_ = lean_usize_dec_lt(v_i_2457_, v_sz_2456_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2462_; 
v___x_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2462_, 0, v_b_2458_);
return v___x_2462_;
}
else
{
uint8_t v___x_2463_; lean_object* v_a_2464_; lean_object* v___x_2465_; lean_object* v_ref_2466_; lean_object* v___x_2467_; 
lean_dec_ref(v_b_2458_);
v___x_2463_ = 0;
v_a_2464_ = lean_array_uget_borrowed(v_as_2455_, v_i_2457_);
lean_inc(v_a_2464_);
v___x_2465_ = l_Lean_Message_toString(v_a_2464_, v___x_2463_);
v_ref_2466_ = lean_ctor_get(v___y_2459_, 2);
v___x_2467_ = l_IO_eprintln___at___00main_spec__6(v___x_2465_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v___x_2468_; size_t v___x_2469_; size_t v___x_2470_; 
lean_dec_ref_known(v___x_2467_, 1);
v___x_2468_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___closed__0));
v___x_2469_ = ((size_t)1ULL);
v___x_2470_ = lean_usize_add(v_i_2457_, v___x_2469_);
v_i_2457_ = v___x_2470_;
v_b_2458_ = v___x_2468_;
goto _start;
}
else
{
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2483_; 
v_a_2472_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2474_ = v___x_2467_;
v_isShared_2475_ = v_isSharedCheck_2483_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2467_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2483_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2481_; 
v___x_2476_ = lean_io_error_to_string(v_a_2472_);
v___x_2477_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2476_);
v___x_2478_ = l_Lean_MessageData_ofFormat(v___x_2477_);
lean_inc(v_ref_2466_);
v___x_2479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2479_, 0, v_ref_2466_);
lean_ctor_set(v___x_2479_, 1, v___x_2478_);
if (v_isShared_2475_ == 0)
{
lean_ctor_set(v___x_2474_, 0, v___x_2479_);
v___x_2481_ = v___x_2474_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v___x_2479_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg___boxed(lean_object* v_as_2484_, lean_object* v_sz_2485_, lean_object* v_i_2486_, lean_object* v_b_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
size_t v_sz_boxed_2490_; size_t v_i_boxed_2491_; lean_object* v_res_2492_; 
v_sz_boxed_2490_ = lean_unbox_usize(v_sz_2485_);
lean_dec(v_sz_2485_);
v_i_boxed_2491_ = lean_unbox_usize(v_i_2486_);
lean_dec(v_i_2486_);
v_res_2492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg(v_as_2484_, v_sz_boxed_2490_, v_i_boxed_2491_, v_b_2487_, v___y_2488_);
lean_dec_ref(v___y_2488_);
lean_dec_ref(v_as_2484_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38(lean_object* v_as_2493_, size_t v_sz_2494_, size_t v_i_2495_, lean_object* v_b_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
uint8_t v___x_2500_; 
v___x_2500_ = lean_usize_dec_lt(v_i_2495_, v_sz_2494_);
if (v___x_2500_ == 0)
{
lean_object* v___x_2501_; 
v___x_2501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2501_, 0, v_b_2496_);
return v___x_2501_;
}
else
{
uint8_t v___x_2502_; lean_object* v_a_2503_; lean_object* v___x_2504_; lean_object* v_ref_2505_; lean_object* v___x_2506_; 
lean_dec_ref(v_b_2496_);
v___x_2502_ = 0;
v_a_2503_ = lean_array_uget_borrowed(v_as_2493_, v_i_2495_);
lean_inc(v_a_2503_);
v___x_2504_ = l_Lean_Message_toString(v_a_2503_, v___x_2502_);
v_ref_2505_ = lean_ctor_get(v___y_2497_, 2);
v___x_2506_ = l_IO_eprintln___at___00main_spec__6(v___x_2504_);
if (lean_obj_tag(v___x_2506_) == 0)
{
lean_object* v___x_2507_; size_t v___x_2508_; size_t v___x_2509_; lean_object* v___x_2510_; 
lean_dec_ref_known(v___x_2506_, 1);
v___x_2507_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___closed__0));
v___x_2508_ = ((size_t)1ULL);
v___x_2509_ = lean_usize_add(v_i_2495_, v___x_2508_);
v___x_2510_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg(v_as_2493_, v_sz_2494_, v___x_2509_, v___x_2507_, v___y_2497_);
return v___x_2510_;
}
else
{
lean_object* v_a_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2522_; 
v_a_2511_ = lean_ctor_get(v___x_2506_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2513_ = v___x_2506_;
v_isShared_2514_ = v_isSharedCheck_2522_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_a_2511_);
lean_dec(v___x_2506_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2522_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2520_; 
v___x_2515_ = lean_io_error_to_string(v_a_2511_);
v___x_2516_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2515_);
v___x_2517_ = l_Lean_MessageData_ofFormat(v___x_2516_);
lean_inc(v_ref_2505_);
v___x_2518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2518_, 0, v_ref_2505_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
if (v_isShared_2514_ == 0)
{
lean_ctor_set(v___x_2513_, 0, v___x_2518_);
v___x_2520_ = v___x_2513_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v___x_2518_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38___boxed(lean_object* v_as_2523_, lean_object* v_sz_2524_, lean_object* v_i_2525_, lean_object* v_b_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
size_t v_sz_boxed_2530_; size_t v_i_boxed_2531_; lean_object* v_res_2532_; 
v_sz_boxed_2530_ = lean_unbox_usize(v_sz_2524_);
lean_dec(v_sz_2524_);
v_i_boxed_2531_ = lean_unbox_usize(v_i_2525_);
lean_dec(v_i_2525_);
v_res_2532_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38(v_as_2523_, v_sz_boxed_2530_, v_i_boxed_2531_, v_b_2526_, v___y_2527_, v___y_2528_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec_ref(v_as_2523_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26(lean_object* v_init_2533_, lean_object* v_n_2534_, lean_object* v_b_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_){
_start:
{
if (lean_obj_tag(v_n_2534_) == 0)
{
lean_object* v_cs_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; size_t v_sz_2542_; size_t v___x_2543_; lean_object* v___x_2544_; 
v_cs_2539_ = lean_ctor_get(v_n_2534_, 0);
v___x_2540_ = lean_box(0);
v___x_2541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2540_);
lean_ctor_set(v___x_2541_, 1, v_b_2535_);
v_sz_2542_ = lean_array_size(v_cs_2539_);
v___x_2543_ = ((size_t)0ULL);
v___x_2544_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__37(v_init_2533_, v_cs_2539_, v_sz_2542_, v___x_2543_, v___x_2541_, v___y_2536_, v___y_2537_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2559_; 
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2547_ = v___x_2544_;
v_isShared_2548_ = v_isSharedCheck_2559_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2544_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2559_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v_fst_2549_; 
v_fst_2549_ = lean_ctor_get(v_a_2545_, 0);
if (lean_obj_tag(v_fst_2549_) == 0)
{
lean_object* v_snd_2550_; lean_object* v___x_2551_; lean_object* v___x_2553_; 
v_snd_2550_ = lean_ctor_get(v_a_2545_, 1);
lean_inc(v_snd_2550_);
lean_dec(v_a_2545_);
v___x_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2551_, 0, v_snd_2550_);
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 0, v___x_2551_);
v___x_2553_ = v___x_2547_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___x_2551_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
else
{
lean_object* v_val_2555_; lean_object* v___x_2557_; 
lean_inc_ref(v_fst_2549_);
lean_dec(v_a_2545_);
v_val_2555_ = lean_ctor_get(v_fst_2549_, 0);
lean_inc(v_val_2555_);
lean_dec_ref_known(v_fst_2549_, 1);
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 0, v_val_2555_);
v___x_2557_ = v___x_2547_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_val_2555_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
}
else
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2567_; 
v_a_2560_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2562_ = v___x_2544_;
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2544_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2565_; 
if (v_isShared_2563_ == 0)
{
v___x_2565_ = v___x_2562_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_a_2560_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
}
else
{
lean_object* v_vs_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; size_t v_sz_2571_; size_t v___x_2572_; lean_object* v___x_2573_; 
v_vs_2568_ = lean_ctor_get(v_n_2534_, 0);
v___x_2569_ = lean_box(0);
v___x_2570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2569_);
lean_ctor_set(v___x_2570_, 1, v_b_2535_);
v_sz_2571_ = lean_array_size(v_vs_2568_);
v___x_2572_ = ((size_t)0ULL);
v___x_2573_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38(v_vs_2568_, v_sz_2571_, v___x_2572_, v___x_2570_, v___y_2536_, v___y_2537_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2588_; 
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2576_ = v___x_2573_;
v_isShared_2577_ = v_isSharedCheck_2588_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2573_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2588_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v_fst_2578_; 
v_fst_2578_ = lean_ctor_get(v_a_2574_, 0);
if (lean_obj_tag(v_fst_2578_) == 0)
{
lean_object* v_snd_2579_; lean_object* v___x_2580_; lean_object* v___x_2582_; 
v_snd_2579_ = lean_ctor_get(v_a_2574_, 1);
lean_inc(v_snd_2579_);
lean_dec(v_a_2574_);
v___x_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2580_, 0, v_snd_2579_);
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 0, v___x_2580_);
v___x_2582_ = v___x_2576_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2580_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
else
{
lean_object* v_val_2584_; lean_object* v___x_2586_; 
lean_inc_ref(v_fst_2578_);
lean_dec(v_a_2574_);
v_val_2584_ = lean_ctor_get(v_fst_2578_, 0);
lean_inc(v_val_2584_);
lean_dec_ref_known(v_fst_2578_, 1);
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 0, v_val_2584_);
v___x_2586_ = v___x_2576_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_val_2584_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
else
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
v_a_2589_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2573_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2573_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__37(lean_object* v_init_2597_, lean_object* v_as_2598_, size_t v_sz_2599_, size_t v_i_2600_, lean_object* v_b_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
uint8_t v___x_2605_; 
v___x_2605_ = lean_usize_dec_lt(v_i_2600_, v_sz_2599_);
if (v___x_2605_ == 0)
{
lean_object* v___x_2606_; 
v___x_2606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2606_, 0, v_b_2601_);
return v___x_2606_;
}
else
{
lean_object* v_snd_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2641_; 
v_snd_2607_ = lean_ctor_get(v_b_2601_, 1);
v_isSharedCheck_2641_ = !lean_is_exclusive(v_b_2601_);
if (v_isSharedCheck_2641_ == 0)
{
lean_object* v_unused_2642_; 
v_unused_2642_ = lean_ctor_get(v_b_2601_, 0);
lean_dec(v_unused_2642_);
v___x_2609_ = v_b_2601_;
v_isShared_2610_ = v_isSharedCheck_2641_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_snd_2607_);
lean_dec(v_b_2601_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2641_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2611_; lean_object* v_a_2612_; lean_object* v___x_2613_; 
v___x_2611_ = lean_box(0);
v_a_2612_ = lean_array_uget_borrowed(v_as_2598_, v_i_2600_);
lean_inc(v_snd_2607_);
v___x_2613_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26(v_init_2597_, v_a_2612_, v_snd_2607_, v___y_2602_, v___y_2603_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2632_; 
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2616_ = v___x_2613_;
v_isShared_2617_ = v_isSharedCheck_2632_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2613_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2632_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
if (lean_obj_tag(v_a_2614_) == 0)
{
lean_object* v___x_2618_; lean_object* v___x_2620_; 
v___x_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2618_, 0, v_a_2614_);
if (v_isShared_2610_ == 0)
{
lean_ctor_set(v___x_2609_, 0, v___x_2618_);
v___x_2620_ = v___x_2609_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2618_);
lean_ctor_set(v_reuseFailAlloc_2624_, 1, v_snd_2607_);
v___x_2620_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
lean_object* v___x_2622_; 
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 0, v___x_2620_);
v___x_2622_ = v___x_2616_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2620_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; 
lean_del_object(v___x_2616_);
lean_dec(v_snd_2607_);
v_a_2625_ = lean_ctor_get(v_a_2614_, 0);
lean_inc(v_a_2625_);
lean_dec_ref_known(v_a_2614_, 1);
if (v_isShared_2610_ == 0)
{
lean_ctor_set(v___x_2609_, 1, v_a_2625_);
lean_ctor_set(v___x_2609_, 0, v___x_2611_);
v___x_2627_ = v___x_2609_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v___x_2611_);
lean_ctor_set(v_reuseFailAlloc_2631_, 1, v_a_2625_);
v___x_2627_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
size_t v___x_2628_; size_t v___x_2629_; 
v___x_2628_ = ((size_t)1ULL);
v___x_2629_ = lean_usize_add(v_i_2600_, v___x_2628_);
v_i_2600_ = v___x_2629_;
v_b_2601_ = v___x_2627_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
lean_del_object(v___x_2609_);
lean_dec(v_snd_2607_);
v_a_2633_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2613_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2613_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2633_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__37___boxed(lean_object* v_init_2643_, lean_object* v_as_2644_, lean_object* v_sz_2645_, lean_object* v_i_2646_, lean_object* v_b_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
size_t v_sz_boxed_2651_; size_t v_i_boxed_2652_; lean_object* v_res_2653_; 
v_sz_boxed_2651_ = lean_unbox_usize(v_sz_2645_);
lean_dec(v_sz_2645_);
v_i_boxed_2652_ = lean_unbox_usize(v_i_2646_);
lean_dec(v_i_2646_);
v_res_2653_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__37(v_init_2643_, v_as_2644_, v_sz_boxed_2651_, v_i_boxed_2652_, v_b_2647_, v___y_2648_, v___y_2649_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec_ref(v_as_2644_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26___boxed(lean_object* v_init_2654_, lean_object* v_n_2655_, lean_object* v_b_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v_res_2660_; 
v_res_2660_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26(v_init_2654_, v_n_2655_, v_b_2656_, v___y_2657_, v___y_2658_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec_ref(v_n_2655_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg(lean_object* v_as_2661_, size_t v_sz_2662_, size_t v_i_2663_, lean_object* v_b_2664_, lean_object* v___y_2665_){
_start:
{
uint8_t v___x_2667_; 
v___x_2667_ = lean_usize_dec_lt(v_i_2663_, v_sz_2662_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2668_; 
v___x_2668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2668_, 0, v_b_2664_);
return v___x_2668_;
}
else
{
uint8_t v___x_2669_; lean_object* v_a_2670_; lean_object* v___x_2671_; lean_object* v_ref_2672_; lean_object* v___x_2673_; 
lean_dec_ref(v_b_2664_);
v___x_2669_ = 0;
v_a_2670_ = lean_array_uget_borrowed(v_as_2661_, v_i_2663_);
lean_inc(v_a_2670_);
v___x_2671_ = l_Lean_Message_toString(v_a_2670_, v___x_2669_);
v_ref_2672_ = lean_ctor_get(v___y_2665_, 2);
v___x_2673_ = l_IO_eprintln___at___00main_spec__6(v___x_2671_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v___x_2674_; size_t v___x_2675_; size_t v___x_2676_; 
lean_dec_ref_known(v___x_2673_, 1);
v___x_2674_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___closed__0));
v___x_2675_ = ((size_t)1ULL);
v___x_2676_ = lean_usize_add(v_i_2663_, v___x_2675_);
v_i_2663_ = v___x_2676_;
v_b_2664_ = v___x_2674_;
goto _start;
}
else
{
lean_object* v_a_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2689_; 
v_a_2678_ = lean_ctor_get(v___x_2673_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2680_ = v___x_2673_;
v_isShared_2681_ = v_isSharedCheck_2689_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_a_2678_);
lean_dec(v___x_2673_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2689_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2687_; 
v___x_2682_ = lean_io_error_to_string(v_a_2678_);
v___x_2683_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2682_);
v___x_2684_ = l_Lean_MessageData_ofFormat(v___x_2683_);
lean_inc(v_ref_2672_);
v___x_2685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2685_, 0, v_ref_2672_);
lean_ctor_set(v___x_2685_, 1, v___x_2684_);
if (v_isShared_2681_ == 0)
{
lean_ctor_set(v___x_2680_, 0, v___x_2685_);
v___x_2687_ = v___x_2680_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v___x_2685_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg___boxed(lean_object* v_as_2690_, lean_object* v_sz_2691_, lean_object* v_i_2692_, lean_object* v_b_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_){
_start:
{
size_t v_sz_boxed_2696_; size_t v_i_boxed_2697_; lean_object* v_res_2698_; 
v_sz_boxed_2696_ = lean_unbox_usize(v_sz_2691_);
lean_dec(v_sz_2691_);
v_i_boxed_2697_ = lean_unbox_usize(v_i_2692_);
lean_dec(v_i_2692_);
v_res_2698_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg(v_as_2690_, v_sz_boxed_2696_, v_i_boxed_2697_, v_b_2693_, v___y_2694_);
lean_dec_ref(v___y_2694_);
lean_dec_ref(v_as_2690_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27(lean_object* v_as_2699_, size_t v_sz_2700_, size_t v_i_2701_, lean_object* v_b_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_){
_start:
{
uint8_t v___x_2706_; 
v___x_2706_ = lean_usize_dec_lt(v_i_2701_, v_sz_2700_);
if (v___x_2706_ == 0)
{
lean_object* v___x_2707_; 
v___x_2707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2707_, 0, v_b_2702_);
return v___x_2707_;
}
else
{
uint8_t v___x_2708_; lean_object* v_a_2709_; lean_object* v___x_2710_; lean_object* v_ref_2711_; lean_object* v___x_2712_; 
lean_dec_ref(v_b_2702_);
v___x_2708_ = 0;
v_a_2709_ = lean_array_uget_borrowed(v_as_2699_, v_i_2701_);
lean_inc(v_a_2709_);
v___x_2710_ = l_Lean_Message_toString(v_a_2709_, v___x_2708_);
v_ref_2711_ = lean_ctor_get(v___y_2703_, 2);
v___x_2712_ = l_IO_eprintln___at___00main_spec__6(v___x_2710_);
if (lean_obj_tag(v___x_2712_) == 0)
{
lean_object* v___x_2713_; size_t v___x_2714_; size_t v___x_2715_; lean_object* v___x_2716_; 
lean_dec_ref_known(v___x_2712_, 1);
v___x_2713_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___closed__0));
v___x_2714_ = ((size_t)1ULL);
v___x_2715_ = lean_usize_add(v_i_2701_, v___x_2714_);
v___x_2716_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg(v_as_2699_, v_sz_2700_, v___x_2715_, v___x_2713_, v___y_2703_);
return v___x_2716_;
}
else
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2728_; 
v_a_2717_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2719_ = v___x_2712_;
v_isShared_2720_ = v_isSharedCheck_2728_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2712_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2728_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2726_; 
v___x_2721_ = lean_io_error_to_string(v_a_2717_);
v___x_2722_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
v___x_2723_ = l_Lean_MessageData_ofFormat(v___x_2722_);
lean_inc(v_ref_2711_);
v___x_2724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2724_, 0, v_ref_2711_);
lean_ctor_set(v___x_2724_, 1, v___x_2723_);
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 0, v___x_2724_);
v___x_2726_ = v___x_2719_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v___x_2724_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27___boxed(lean_object* v_as_2729_, lean_object* v_sz_2730_, lean_object* v_i_2731_, lean_object* v_b_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
size_t v_sz_boxed_2736_; size_t v_i_boxed_2737_; lean_object* v_res_2738_; 
v_sz_boxed_2736_ = lean_unbox_usize(v_sz_2730_);
lean_dec(v_sz_2730_);
v_i_boxed_2737_ = lean_unbox_usize(v_i_2731_);
lean_dec(v_i_2731_);
v_res_2738_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27(v_as_2729_, v_sz_boxed_2736_, v_i_boxed_2737_, v_b_2732_, v___y_2733_, v___y_2734_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec_ref(v_as_2729_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__11(lean_object* v_t_2739_, lean_object* v_init_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_){
_start:
{
lean_object* v_root_2744_; lean_object* v_tail_2745_; lean_object* v___x_2746_; 
v_root_2744_ = lean_ctor_get(v_t_2739_, 0);
v_tail_2745_ = lean_ctor_get(v_t_2739_, 1);
v___x_2746_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26(v_init_2740_, v_root_2744_, v_init_2740_, v___y_2741_, v___y_2742_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2783_; 
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2749_ = v___x_2746_;
v_isShared_2750_ = v_isSharedCheck_2783_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2746_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2783_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
if (lean_obj_tag(v_a_2747_) == 0)
{
lean_object* v_a_2751_; lean_object* v___x_2753_; 
v_a_2751_ = lean_ctor_get(v_a_2747_, 0);
lean_inc(v_a_2751_);
lean_dec_ref_known(v_a_2747_, 1);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 0, v_a_2751_);
v___x_2753_ = v___x_2749_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_a_2751_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
else
{
lean_object* v_a_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; size_t v_sz_2758_; size_t v___x_2759_; lean_object* v___x_2760_; 
lean_del_object(v___x_2749_);
v_a_2755_ = lean_ctor_get(v_a_2747_, 0);
lean_inc(v_a_2755_);
lean_dec_ref_known(v_a_2747_, 1);
v___x_2756_ = lean_box(0);
v___x_2757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2756_);
lean_ctor_set(v___x_2757_, 1, v_a_2755_);
v_sz_2758_ = lean_array_size(v_tail_2745_);
v___x_2759_ = ((size_t)0ULL);
v___x_2760_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27(v_tail_2745_, v_sz_2758_, v___x_2759_, v___x_2757_, v___y_2741_, v___y_2742_);
if (lean_obj_tag(v___x_2760_) == 0)
{
lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2774_; 
v_a_2761_ = lean_ctor_get(v___x_2760_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2763_ = v___x_2760_;
v_isShared_2764_ = v_isSharedCheck_2774_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2760_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2774_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v_fst_2765_; 
v_fst_2765_ = lean_ctor_get(v_a_2761_, 0);
if (lean_obj_tag(v_fst_2765_) == 0)
{
lean_object* v_snd_2766_; lean_object* v___x_2768_; 
v_snd_2766_ = lean_ctor_get(v_a_2761_, 1);
lean_inc(v_snd_2766_);
lean_dec(v_a_2761_);
if (v_isShared_2764_ == 0)
{
lean_ctor_set(v___x_2763_, 0, v_snd_2766_);
v___x_2768_ = v___x_2763_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_snd_2766_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
else
{
lean_object* v_val_2770_; lean_object* v___x_2772_; 
lean_inc_ref(v_fst_2765_);
lean_dec(v_a_2761_);
v_val_2770_ = lean_ctor_get(v_fst_2765_, 0);
lean_inc(v_val_2770_);
lean_dec_ref_known(v_fst_2765_, 1);
if (v_isShared_2764_ == 0)
{
lean_ctor_set(v___x_2763_, 0, v_val_2770_);
v___x_2772_ = v___x_2763_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_val_2770_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
else
{
lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2782_; 
v_a_2775_ = lean_ctor_get(v___x_2760_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2777_ = v___x_2760_;
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2760_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2780_; 
if (v_isShared_2778_ == 0)
{
v___x_2780_ = v___x_2777_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_a_2775_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
}
}
}
else
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
v_a_2784_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___x_2746_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2746_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__11___boxed(lean_object* v_t_2792_, lean_object* v_init_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l_Lean_PersistentArray_forIn___at___00main_spec__11(v_t_2792_, v_init_2793_, v___y_2794_, v___y_2795_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec_ref(v_t_2792_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(lean_object* v_as_2798_, size_t v_sz_2799_, size_t v_i_2800_, lean_object* v_b_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_){
_start:
{
uint8_t v___x_2805_; 
v___x_2805_ = lean_usize_dec_lt(v_i_2800_, v_sz_2799_);
if (v___x_2805_ == 0)
{
lean_object* v___x_2806_; 
v___x_2806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2806_, 0, v_b_2801_);
return v___x_2806_;
}
else
{
lean_object* v_a_2807_; lean_object* v_declNames_2808_; lean_object* v___x_2809_; size_t v_sz_2810_; size_t v___x_2811_; lean_object* v___x_2812_; 
v_a_2807_ = lean_array_uget_borrowed(v_as_2798_, v_i_2800_);
v_declNames_2808_ = lean_ctor_get(v_a_2807_, 0);
v___x_2809_ = lean_box(0);
v_sz_2810_ = lean_array_size(v_declNames_2808_);
v___x_2811_ = ((size_t)0ULL);
v___x_2812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10(v_declNames_2808_, v_sz_2810_, v___x_2811_, v___x_2809_, v___y_2802_, v___y_2803_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v___x_2813_; 
lean_dec_ref_known(v___x_2812_, 1);
v___x_2813_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v___y_2803_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v_a_2814_; lean_object* v_unreported_2815_; lean_object* v___x_2816_; 
v_a_2814_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_a_2814_);
lean_dec_ref_known(v___x_2813_, 1);
v_unreported_2815_ = lean_ctor_get(v_a_2814_, 1);
lean_inc_ref(v_unreported_2815_);
lean_dec(v_a_2814_);
v___x_2816_ = l_Lean_PersistentArray_forIn___at___00main_spec__11(v_unreported_2815_, v___x_2809_, v___y_2802_, v___y_2803_);
lean_dec_ref(v_unreported_2815_);
if (lean_obj_tag(v___x_2816_) == 0)
{
size_t v___x_2817_; size_t v___x_2818_; 
lean_dec_ref_known(v___x_2816_, 1);
v___x_2817_ = ((size_t)1ULL);
v___x_2818_ = lean_usize_add(v_i_2800_, v___x_2817_);
v_i_2800_ = v___x_2818_;
v_b_2801_ = v___x_2809_;
goto _start;
}
else
{
return v___x_2816_;
}
}
else
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2827_; 
v_a_2820_ = lean_ctor_get(v___x_2813_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2813_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2822_ = v___x_2813_;
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2813_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2825_; 
if (v_isShared_2823_ == 0)
{
v___x_2825_ = v___x_2822_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2820_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
}
else
{
return v___x_2812_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___boxed(lean_object* v_as_2828_, lean_object* v_sz_2829_, lean_object* v_i_2830_, lean_object* v_b_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_){
_start:
{
size_t v_sz_boxed_2835_; size_t v_i_boxed_2836_; lean_object* v_res_2837_; 
v_sz_boxed_2835_ = lean_unbox_usize(v_sz_2829_);
lean_dec(v_sz_2829_);
v_i_boxed_2836_ = lean_unbox_usize(v_i_2830_);
lean_dec(v_i_2830_);
v_res_2837_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(v_as_2828_, v_sz_boxed_2835_, v_i_boxed_2836_, v_b_2831_, v___y_2832_, v___y_2833_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec_ref(v_as_2828_);
return v_res_2837_;
}
}
static lean_object* _init_l_main___closed__1(void){
_start:
{
lean_object* v___x_2839_; 
v___x_2839_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg();
return v___x_2839_;
}
}
static lean_object* _init_l_main___closed__2(void){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___x_2840_ = l_Lean_instInhabitedClassState_default;
v___x_2841_ = lean_box(0);
v___x_2842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2842_, 0, v___x_2841_);
lean_ctor_set(v___x_2842_, 1, v___x_2840_);
return v___x_2842_;
}
}
static lean_object* _init_l_main___closed__3(void){
_start:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
v___x_2843_ = l_Lean_Meta_Match_Extension_instInhabitedState;
v___x_2844_ = lean_box(0);
v___x_2845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2844_);
lean_ctor_set(v___x_2845_, 1, v___x_2843_);
return v___x_2845_;
}
}
static lean_object* _init_l_main___closed__4(void){
_start:
{
lean_object* v___x_2846_; 
v___x_2846_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v___x_2846_;
}
}
static lean_object* _init_l_main___closed__5(void){
_start:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2847_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_2848_ = lean_box(0);
v___x_2849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2848_);
lean_ctor_set(v___x_2849_, 1, v___x_2847_);
return v___x_2849_;
}
}
static lean_object* _init_l_main___closed__6(void){
_start:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; 
v___x_2850_ = lean_obj_once(&l_main___closed__5, &l_main___closed__5_once, _init_l_main___closed__5);
v___x_2851_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2850_);
return v___x_2851_;
}
}
static lean_object* _init_l_main___closed__7(void){
_start:
{
lean_object* v___x_2852_; 
v___x_2852_ = l_Array_instInhabited___redArg();
return v___x_2852_;
}
}
static lean_object* _init_l_main___closed__13(void){
_start:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2861_ = l_Lean_Options_empty;
v___x_2862_ = l_Lean_Core_getMaxHeartbeats(v___x_2861_);
return v___x_2862_;
}
}
static uint16_t _init_l_main___closed__14(void){
_start:
{
lean_object* v___x_2863_; uint16_t v___x_2864_; 
v___x_2863_ = l_Lean_Options_empty;
v___x_2864_ = l_Lean_OptionFlags_ofOptions(v___x_2863_);
return v___x_2864_;
}
}
static lean_object* _init_l_main___closed__19(void){
_start:
{
lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2869_ = ((lean_object*)(l_main___closed__18));
v___x_2870_ = lean_unsigned_to_nat(27u);
v___x_2871_ = lean_unsigned_to_nat(151u);
v___x_2872_ = ((lean_object*)(l_main___closed__17));
v___x_2873_ = ((lean_object*)(l_main___closed__16));
v___x_2874_ = l_mkPanicMessageWithDecl(v___x_2873_, v___x_2872_, v___x_2871_, v___x_2870_, v___x_2869_);
return v___x_2874_;
}
}
static lean_object* _init_l_main___closed__21(void){
_start:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2876_ = ((lean_object*)(l_main___closed__18));
v___x_2877_ = lean_unsigned_to_nat(51u);
v___x_2878_ = lean_unsigned_to_nat(124u);
v___x_2879_ = ((lean_object*)(l_main___closed__17));
v___x_2880_ = ((lean_object*)(l_main___closed__16));
v___x_2881_ = l_mkPanicMessageWithDecl(v___x_2880_, v___x_2879_, v___x_2878_, v___x_2877_, v___x_2876_);
return v___x_2881_;
}
}
static lean_object* _init_l_main___closed__22(void){
_start:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2882_ = lean_unsigned_to_nat(1u);
v___x_2883_ = l_Lean_firstFrontendMacroScope;
v___x_2884_ = lean_nat_add(v___x_2883_, v___x_2882_);
return v___x_2884_;
}
}
static lean_object* _init_l_main___closed__26(void){
_start:
{
lean_object* v___x_2891_; uint64_t v___x_2892_; lean_object* v___x_2893_; 
v___x_2891_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1);
v___x_2892_ = 0ULL;
v___x_2893_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2893_, 0, v___x_2891_);
lean_ctor_set_uint64(v___x_2893_, sizeof(void*)*1, v___x_2892_);
return v___x_2893_;
}
}
static lean_object* _init_l_main___closed__27(void){
_start:
{
lean_object* v___x_2894_; 
v___x_2894_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2894_;
}
}
static lean_object* _init_l_main___closed__28(void){
_start:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2895_ = lean_obj_once(&l_main___closed__27, &l_main___closed__27_once, _init_l_main___closed__27);
v___x_2896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2895_);
return v___x_2896_;
}
}
static lean_object* _init_l_main___closed__29(void){
_start:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2897_ = lean_obj_once(&l_main___closed__28, &l_main___closed__28_once, _init_l_main___closed__28);
v___x_2898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2897_);
lean_ctor_set(v___x_2898_, 1, v___x_2897_);
return v___x_2898_;
}
}
static lean_object* _init_l_main___closed__31(void){
_start:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2901_ = l_Lean_NameSet_empty;
v___x_2902_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1);
v___x_2903_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2902_);
lean_ctor_set(v___x_2903_, 1, v___x_2902_);
lean_ctor_set(v___x_2903_, 2, v___x_2901_);
return v___x_2903_;
}
}
static lean_object* _init_l_main___closed__32(void){
_start:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; uint8_t v___x_2906_; lean_object* v___x_2907_; 
v___x_2904_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1);
v___x_2905_ = lean_obj_once(&l_main___closed__28, &l_main___closed__28_once, _init_l_main___closed__28);
v___x_2906_ = 1;
v___x_2907_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2907_, 0, v___x_2905_);
lean_ctor_set(v___x_2907_, 1, v___x_2905_);
lean_ctor_set(v___x_2907_, 2, v___x_2904_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*3, v___x_2906_);
return v___x_2907_;
}
}
static uint8_t _init_l_main___closed__36(void){
_start:
{
uint8_t v___x_2912_; uint8_t v___x_2913_; uint8_t v___x_2914_; 
v___x_2912_ = 2;
v___x_2913_ = 0;
v___x_2914_ = l_Lean_instOrdOLeanLevel_ord(v___x_2913_, v___x_2912_);
return v___x_2914_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_2915_; lean_object* v___x_2916_; 
v___x_2915_ = 0;
v___x_2916_ = lean_box_uint32(v___x_2915_);
return v___x_2916_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_2917_; lean_object* v___x_2918_; 
v___x_2917_ = 1;
v___x_2918_ = lean_box_uint32(v___x_2917_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_2919_){
_start:
{
if (lean_obj_tag(v_args_2919_) == 1)
{
lean_object* v_tail_2944_; 
v_tail_2944_ = lean_ctor_get(v_args_2919_, 1);
lean_inc(v_tail_2944_);
if (lean_obj_tag(v_tail_2944_) == 1)
{
lean_object* v_tail_2945_; 
v_tail_2945_ = lean_ctor_get(v_tail_2944_, 1);
lean_inc(v_tail_2945_);
if (lean_obj_tag(v_tail_2945_) == 1)
{
lean_object* v_head_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_3665_; 
v_head_2946_ = lean_ctor_get(v_args_2919_, 0);
v_isSharedCheck_3665_ = !lean_is_exclusive(v_args_2919_);
if (v_isSharedCheck_3665_ == 0)
{
lean_object* v_unused_3666_; 
v_unused_3666_ = lean_ctor_get(v_args_2919_, 1);
lean_dec(v_unused_3666_);
v___x_2948_ = v_args_2919_;
v_isShared_2949_ = v_isSharedCheck_3665_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_head_2946_);
lean_dec(v_args_2919_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_3665_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v_head_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_3663_; 
v_head_2950_ = lean_ctor_get(v_tail_2944_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v_tail_2944_);
if (v_isSharedCheck_3663_ == 0)
{
lean_object* v_unused_3664_; 
v_unused_3664_ = lean_ctor_get(v_tail_2944_, 1);
lean_dec(v_unused_3664_);
v___x_2952_ = v_tail_2944_;
v_isShared_2953_ = v_isSharedCheck_3663_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_head_2950_);
lean_dec(v_tail_2944_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_3663_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v_head_2954_; lean_object* v_tail_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_3662_; 
v_head_2954_ = lean_ctor_get(v_tail_2945_, 0);
v_tail_2955_ = lean_ctor_get(v_tail_2945_, 1);
v_isSharedCheck_3662_ = !lean_is_exclusive(v_tail_2945_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_2957_ = v_tail_2945_;
v_isShared_2958_ = v_isSharedCheck_3662_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_tail_2955_);
lean_inc(v_head_2954_);
lean_dec(v_tail_2945_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_3662_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2959_ = lean_obj_once(&l_main___closed__1, &l_main___closed__1_once, _init_l_main___closed__1);
v___x_2960_ = lean_box(0);
v___x_2961_ = lean_obj_once(&l_main___closed__2, &l_main___closed__2_once, _init_l_main___closed__2);
v___x_2962_ = lean_obj_once(&l_main___closed__3, &l_main___closed__3_once, _init_l_main___closed__3);
v___x_2963_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_2964_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_2965_ = lean_obj_once(&l_main___closed__7, &l_main___closed__7_once, _init_l_main___closed__7);
v___x_2966_ = lean_box(1);
v___x_2967_ = ((lean_object*)(l_main___closed__8));
v___x_2968_ = l_Lean_ModuleSetup_load(v_head_2946_);
lean_dec(v_head_2946_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v_a_2969_; lean_object* v_name_2970_; lean_object* v_package_x3f_2971_; lean_object* v_importArts_2972_; lean_object* v_options_2973_; uint8_t v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2978_; 
v_a_2969_ = lean_ctor_get(v___x_2968_, 0);
lean_inc(v_a_2969_);
lean_dec_ref_known(v___x_2968_, 1);
v_name_2970_ = lean_ctor_get(v_a_2969_, 0);
lean_inc(v_name_2970_);
v_package_x3f_2971_ = lean_ctor_get(v_a_2969_, 1);
lean_inc(v_package_x3f_2971_);
v_importArts_2972_ = lean_ctor_get(v_a_2969_, 3);
lean_inc(v_importArts_2972_);
v_options_2973_ = lean_ctor_get(v_a_2969_, 6);
lean_inc(v_options_2973_);
lean_dec(v_a_2969_);
v___x_2974_ = 0;
v___x_2975_ = l_Lean_LeanOptions_toOptions(v_options_2973_);
v___x_2976_ = lean_box(v___x_2974_);
if (v_isShared_2958_ == 0)
{
lean_ctor_set_tag(v___x_2957_, 0);
lean_ctor_set(v___x_2957_, 1, v___x_2975_);
lean_ctor_set(v___x_2957_, 0, v___x_2976_);
v___x_2978_ = v___x_2957_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v___x_2976_);
lean_ctor_set(v_reuseFailAlloc_3653_, 1, v___x_2975_);
v___x_2978_ = v_reuseFailAlloc_3653_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
lean_object* v___x_2979_; 
v___x_2979_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_tail_2955_, v___x_2978_);
lean_dec(v_tail_2955_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v_a_2980_; lean_object* v_fst_2981_; lean_object* v_snd_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_3644_; 
v_a_2980_ = lean_ctor_get(v___x_2979_, 0);
lean_inc(v_a_2980_);
lean_dec_ref_known(v___x_2979_, 1);
v_fst_2981_ = lean_ctor_get(v_a_2980_, 0);
v_snd_2982_ = lean_ctor_get(v_a_2980_, 1);
v_isSharedCheck_3644_ = !lean_is_exclusive(v_a_2980_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_2984_ = v_a_2980_;
v_isShared_2985_ = v_isSharedCheck_3644_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_snd_2982_);
lean_inc(v_fst_2981_);
lean_dec(v_a_2980_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_3644_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2986_; uint8_t v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; uint8_t v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3150_; lean_object* v___y_3151_; uint8_t v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v_nextMacroScope_3168_; lean_object* v_ngen_3169_; lean_object* v_auxDeclNGen_3170_; lean_object* v_traceState_3171_; lean_object* v_recordedDeps_3172_; lean_object* v_messages_3173_; lean_object* v_infoState_3174_; lean_object* v_snapshotTasks_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; uint8_t v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; uint16_t v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3275_; lean_object* v___y_3276_; uint8_t v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; uint8_t v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; uint16_t v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; uint8_t v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; uint8_t v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; uint16_t v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; uint8_t v___y_3344_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; uint8_t v___y_3354_; lean_object* v___y_3355_; uint16_t v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; uint8_t v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; uint8_t v___y_3368_; lean_object* v___y_3369_; uint8_t v___y_3370_; lean_object* v___x_3371_; 
v___x_2986_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_2987_ = 1;
v___x_2988_ = l_Lean_Option_set___at___00Lean_Environment_realizeConst_spec__0(v_snd_2982_, v___x_2986_, v___x_2987_);
v___x_2989_ = l_Lean_maxHeartbeats;
v___x_2990_ = lean_unsigned_to_nat(0u);
v___x_2991_ = l_Lean_Option_set___at___00main_spec__3(v___x_2988_, v___x_2989_, v___x_2990_);
v___x_3371_ = lean_init_search_path();
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; uint8_t v___x_3377_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; uint8_t v___x_3537_; uint8_t v___y_3539_; uint8_t v___x_3635_; 
lean_dec_ref_known(v___x_3371_, 1);
v___x_3372_ = ((lean_object*)(l_main___closed__20));
lean_inc(v_name_2970_);
v___x_3373_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_3373_, 0, v_name_2970_);
lean_ctor_set_uint8(v___x_3373_, sizeof(void*)*1, v___x_2987_);
lean_ctor_set_uint8(v___x_3373_, sizeof(void*)*1 + 1, v___x_2987_);
lean_ctor_set_uint8(v___x_3373_, sizeof(void*)*1 + 2, v___x_2974_);
v___x_3374_ = lean_unsigned_to_nat(1u);
v___x_3375_ = lean_mk_empty_array_with_capacity(v___x_3374_);
v___x_3376_ = lean_array_push(v___x_3375_, v___x_3373_);
v___x_3377_ = 0;
v___x_3537_ = 2;
v___x_3635_ = lean_uint8_once(&l_main___closed__36, &l_main___closed__36_once, _init_l_main___closed__36);
if (v___x_3635_ == 0)
{
v___y_3539_ = v___x_2987_;
goto v___jp_3538_;
}
else
{
v___y_3539_ = v___x_2974_;
goto v___jp_3538_;
}
v___jp_3378_:
{
lean_object* v___x_3387_; 
if (v_isShared_2949_ == 0)
{
lean_ctor_set_tag(v___x_2948_, 0);
lean_ctor_set(v___x_2948_, 1, v___y_3385_);
lean_ctor_set(v___x_2948_, 0, v___y_3383_);
v___x_3387_ = v___x_2948_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v___y_3383_);
lean_ctor_set(v_reuseFailAlloc_3486_, 1, v___y_3385_);
v___x_3387_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v_moduleData_3391_; lean_object* v___x_3392_; uint8_t v___x_3393_; 
v___x_3388_ = lean_box(0);
lean_inc_ref(v___y_3384_);
v___x_3389_ = l_Lean_EnvExtension_setState___redArg(v___y_3384_, v___y_3382_, v___x_3387_, v___x_3388_);
v___x_3390_ = l_Lean_Environment_header(v___x_3389_);
v_moduleData_3391_ = lean_ctor_get(v___x_3390_, 6);
lean_inc_ref(v_moduleData_3391_);
lean_dec_ref(v___x_3390_);
v___x_3392_ = lean_array_get_size(v_moduleData_3391_);
v___x_3393_ = lean_nat_dec_lt(v___y_3380_, v___x_3392_);
if (v___x_3393_ == 0)
{
lean_object* v___x_3394_; lean_object* v___x_3395_; 
lean_dec_ref(v_moduleData_3391_);
lean_dec_ref(v___x_3389_);
lean_dec(v___y_3381_);
lean_dec(v___y_3380_);
lean_dec(v___y_3379_);
lean_dec_ref(v___x_2991_);
lean_del_object(v___x_2984_);
lean_dec(v_fst_2981_);
lean_dec(v_name_2970_);
lean_dec(v_head_2954_);
lean_del_object(v___x_2952_);
lean_dec(v_head_2950_);
v___x_3394_ = lean_obj_once(&l_main___closed__21, &l_main___closed__21_once, _init_l_main___closed__21);
v___x_3395_ = l_panic___at___00main_spec__5(v___x_3394_);
return v___x_3395_;
}
else
{
lean_object* v_base_3396_; lean_object* v_private_3397_; lean_object* v_header_3398_; lean_object* v_serverBaseExts_3399_; lean_object* v_checked_3400_; lean_object* v_asyncConstsMap_3401_; lean_object* v_asyncCtx_x3f_3402_; lean_object* v_importRealizationCtx_x3f_3403_; lean_object* v_localRealizationCtxMap_3404_; lean_object* v_allRealizations_3405_; uint8_t v_isExporting_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3484_; 
v_base_3396_ = lean_ctor_get(v___x_3389_, 0);
lean_inc_ref(v_base_3396_);
v_private_3397_ = lean_ctor_get(v_base_3396_, 0);
lean_inc(v_private_3397_);
v_header_3398_ = lean_ctor_get(v_private_3397_, 5);
lean_inc_ref(v_header_3398_);
v_serverBaseExts_3399_ = lean_ctor_get(v___x_3389_, 1);
v_checked_3400_ = lean_ctor_get(v___x_3389_, 2);
v_asyncConstsMap_3401_ = lean_ctor_get(v___x_3389_, 3);
v_asyncCtx_x3f_3402_ = lean_ctor_get(v___x_3389_, 4);
v_importRealizationCtx_x3f_3403_ = lean_ctor_get(v___x_3389_, 5);
v_localRealizationCtxMap_3404_ = lean_ctor_get(v___x_3389_, 6);
v_allRealizations_3405_ = lean_ctor_get(v___x_3389_, 7);
v_isExporting_3406_ = lean_ctor_get_uint8(v___x_3389_, sizeof(void*)*8);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3389_);
if (v_isSharedCheck_3484_ == 0)
{
lean_object* v_unused_3485_; 
v_unused_3485_ = lean_ctor_get(v___x_3389_, 0);
lean_dec(v_unused_3485_);
v___x_3408_ = v___x_3389_;
v_isShared_3409_ = v_isSharedCheck_3484_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_allRealizations_3405_);
lean_inc(v_localRealizationCtxMap_3404_);
lean_inc(v_importRealizationCtx_x3f_3403_);
lean_inc(v_asyncCtx_x3f_3402_);
lean_inc(v_asyncConstsMap_3401_);
lean_inc(v_checked_3400_);
lean_inc(v_serverBaseExts_3399_);
lean_dec(v___x_3389_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3484_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v_public_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3482_; 
v_public_3410_ = lean_ctor_get(v_base_3396_, 1);
v_isSharedCheck_3482_ = !lean_is_exclusive(v_base_3396_);
if (v_isSharedCheck_3482_ == 0)
{
lean_object* v_unused_3483_; 
v_unused_3483_ = lean_ctor_get(v_base_3396_, 0);
lean_dec(v_unused_3483_);
v___x_3412_ = v_base_3396_;
v_isShared_3413_ = v_isSharedCheck_3482_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_public_3410_);
lean_dec(v_base_3396_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3482_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v_constants_3414_; uint8_t v_quotInit_3415_; lean_object* v_diagnostics_3416_; lean_object* v_const2ModIdx_3417_; lean_object* v_extensions_3418_; lean_object* v_irBaseExts_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3480_; 
v_constants_3414_ = lean_ctor_get(v_private_3397_, 0);
v_quotInit_3415_ = lean_ctor_get_uint8(v_private_3397_, sizeof(void*)*6);
v_diagnostics_3416_ = lean_ctor_get(v_private_3397_, 1);
v_const2ModIdx_3417_ = lean_ctor_get(v_private_3397_, 2);
v_extensions_3418_ = lean_ctor_get(v_private_3397_, 3);
v_irBaseExts_3419_ = lean_ctor_get(v_private_3397_, 4);
v_isSharedCheck_3480_ = !lean_is_exclusive(v_private_3397_);
if (v_isSharedCheck_3480_ == 0)
{
lean_object* v_unused_3481_; 
v_unused_3481_ = lean_ctor_get(v_private_3397_, 5);
lean_dec(v_unused_3481_);
v___x_3421_ = v_private_3397_;
v_isShared_3422_ = v_isSharedCheck_3480_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_irBaseExts_3419_);
lean_inc(v_extensions_3418_);
lean_inc(v_const2ModIdx_3417_);
lean_inc(v_diagnostics_3416_);
lean_inc(v_constants_3414_);
lean_dec(v_private_3397_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3480_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
uint32_t v_trustLevel_3423_; lean_object* v_mainModule_3424_; uint8_t v_isModule_3425_; lean_object* v_regions_3426_; lean_object* v_modules_3427_; lean_object* v_moduleName2Idx_3428_; lean_object* v_importAllModules_3429_; lean_object* v_moduleData_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3478_; 
v_trustLevel_3423_ = lean_ctor_get_uint32(v_header_3398_, sizeof(void*)*7);
v_mainModule_3424_ = lean_ctor_get(v_header_3398_, 0);
v_isModule_3425_ = lean_ctor_get_uint8(v_header_3398_, sizeof(void*)*7 + 4);
v_regions_3426_ = lean_ctor_get(v_header_3398_, 2);
v_modules_3427_ = lean_ctor_get(v_header_3398_, 3);
v_moduleName2Idx_3428_ = lean_ctor_get(v_header_3398_, 4);
v_importAllModules_3429_ = lean_ctor_get(v_header_3398_, 5);
v_moduleData_3430_ = lean_ctor_get(v_header_3398_, 6);
v_isSharedCheck_3478_ = !lean_is_exclusive(v_header_3398_);
if (v_isSharedCheck_3478_ == 0)
{
lean_object* v_unused_3479_; 
v_unused_3479_ = lean_ctor_get(v_header_3398_, 1);
lean_dec(v_unused_3479_);
v___x_3432_ = v_header_3398_;
v_isShared_3433_ = v_isSharedCheck_3478_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_moduleData_3430_);
lean_inc(v_importAllModules_3429_);
lean_inc(v_moduleName2Idx_3428_);
lean_inc(v_modules_3427_);
lean_inc(v_regions_3426_);
lean_inc(v_mainModule_3424_);
lean_dec(v_header_3398_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3478_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3434_; lean_object* v_imports_3435_; lean_object* v___x_3437_; 
v___x_3434_ = lean_array_fget(v_moduleData_3391_, v___y_3380_);
lean_dec_ref(v_moduleData_3391_);
v_imports_3435_ = lean_ctor_get(v___x_3434_, 0);
lean_inc_ref(v_imports_3435_);
lean_dec(v___x_3434_);
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 1, v_imports_3435_);
v___x_3437_ = v___x_3432_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(0, 7, 5);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_mainModule_3424_);
lean_ctor_set(v_reuseFailAlloc_3477_, 1, v_imports_3435_);
lean_ctor_set(v_reuseFailAlloc_3477_, 2, v_regions_3426_);
lean_ctor_set(v_reuseFailAlloc_3477_, 3, v_modules_3427_);
lean_ctor_set(v_reuseFailAlloc_3477_, 4, v_moduleName2Idx_3428_);
lean_ctor_set(v_reuseFailAlloc_3477_, 5, v_importAllModules_3429_);
lean_ctor_set(v_reuseFailAlloc_3477_, 6, v_moduleData_3430_);
lean_ctor_set_uint32(v_reuseFailAlloc_3477_, sizeof(void*)*7, v_trustLevel_3423_);
lean_ctor_set_uint8(v_reuseFailAlloc_3477_, sizeof(void*)*7 + 4, v_isModule_3425_);
v___x_3437_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
lean_object* v___x_3439_; 
if (v_isShared_3422_ == 0)
{
lean_ctor_set(v___x_3421_, 5, v___x_3437_);
v___x_3439_ = v___x_3421_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_constants_3414_);
lean_ctor_set(v_reuseFailAlloc_3476_, 1, v_diagnostics_3416_);
lean_ctor_set(v_reuseFailAlloc_3476_, 2, v_const2ModIdx_3417_);
lean_ctor_set(v_reuseFailAlloc_3476_, 3, v_extensions_3418_);
lean_ctor_set(v_reuseFailAlloc_3476_, 4, v_irBaseExts_3419_);
lean_ctor_set(v_reuseFailAlloc_3476_, 5, v___x_3437_);
lean_ctor_set_uint8(v_reuseFailAlloc_3476_, sizeof(void*)*6, v_quotInit_3415_);
v___x_3439_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
lean_object* v___x_3441_; 
if (v_isShared_3413_ == 0)
{
lean_ctor_set(v___x_3412_, 0, v___x_3439_);
v___x_3441_ = v___x_3412_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v___x_3439_);
lean_ctor_set(v_reuseFailAlloc_3475_, 1, v_public_3410_);
v___x_3441_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
lean_object* v___x_3443_; 
if (v_isShared_3409_ == 0)
{
lean_ctor_set(v___x_3408_, 0, v___x_3441_);
v___x_3443_ = v___x_3408_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v___x_3441_);
lean_ctor_set(v_reuseFailAlloc_3474_, 1, v_serverBaseExts_3399_);
lean_ctor_set(v_reuseFailAlloc_3474_, 2, v_checked_3400_);
lean_ctor_set(v_reuseFailAlloc_3474_, 3, v_asyncConstsMap_3401_);
lean_ctor_set(v_reuseFailAlloc_3474_, 4, v_asyncCtx_x3f_3402_);
lean_ctor_set(v_reuseFailAlloc_3474_, 5, v_importRealizationCtx_x3f_3403_);
lean_ctor_set(v_reuseFailAlloc_3474_, 6, v_localRealizationCtxMap_3404_);
lean_ctor_set(v_reuseFailAlloc_3474_, 7, v_allRealizations_3405_);
lean_ctor_set_uint8(v_reuseFailAlloc_3474_, sizeof(void*)*8, v_isExporting_3406_);
v___x_3443_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; uint16_t v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v_env_3468_; uint8_t v___x_3469_; uint16_t v___x_3470_; uint16_t v___x_3471_; uint16_t v___x_3472_; uint8_t v___x_3473_; 
v___x_3444_ = l_Lean_Compiler_LCNF_postponedCompileDeclsExt;
v___x_3445_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2967_, v___x_3444_, v___x_3443_, v___y_3380_, v___x_3377_);
lean_dec(v___y_3380_);
v___x_3446_ = l_Lean_instInhabitedFileMap_default;
v___x_3447_ = lean_unsigned_to_nat(1000u);
v___x_3448_ = l_Lean_Core_getMaxHeartbeats(v___x_2991_);
v___x_3449_ = l_Lean_firstFrontendMacroScope;
v___x_3450_ = lean_box(0);
v___x_3451_ = lean_box(0);
v___x_3452_ = l_Lean_OptionFlags_ofOptions(v___x_2991_);
v___x_3453_ = lean_obj_once(&l_main___closed__22, &l_main___closed__22_once, _init_l_main___closed__22);
v___x_3454_ = ((lean_object*)(l_main___closed__25));
lean_inc_n(v___y_3381_, 3);
v___x_3455_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3455_, 0, v___y_3381_);
lean_ctor_set(v___x_3455_, 1, v___x_3374_);
lean_ctor_set(v___x_3455_, 2, v___x_2960_);
v___x_3456_ = lean_obj_once(&l_main___closed__26, &l_main___closed__26_once, _init_l_main___closed__26);
v___x_3457_ = lean_obj_once(&l_main___closed__29, &l_main___closed__29_once, _init_l_main___closed__29);
v___x_3458_ = ((lean_object*)(l_main___closed__30));
v___x_3459_ = lean_obj_once(&l_main___closed__31, &l_main___closed__31_once, _init_l_main___closed__31);
v___x_3460_ = lean_obj_once(&l_main___closed__32, &l_main___closed__32_once, _init_l_main___closed__32);
lean_inc_ref(v___x_3455_);
v___x_3461_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3443_);
lean_ctor_set(v___x_3461_, 1, v___x_3453_);
lean_ctor_set(v___x_3461_, 2, v___x_3454_);
lean_ctor_set(v___x_3461_, 3, v___x_3455_);
lean_ctor_set(v___x_3461_, 4, v___x_3456_);
lean_ctor_set(v___x_3461_, 5, v___x_3457_);
lean_ctor_set(v___x_3461_, 6, v___x_3458_);
lean_ctor_set(v___x_3461_, 7, v___x_3459_);
lean_ctor_set(v___x_3461_, 8, v___x_3460_);
lean_ctor_set(v___x_3461_, 9, v___x_3458_);
v___x_3462_ = lean_st_mk_ref(v___x_3461_);
v___x_3463_ = l_Lean_inheritedTraceOptions;
v___x_3464_ = lean_st_ref_get(v___x_3463_);
lean_inc_ref(v___x_2991_);
lean_inc(v_head_2950_);
v___x_3465_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3465_, 0, v_head_2950_);
lean_ctor_set(v___x_3465_, 1, v___x_3446_);
lean_ctor_set(v___x_3465_, 2, v___x_2991_);
lean_ctor_set(v___x_3465_, 3, v___x_3447_);
lean_ctor_set(v___x_3465_, 4, v___y_3381_);
lean_ctor_set(v___x_3465_, 5, v___x_2960_);
lean_ctor_set(v___x_3465_, 6, v___x_2990_);
lean_ctor_set(v___x_3465_, 7, v___x_3448_);
lean_ctor_set(v___x_3465_, 8, v___y_3381_);
lean_ctor_set(v___x_3465_, 9, v___x_3449_);
lean_ctor_set(v___x_3465_, 10, v___x_3450_);
lean_ctor_set(v___x_3465_, 11, v___x_3464_);
v___x_3466_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3466_, 0, v___x_3465_);
lean_ctor_set(v___x_3466_, 1, v___x_2990_);
lean_ctor_set(v___x_3466_, 2, v___x_3451_);
lean_ctor_set_uint16(v___x_3466_, sizeof(void*)*3, v___x_3452_);
lean_ctor_set_uint8(v___x_3466_, sizeof(void*)*3 + 2, v___x_2974_);
lean_ctor_set_uint8(v___x_3466_, sizeof(void*)*3 + 3, v___x_2974_);
v___x_3467_ = lean_st_ref_get(v___x_3462_);
v_env_3468_ = lean_ctor_get(v___x_3467_, 0);
lean_inc_ref(v_env_3468_);
lean_dec(v___x_3467_);
v___x_3469_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3468_);
lean_dec_ref(v_env_3468_);
v___x_3470_ = 512;
v___x_3471_ = lean_uint16_land(v___x_3452_, v___x_3470_);
v___x_3472_ = 0;
v___x_3473_ = lean_uint16_dec_eq(v___x_3471_, v___x_3472_);
if (v___x_3473_ == 0)
{
if (v___x_3393_ == 0)
{
v___y_3346_ = v___x_3451_;
v___y_3347_ = v___x_3455_;
v___y_3348_ = v___x_3449_;
v___y_3349_ = v___x_3453_;
v___y_3350_ = v___x_3450_;
v___y_3351_ = v___x_3446_;
v___y_3352_ = v___y_3379_;
v___y_3353_ = v___x_2960_;
v___y_3354_ = v___x_3393_;
v___y_3355_ = v___x_3454_;
v___y_3356_ = v___x_3452_;
v___y_3357_ = v___x_3456_;
v___y_3358_ = v___x_3457_;
v___y_3359_ = v___x_3444_;
v___y_3360_ = v___x_3445_;
v___y_3361_ = v___x_3459_;
v___y_3362_ = v___x_3469_;
v___y_3363_ = v___x_3466_;
v___y_3364_ = v___x_3460_;
v___y_3365_ = v___x_3458_;
v___y_3366_ = v___y_3381_;
v___y_3367_ = v___x_3458_;
v___y_3368_ = v___x_3393_;
v___y_3369_ = v___x_3462_;
v___y_3370_ = v___x_3393_;
goto v___jp_3345_;
}
else
{
v___y_3320_ = v___y_3379_;
v___y_3321_ = v___x_2960_;
v___y_3322_ = v___x_3451_;
v___y_3323_ = v___x_3393_;
v___y_3324_ = v___x_3449_;
v___y_3325_ = v___x_3457_;
v___y_3326_ = v___x_3450_;
v___y_3327_ = v___x_3446_;
v___y_3328_ = v___x_3459_;
v___y_3329_ = v___x_3393_;
v___y_3330_ = v___x_3455_;
v___y_3331_ = v___x_3466_;
v___y_3332_ = v___x_3453_;
v___y_3333_ = v___x_3460_;
v___y_3334_ = v___x_3458_;
v___y_3335_ = v___y_3381_;
v___y_3336_ = v___x_3458_;
v___y_3337_ = v___x_3462_;
v___y_3338_ = v___x_3454_;
v___y_3339_ = v___x_3452_;
v___y_3340_ = v___x_3456_;
v___y_3341_ = v___x_3457_;
v___y_3342_ = v___x_3444_;
v___y_3343_ = v___x_3445_;
v___y_3344_ = v___x_3469_;
goto v___jp_3319_;
}
}
else
{
v___y_3346_ = v___x_3451_;
v___y_3347_ = v___x_3455_;
v___y_3348_ = v___x_3449_;
v___y_3349_ = v___x_3453_;
v___y_3350_ = v___x_3450_;
v___y_3351_ = v___x_3446_;
v___y_3352_ = v___y_3379_;
v___y_3353_ = v___x_2960_;
v___y_3354_ = v___x_3393_;
v___y_3355_ = v___x_3454_;
v___y_3356_ = v___x_3452_;
v___y_3357_ = v___x_3456_;
v___y_3358_ = v___x_3457_;
v___y_3359_ = v___x_3444_;
v___y_3360_ = v___x_3445_;
v___y_3361_ = v___x_3459_;
v___y_3362_ = v___x_3469_;
v___y_3363_ = v___x_3466_;
v___y_3364_ = v___x_3460_;
v___y_3365_ = v___x_3458_;
v___y_3366_ = v___y_3381_;
v___y_3367_ = v___x_3458_;
v___y_3368_ = v___x_3393_;
v___y_3369_ = v___x_3462_;
v___y_3370_ = v___x_2974_;
goto v___jp_3345_;
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
v___jp_3487_:
{
lean_object* v___x_3492_; lean_object* v_toEnvExtension_3493_; lean_object* v_asyncMode_3494_; lean_object* v___x_3495_; lean_object* v_importedEntries_3496_; lean_object* v_state_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; uint8_t v___x_3500_; 
v___x_3492_ = l_Lean_IR_declMapExt;
v_toEnvExtension_3493_ = lean_ctor_get(v___x_3492_, 0);
v_asyncMode_3494_ = lean_ctor_get(v_toEnvExtension_3493_, 2);
lean_inc(v___y_3490_);
lean_inc_ref(v___y_3491_);
v___x_3495_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2964_, v_toEnvExtension_3493_, v___y_3491_, v_asyncMode_3494_, v___y_3490_);
v_importedEntries_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc_ref(v_importedEntries_3496_);
v_state_3497_ = lean_ctor_get(v___x_3495_, 1);
lean_inc(v_state_3497_);
lean_dec(v___x_3495_);
v___x_3498_ = lean_array_get_borrowed(v___x_2965_, v_importedEntries_3496_, v___y_3489_);
v___x_3499_ = lean_array_get_size(v___x_3498_);
v___x_3500_ = lean_nat_dec_lt(v___x_2990_, v___x_3499_);
if (v___x_3500_ == 0)
{
v___y_3379_ = v___y_3488_;
v___y_3380_ = v___y_3489_;
v___y_3381_ = v___y_3490_;
v___y_3382_ = v___y_3491_;
v___y_3383_ = v_importedEntries_3496_;
v___y_3384_ = v_toEnvExtension_3493_;
v___y_3385_ = v_state_3497_;
goto v___jp_3378_;
}
else
{
uint8_t v___x_3501_; 
v___x_3501_ = lean_nat_dec_le(v___x_3499_, v___x_3499_);
if (v___x_3501_ == 0)
{
if (v___x_3500_ == 0)
{
v___y_3379_ = v___y_3488_;
v___y_3380_ = v___y_3489_;
v___y_3381_ = v___y_3490_;
v___y_3382_ = v___y_3491_;
v___y_3383_ = v_importedEntries_3496_;
v___y_3384_ = v_toEnvExtension_3493_;
v___y_3385_ = v_state_3497_;
goto v___jp_3378_;
}
else
{
size_t v___x_3502_; size_t v___x_3503_; lean_object* v___x_3504_; 
v___x_3502_ = ((size_t)0ULL);
v___x_3503_ = lean_usize_of_nat(v___x_3499_);
lean_inc_ref(v___y_3491_);
v___x_3504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3491_, v___x_3498_, v___x_3502_, v___x_3503_, v_state_3497_);
v___y_3379_ = v___y_3488_;
v___y_3380_ = v___y_3489_;
v___y_3381_ = v___y_3490_;
v___y_3382_ = v___y_3491_;
v___y_3383_ = v_importedEntries_3496_;
v___y_3384_ = v_toEnvExtension_3493_;
v___y_3385_ = v___x_3504_;
goto v___jp_3378_;
}
}
else
{
size_t v___x_3505_; size_t v___x_3506_; lean_object* v___x_3507_; 
v___x_3505_ = ((size_t)0ULL);
v___x_3506_ = lean_usize_of_nat(v___x_3499_);
lean_inc_ref(v___y_3491_);
v___x_3507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3491_, v___x_3498_, v___x_3505_, v___x_3506_, v_state_3497_);
v___y_3379_ = v___y_3488_;
v___y_3380_ = v___y_3489_;
v___y_3381_ = v___y_3490_;
v___y_3382_ = v___y_3491_;
v___y_3383_ = v_importedEntries_3496_;
v___y_3384_ = v_toEnvExtension_3493_;
v___y_3385_ = v___x_3507_;
goto v___jp_3378_;
}
}
}
v___jp_3508_:
{
uint8_t v___x_3515_; 
v___x_3515_ = lean_nat_dec_lt(v___x_2990_, v___y_3513_);
if (v___x_3515_ == 0)
{
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3512_);
v___y_3488_ = v___y_3509_;
v___y_3489_ = v___y_3510_;
v___y_3490_ = v___y_3511_;
v___y_3491_ = v___y_3514_;
goto v___jp_3487_;
}
else
{
uint8_t v___x_3516_; 
v___x_3516_ = lean_nat_dec_le(v___y_3513_, v___y_3513_);
if (v___x_3516_ == 0)
{
if (v___x_3515_ == 0)
{
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3512_);
v___y_3488_ = v___y_3509_;
v___y_3489_ = v___y_3510_;
v___y_3490_ = v___y_3511_;
v___y_3491_ = v___y_3514_;
goto v___jp_3487_;
}
else
{
size_t v___x_3517_; size_t v___x_3518_; lean_object* v___x_3519_; 
v___x_3517_ = ((size_t)0ULL);
v___x_3518_ = lean_usize_of_nat(v___y_3513_);
lean_dec(v___y_3513_);
v___x_3519_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3512_, v___x_3517_, v___x_3518_, v___y_3514_);
lean_dec_ref(v___y_3512_);
v___y_3488_ = v___y_3509_;
v___y_3489_ = v___y_3510_;
v___y_3490_ = v___y_3511_;
v___y_3491_ = v___x_3519_;
goto v___jp_3487_;
}
}
else
{
size_t v___x_3520_; size_t v___x_3521_; lean_object* v___x_3522_; 
v___x_3520_ = ((size_t)0ULL);
v___x_3521_ = lean_usize_of_nat(v___y_3513_);
lean_dec(v___y_3513_);
v___x_3522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3512_, v___x_3520_, v___x_3521_, v___y_3514_);
lean_dec_ref(v___y_3512_);
v___y_3488_ = v___y_3509_;
v___y_3489_ = v___y_3510_;
v___y_3490_ = v___y_3511_;
v___y_3491_ = v___x_3522_;
goto v___jp_3487_;
}
}
}
v___jp_3523_:
{
lean_object* v___x_3528_; uint8_t v___x_3529_; 
v___x_3528_ = lean_array_get_size(v___y_3527_);
v___x_3529_ = lean_nat_dec_lt(v___x_2990_, v___x_3528_);
if (v___x_3529_ == 0)
{
lean_inc(v___y_3524_);
v___y_3509_ = v___y_3524_;
v___y_3510_ = v___y_3525_;
v___y_3511_ = v___y_3524_;
v___y_3512_ = v___y_3527_;
v___y_3513_ = v___x_3528_;
v___y_3514_ = v___y_3526_;
goto v___jp_3508_;
}
else
{
uint8_t v___x_3530_; 
v___x_3530_ = lean_nat_dec_le(v___x_3528_, v___x_3528_);
if (v___x_3530_ == 0)
{
if (v___x_3529_ == 0)
{
lean_inc(v___y_3524_);
v___y_3509_ = v___y_3524_;
v___y_3510_ = v___y_3525_;
v___y_3511_ = v___y_3524_;
v___y_3512_ = v___y_3527_;
v___y_3513_ = v___x_3528_;
v___y_3514_ = v___y_3526_;
goto v___jp_3508_;
}
else
{
size_t v___x_3531_; size_t v___x_3532_; lean_object* v___x_3533_; 
v___x_3531_ = ((size_t)0ULL);
v___x_3532_ = lean_usize_of_nat(v___x_3528_);
v___x_3533_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3527_, v___x_3531_, v___x_3532_, v___y_3526_);
lean_inc(v___y_3524_);
v___y_3509_ = v___y_3524_;
v___y_3510_ = v___y_3525_;
v___y_3511_ = v___y_3524_;
v___y_3512_ = v___y_3527_;
v___y_3513_ = v___x_3528_;
v___y_3514_ = v___x_3533_;
goto v___jp_3508_;
}
}
else
{
size_t v___x_3534_; size_t v___x_3535_; lean_object* v___x_3536_; 
v___x_3534_ = ((size_t)0ULL);
v___x_3535_ = lean_usize_of_nat(v___x_3528_);
v___x_3536_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3527_, v___x_3534_, v___x_3535_, v___y_3526_);
lean_inc(v___y_3524_);
v___y_3509_ = v___y_3524_;
v___y_3510_ = v___y_3525_;
v___y_3511_ = v___y_3524_;
v___y_3512_ = v___y_3527_;
v___y_3513_ = v___x_3528_;
v___y_3514_ = v___x_3536_;
goto v___jp_3508_;
}
}
}
v___jp_3538_:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___f_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; 
v___x_3540_ = l_Lean_instInhabitedImportState_default;
v___x_3541_ = lean_box(v___x_3377_);
v___x_3542_ = lean_box(v___y_3539_);
v___x_3543_ = lean_box(v___x_2987_);
v___x_3544_ = lean_box(v___x_3537_);
v___x_3545_ = lean_box(v___x_2974_);
lean_inc_ref(v___x_2991_);
lean_inc(v_name_2970_);
v___f_3546_ = lean_alloc_closure((void*)(l_main___lam__0___boxed), 11, 10);
lean_closure_set(v___f_3546_, 0, v___x_3540_);
lean_closure_set(v___f_3546_, 1, v___x_3376_);
lean_closure_set(v___f_3546_, 2, v___x_3541_);
lean_closure_set(v___f_3546_, 3, v_importArts_2972_);
lean_closure_set(v___f_3546_, 4, v___x_3542_);
lean_closure_set(v___f_3546_, 5, v___x_3543_);
lean_closure_set(v___f_3546_, 6, v_name_2970_);
lean_closure_set(v___f_3546_, 7, v___x_3544_);
lean_closure_set(v___f_3546_, 8, v___x_2991_);
lean_closure_set(v___f_3546_, 9, v___x_3545_);
v___x_3547_ = lean_alloc_closure((void*)(l_Lean_withImporting___boxed), 3, 2);
lean_closure_set(v___x_3547_, 0, lean_box(0));
lean_closure_set(v___x_3547_, 1, v___f_3546_);
v___x_3548_ = lean_box(0);
v___x_3549_ = l_Lean_profileitIOUnsafe___redArg(v___x_3372_, v___x_2991_, v___x_3547_, v___x_3548_);
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_object* v_a_3550_; lean_object* v___x_3551_; lean_object* v_ext_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; 
v_a_3550_ = lean_ctor_get(v___x_3549_, 0);
lean_inc(v_a_3550_);
lean_dec_ref_known(v___x_3549_, 1);
v___x_3551_ = l_Lean_Compiler_CSimp_ext;
v_ext_3552_ = lean_ctor_get(v___x_3551_, 1);
lean_inc(v_name_2970_);
v___x_3553_ = l_Lean_Environment_setMainModule(v_a_3550_, v_name_2970_);
v___x_3554_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v___x_3555_ = l_Lean_PersistentEnvExtension_setState___redArg(v___x_3554_, v___x_3553_, v_package_x3f_2971_);
lean_inc_ref(v_ext_3552_);
v___x_3556_ = l_main___elam__0___redArg(v___x_3548_, v___x_2959_, v_ext_3552_, v___x_3555_);
if (lean_obj_tag(v___x_3556_) == 0)
{
lean_object* v_a_3557_; lean_object* v___x_3558_; lean_object* v_ext_3559_; lean_object* v___x_3560_; 
v_a_3557_ = lean_ctor_get(v___x_3556_, 0);
lean_inc(v_a_3557_);
lean_dec_ref_known(v___x_3556_, 1);
v___x_3558_ = l_Lean_Meta_instanceExtension;
v_ext_3559_ = lean_ctor_get(v___x_3558_, 1);
lean_inc_ref(v_ext_3559_);
v___x_3560_ = l_main___elam__0___redArg(v___x_3548_, v___x_2959_, v_ext_3559_, v_a_3557_);
if (lean_obj_tag(v___x_3560_) == 0)
{
lean_object* v_a_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; 
v_a_3561_ = lean_ctor_get(v___x_3560_, 0);
lean_inc(v_a_3561_);
lean_dec_ref_known(v___x_3560_, 1);
v___x_3562_ = l_Lean_classExtension;
v___x_3563_ = l_main___elam__0___redArg(v___x_3548_, v___x_2961_, v___x_3562_, v_a_3561_);
if (lean_obj_tag(v___x_3563_) == 0)
{
lean_object* v_a_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; 
v_a_3564_ = lean_ctor_get(v___x_3563_, 0);
lean_inc(v_a_3564_);
lean_dec_ref_known(v___x_3563_, 1);
v___x_3565_ = l_Lean_Meta_Match_Extension_extension;
v___x_3566_ = l_main___elam__0___redArg(v___x_3548_, v___x_2962_, v___x_3565_, v_a_3564_);
if (lean_obj_tag(v___x_3566_) == 0)
{
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3594_; 
v_a_3567_ = lean_ctor_get(v___x_3566_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3566_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3569_ = v___x_3566_;
v_isShared_3570_ = v_isSharedCheck_3594_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___x_3566_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3594_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3571_; 
v___x_3571_ = l_Lean_Environment_getModuleIdx_x3f(v_a_3567_, v_name_2970_);
if (lean_obj_tag(v___x_3571_) == 1)
{
lean_object* v_val_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; uint8_t v___x_3577_; 
lean_del_object(v___x_3569_);
v_val_3572_ = lean_ctor_get(v___x_3571_, 0);
lean_inc(v_val_3572_);
lean_dec_ref_known(v___x_3571_, 1);
v___x_3573_ = l_Lean_Compiler_LCNF_impureSigExt;
v___x_3574_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2963_, v___x_3573_, v_a_3567_, v_val_3572_, v___x_3377_);
v___x_3575_ = lean_array_get_size(v___x_3574_);
v___x_3576_ = ((lean_object*)(l_main___closed__33));
v___x_3577_ = lean_nat_dec_lt(v___x_2990_, v___x_3575_);
if (v___x_3577_ == 0)
{
lean_dec_ref(v___x_3574_);
v___y_3524_ = v___x_3548_;
v___y_3525_ = v_val_3572_;
v___y_3526_ = v_a_3567_;
v___y_3527_ = v___x_3576_;
goto v___jp_3523_;
}
else
{
uint8_t v___x_3578_; 
v___x_3578_ = lean_nat_dec_le(v___x_3575_, v___x_3575_);
if (v___x_3578_ == 0)
{
if (v___x_3577_ == 0)
{
lean_dec_ref(v___x_3574_);
v___y_3524_ = v___x_3548_;
v___y_3525_ = v_val_3572_;
v___y_3526_ = v_a_3567_;
v___y_3527_ = v___x_3576_;
goto v___jp_3523_;
}
else
{
size_t v___x_3579_; size_t v___x_3580_; lean_object* v___x_3581_; 
v___x_3579_ = ((size_t)0ULL);
v___x_3580_ = lean_usize_of_nat(v___x_3575_);
lean_inc(v_a_3567_);
v___x_3581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_a_3567_, v___x_3574_, v___x_3579_, v___x_3580_, v___x_3576_);
lean_dec_ref(v___x_3574_);
v___y_3524_ = v___x_3548_;
v___y_3525_ = v_val_3572_;
v___y_3526_ = v_a_3567_;
v___y_3527_ = v___x_3581_;
goto v___jp_3523_;
}
}
else
{
size_t v___x_3582_; size_t v___x_3583_; lean_object* v___x_3584_; 
v___x_3582_ = ((size_t)0ULL);
v___x_3583_ = lean_usize_of_nat(v___x_3575_);
lean_inc(v_a_3567_);
v___x_3584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_a_3567_, v___x_3574_, v___x_3582_, v___x_3583_, v___x_3576_);
lean_dec_ref(v___x_3574_);
v___y_3524_ = v___x_3548_;
v___y_3525_ = v_val_3572_;
v___y_3526_ = v_a_3567_;
v___y_3527_ = v___x_3584_;
goto v___jp_3523_;
}
}
}
else
{
lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3592_; 
lean_dec(v___x_3571_);
lean_dec(v_a_3567_);
lean_dec_ref(v___x_2991_);
lean_del_object(v___x_2984_);
lean_dec(v_fst_2981_);
lean_dec(v_head_2954_);
lean_del_object(v___x_2952_);
lean_dec(v_head_2950_);
lean_del_object(v___x_2948_);
v___x_3585_ = ((lean_object*)(l_main___closed__34));
v___x_3586_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2970_, v___x_2987_);
v___x_3587_ = lean_string_append(v___x_3585_, v___x_3586_);
lean_dec_ref(v___x_3586_);
v___x_3588_ = ((lean_object*)(l_main___closed__35));
v___x_3589_ = lean_string_append(v___x_3587_, v___x_3588_);
v___x_3590_ = lean_mk_io_user_error(v___x_3589_);
if (v_isShared_3570_ == 0)
{
lean_ctor_set_tag(v___x_3569_, 1);
lean_ctor_set(v___x_3569_, 0, v___x_3590_);
v___x_3592_ = v___x_3569_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v___x_3590_);
v___x_3592_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
return v___x_3592_;
}
}
}
}
else
{
lean_object* v_a_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3602_; 
lean_dec_ref(v___x_2991_);
lean_del_object(v___x_2984_);
lean_dec(v_fst_2981_);
lean_dec(v_name_2970_);
lean_dec(v_head_2954_);
lean_del_object(v___x_2952_);
lean_dec(v_head_2950_);
lean_del_object(v___x_2948_);
v_a_3595_ = lean_ctor_get(v___x_3566_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3566_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3597_ = v___x_3566_;
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_a_3595_);
lean_dec(v___x_3566_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3600_; 
if (v_isShared_3598_ == 0)
{
v___x_3600_ = v___x_3597_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_a_3595_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
}
else
{
lean_object* v_a_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3610_; 
lean_dec_ref(v___x_2991_);
lean_del_object(v___x_2984_);
lean_dec(v_fst_2981_);
lean_dec(v_name_2970_);
lean_dec(v_head_2954_);
lean_del_object(v___x_2952_);
lean_dec(v_head_2950_);
lean_del_object(v___x_2948_);
v_a_3603_ = lean_ctor_get(v___x_3563_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3563_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3605_ = v___x_3563_;
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_a_3603_);
lean_dec(v___x_3563_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3608_; 
if (v_isShared_3606_ == 0)
{
v___x_3608_ = v___x_3605_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_a_3603_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
}
else
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
lean_dec_ref(v___x_2991_);
lean_del_object(v___x_2984_);
lean_dec(v_fst_2981_);
lean_dec(v_name_2970_);
lean_dec(v_head_2954_);
lean_del_object(v___x_2952_);
lean_dec(v_head_2950_);
lean_del_object(v___x_2948_);
v_a_3611_ = lean_ctor_get(v___x_3560_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3560_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3613_ = v___x_3560_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3560_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
if (v_isShared_3614_ == 0)
{
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3611_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
}
else
{
lean_object* v_a_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3626_; 
lean_dec_ref(v___x_2991_);
lean_del_object(v___x_2984_);
lean_dec(v_fst_2981_);
lean_dec(v_name_2970_);
lean_dec(v_head_2954_);
lean_del_object(v___x_2952_);
lean_dec(v_head_2950_);
lean_del_object(v___x_2948_);
v_a_3619_ = lean_ctor_get(v___x_3556_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3621_ = v___x_3556_;
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_a_3619_);
lean_dec(v___x_3556_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3624_; 
if (v_isShared_3622_ == 0)
{
v___x_3624_ = v___x_3621_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_a_3619_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
}
}
}
}
else
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3634_; 
lean_dec_ref(v___x_2991_);
lean_del_object(v___x_2984_);
lean_dec(v_fst_2981_);
lean_dec(v_package_x3f_2971_);
lean_dec(v_name_2970_);
lean_dec(v_head_2954_);
lean_del_object(v___x_2952_);
lean_dec(v_head_2950_);
lean_del_object(v___x_2948_);
v_a_3627_ = lean_ctor_get(v___x_3549_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3549_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3629_ = v___x_3549_;
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3549_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3632_; 
if (v_isShared_3630_ == 0)
{
v___x_3632_ = v___x_3629_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_a_3627_);
v___x_3632_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
return v___x_3632_;
}
}
}
}
}
else
{
lean_object* v_a_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3643_; 
lean_dec_ref(v___x_2991_);
lean_del_object(v___x_2984_);
lean_dec(v_fst_2981_);
lean_dec(v_importArts_2972_);
lean_dec(v_package_x3f_2971_);
lean_dec(v_name_2970_);
lean_dec(v_head_2954_);
lean_del_object(v___x_2952_);
lean_dec(v_head_2950_);
lean_del_object(v___x_2948_);
v_a_3636_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3638_ = v___x_3371_;
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_a_3636_);
lean_dec(v___x_3371_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v___x_3641_; 
if (v_isShared_3639_ == 0)
{
v___x_3641_ = v___x_3638_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_a_3636_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
return v___x_3641_;
}
}
}
v___jp_2992_:
{
lean_object* v___x_3012_; lean_object* v_messages_3013_; lean_object* v_env_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3140_; 
v___x_3012_ = lean_st_ref_get(v___y_3005_);
lean_dec(v___y_3005_);
v_messages_3013_ = lean_ctor_get(v___x_3012_, 7);
v_env_3014_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3140_ == 0)
{
lean_object* v_unused_3141_; lean_object* v_unused_3142_; lean_object* v_unused_3143_; lean_object* v_unused_3144_; lean_object* v_unused_3145_; lean_object* v_unused_3146_; lean_object* v_unused_3147_; lean_object* v_unused_3148_; 
v_unused_3141_ = lean_ctor_get(v___x_3012_, 9);
lean_dec(v_unused_3141_);
v_unused_3142_ = lean_ctor_get(v___x_3012_, 8);
lean_dec(v_unused_3142_);
v_unused_3143_ = lean_ctor_get(v___x_3012_, 6);
lean_dec(v_unused_3143_);
v_unused_3144_ = lean_ctor_get(v___x_3012_, 5);
lean_dec(v_unused_3144_);
v_unused_3145_ = lean_ctor_get(v___x_3012_, 4);
lean_dec(v_unused_3145_);
v_unused_3146_ = lean_ctor_get(v___x_3012_, 3);
lean_dec(v_unused_3146_);
v_unused_3147_ = lean_ctor_get(v___x_3012_, 2);
lean_dec(v_unused_3147_);
v_unused_3148_ = lean_ctor_get(v___x_3012_, 1);
lean_dec(v_unused_3148_);
v___x_3016_ = v___x_3012_;
v_isShared_3017_ = v_isSharedCheck_3140_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_messages_3013_);
lean_inc(v_env_3014_);
lean_dec(v___x_3012_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3140_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v_unreported_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
v_unreported_3018_ = lean_ctor_get(v_messages_3013_, 1);
v___x_3019_ = lean_box(0);
v___x_3020_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_unreported_3018_, v___x_3019_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3130_; 
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3130_ == 0)
{
lean_object* v_unused_3131_; 
v_unused_3131_ = lean_ctor_get(v___x_3020_, 0);
lean_dec(v_unused_3131_);
v___x_3022_ = v___x_3020_;
v_isShared_3023_ = v_isSharedCheck_3130_;
goto v_resetjp_3021_;
}
else
{
lean_dec(v___x_3020_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3130_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
uint8_t v___x_3024_; 
v___x_3024_ = l_Lean_MessageLog_hasErrors(v_messages_3013_);
lean_dec_ref(v_messages_3013_);
if (v___x_3024_ == 0)
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
lean_del_object(v___x_3022_);
v___x_3025_ = ((lean_object*)(l_main___closed__9));
lean_inc(v_head_2950_);
v___x_3026_ = l_System_FilePath_addExtension(v_head_2950_, v___x_3025_);
lean_inc_ref(v_env_3014_);
v___x_3027_ = l___private_LeanIR_0__mkIRSigData(v_env_3014_);
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_object* v_a_3028_; lean_object* v___x_3029_; 
v_a_3028_ = lean_ctor_get(v___x_3027_, 0);
lean_inc(v_a_3028_);
lean_dec_ref_known(v___x_3027_, 1);
lean_inc_ref(v_env_3014_);
v___x_3029_ = l___private_LeanIR_0__mkIRData(v_env_3014_);
if (lean_obj_tag(v___x_3029_) == 0)
{
lean_object* v_a_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3035_; 
v_a_3030_ = lean_ctor_get(v___x_3029_, 0);
lean_inc(v_a_3030_);
lean_dec_ref_known(v___x_3029_, 1);
v___x_3031_ = l_Lean_Environment_mainModule(v_env_3014_);
v___x_3032_ = ((lean_object*)(l_main___closed__11));
v___x_3033_ = l_Lean_Name_append(v___x_3031_, v___x_3032_);
if (v_isShared_2985_ == 0)
{
lean_ctor_set(v___x_2984_, 1, v_a_3028_);
lean_ctor_set(v___x_2984_, 0, v___x_3026_);
v___x_3035_ = v___x_2984_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v___x_3026_);
lean_ctor_set(v_reuseFailAlloc_3109_, 1, v_a_3028_);
v___x_3035_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
lean_object* v___x_3037_; 
lean_inc(v_head_2950_);
if (v_isShared_2953_ == 0)
{
lean_ctor_set_tag(v___x_2952_, 0);
lean_ctor_set(v___x_2952_, 1, v_a_3030_);
v___x_3037_ = v___x_2952_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_head_2950_);
lean_ctor_set(v_reuseFailAlloc_3108_, 1, v_a_3030_);
v___x_3037_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3038_ = lean_unsigned_to_nat(2u);
v___x_3039_ = lean_mk_empty_array_with_capacity(v___x_3038_);
v___x_3040_ = lean_array_push(v___x_3039_, v___x_3035_);
v___x_3041_ = lean_array_push(v___x_3040_, v___x_3037_);
v___x_3042_ = l_Lean_saveModuleDataParts(v___x_3033_, v___x_3041_);
lean_dec_ref(v___x_3041_);
lean_dec(v___x_3033_);
if (lean_obj_tag(v___x_3042_) == 0)
{
uint8_t v___x_3043_; lean_object* v___x_3044_; 
lean_dec_ref_known(v___x_3042_, 1);
v___x_3043_ = 1;
v___x_3044_ = lean_io_prim_handle_mk(v_head_2954_, v___x_3043_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; uint16_t v___x_3049_; lean_object* v___x_3051_; 
lean_dec(v_head_2954_);
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
lean_inc(v_a_3045_);
lean_dec_ref_known(v___x_3044_, 1);
v___x_3046_ = ((lean_object*)(l_main___closed__12));
v___x_3047_ = l_Lean_Options_empty;
v___x_3048_ = lean_obj_once(&l_main___closed__13, &l_main___closed__13_once, _init_l_main___closed__13);
v___x_3049_ = lean_uint16_once(&l_main___closed__14, &l_main___closed__14_once, _init_l_main___closed__14);
lean_inc_ref(v___y_3011_);
lean_inc_ref(v___y_3010_);
lean_inc_ref(v___y_3001_);
lean_inc_ref(v___y_3003_);
lean_inc_ref(v___y_3008_);
lean_inc_ref(v___y_3007_);
lean_inc_ref(v___y_3006_);
lean_inc(v___y_3009_);
lean_inc_ref(v_env_3014_);
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 9, v___y_3011_);
lean_ctor_set(v___x_3016_, 8, v___y_3010_);
lean_ctor_set(v___x_3016_, 7, v___y_3001_);
lean_ctor_set(v___x_3016_, 6, v___y_3003_);
lean_ctor_set(v___x_3016_, 5, v___y_3008_);
lean_ctor_set(v___x_3016_, 4, v___y_3007_);
lean_ctor_set(v___x_3016_, 3, v___y_3004_);
lean_ctor_set(v___x_3016_, 2, v___y_3006_);
lean_ctor_set(v___x_3016_, 1, v___y_3009_);
v___x_3051_ = v___x_3016_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_env_3014_);
lean_ctor_set(v_reuseFailAlloc_3077_, 1, v___y_3009_);
lean_ctor_set(v_reuseFailAlloc_3077_, 2, v___y_3006_);
lean_ctor_set(v_reuseFailAlloc_3077_, 3, v___y_3004_);
lean_ctor_set(v_reuseFailAlloc_3077_, 4, v___y_3007_);
lean_ctor_set(v_reuseFailAlloc_3077_, 5, v___y_3008_);
lean_ctor_set(v_reuseFailAlloc_3077_, 6, v___y_3003_);
lean_ctor_set(v_reuseFailAlloc_3077_, 7, v___y_3001_);
lean_ctor_set(v_reuseFailAlloc_3077_, 8, v___y_3010_);
lean_ctor_set(v_reuseFailAlloc_3077_, 9, v___y_3011_);
v___x_3051_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___f_3056_; lean_object* v___x_3057_; 
v___x_3052_ = lean_box(v___x_3049_);
v___x_3053_ = lean_box(v___y_2996_);
v___x_3054_ = lean_box(v___x_2974_);
v___x_3055_ = lean_box(v___x_3024_);
lean_inc(v___y_2995_);
lean_inc(v___y_2999_);
lean_inc(v___y_2997_);
lean_inc(v___y_2994_);
lean_inc_ref(v___y_3000_);
lean_inc_ref(v___y_2998_);
v___f_3056_ = lean_alloc_closure((void*)(l_main___lam__1___boxed), 19, 18);
lean_closure_set(v___f_3056_, 0, v___x_3051_);
lean_closure_set(v___f_3056_, 1, v___x_3047_);
lean_closure_set(v___f_3056_, 2, v___x_3052_);
lean_closure_set(v___f_3056_, 3, v_name_2970_);
lean_closure_set(v___f_3056_, 4, v_a_3045_);
lean_closure_set(v___f_3056_, 5, v___x_3053_);
lean_closure_set(v___f_3056_, 6, v___y_2998_);
lean_closure_set(v___f_3056_, 7, v_head_2950_);
lean_closure_set(v___f_3056_, 8, v___y_3000_);
lean_closure_set(v___f_3056_, 9, v___y_2993_);
lean_closure_set(v___f_3056_, 10, v___y_2994_);
lean_closure_set(v___f_3056_, 11, v___x_3048_);
lean_closure_set(v___f_3056_, 12, v___y_2997_);
lean_closure_set(v___f_3056_, 13, v___y_2999_);
lean_closure_set(v___f_3056_, 14, v___x_2990_);
lean_closure_set(v___f_3056_, 15, v___y_2995_);
lean_closure_set(v___f_3056_, 16, v___x_3054_);
lean_closure_set(v___f_3056_, 17, v___x_3055_);
v___x_3057_ = l_Lean_profileitIOUnsafe___redArg(v___x_3046_, v___x_2991_, v___f_3056_, v___y_3002_);
lean_dec_ref(v___x_2991_);
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_object* v___x_3058_; uint8_t v___x_3059_; 
lean_dec_ref_known(v___x_3057_, 1);
v___x_3058_ = lean_display_cumulative_profiling_times();
v___x_3059_ = lean_unbox(v_fst_2981_);
lean_dec(v_fst_2981_);
if (v___x_3059_ == 0)
{
lean_dec_ref(v_env_3014_);
goto v___jp_2921_;
}
else
{
lean_object* v___x_3060_; 
v___x_3060_ = l_Lean_Environment_displayStats(v_env_3014_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_dec_ref_known(v___x_3060_, 1);
goto v___jp_2921_;
}
else
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
v_a_3061_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_3060_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3060_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
}
}
else
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
lean_dec_ref(v_env_3014_);
lean_dec(v_fst_2981_);
v_a_3069_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3071_ = v___x_3057_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_3057_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3074_; 
if (v_isShared_3072_ == 0)
{
v___x_3074_ = v___x_3071_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_a_3069_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
}
}
else
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
lean_dec_ref_known(v___x_3044_, 1);
lean_del_object(v___x_3016_);
lean_dec_ref(v_env_3014_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_3002_);
lean_dec(v___y_2993_);
lean_dec_ref(v___x_2991_);
lean_dec(v_fst_2981_);
lean_dec(v_name_2970_);
lean_dec(v_head_2950_);
v___x_3078_ = ((lean_object*)(l_main___closed__15));
v___x_3079_ = lean_string_append(v___x_3078_, v_head_2954_);
lean_dec(v_head_2954_);
v___x_3080_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__1));
v___x_3081_ = lean_string_append(v___x_3079_, v___x_3080_);
v___x_3082_ = l_IO_eprintln___at___00main_spec__6(v___x_3081_);
if (lean_obj_tag(v___x_3082_) == 0)
{
lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3090_; 
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3090_ == 0)
{
lean_object* v_unused_3091_; 
v_unused_3091_ = lean_ctor_get(v___x_3082_, 0);
lean_dec(v_unused_3091_);
v___x_3084_ = v___x_3082_;
v_isShared_3085_ = v_isSharedCheck_3090_;
goto v_resetjp_3083_;
}
else
{
lean_dec(v___x_3082_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3090_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___x_3086_; lean_object* v___x_3088_; 
v___x_3086_ = l_main___boxed__const__2;
if (v_isShared_3085_ == 0)
{
lean_ctor_set(v___x_3084_, 0, v___x_3086_);
v___x_3088_ = v___x_3084_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v___x_3086_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
else
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3099_; 
v_a_3092_ = lean_ctor_get(v___x_3082_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3094_ = v___x_3082_;
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_3082_);
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
}
else
{
lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3107_; 
lean_del_object(v___x_3016_);
lean_dec_ref(v_env_3014_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_3002_);
lean_dec(v___y_2993_);
lean_dec_ref(v___x_2991_);
lean_dec(v_fst_2981_);
lean_dec(v_name_2970_);
lean_dec(v_head_2954_);
lean_dec(v_head_2950_);
v_a_3100_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3102_ = v___x_3042_;
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v___x_3042_);
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
}
}
else
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3117_; 
lean_dec(v_a_3028_);
lean_dec_ref(v___x_3026_);
lean_del_object(v___x_3016_);
lean_dec_ref(v_env_3014_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_3002_);
lean_dec(v___y_2993_);
lean_dec_ref(v___x_2991_);
lean_del_object(v___x_2984_);
lean_dec(v_fst_2981_);
lean_dec(v_name_2970_);
lean_dec(v_head_2954_);
lean_del_object(v___x_2952_);
lean_dec(v_head_2950_);
v_a_3110_ = lean_ctor_get(v___x_3029_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3029_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3112_ = v___x_3029_;
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3029_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3115_; 
if (v_isShared_3113_ == 0)
{
v___x_3115_ = v___x_3112_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_a_3110_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
}
else
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3125_; 
lean_dec_ref(v___x_3026_);
lean_del_object(v___x_3016_);
lean_dec_ref(v_env_3014_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_3002_);
lean_dec(v___y_2993_);
lean_dec_ref(v___x_2991_);
lean_del_object(v___x_2984_);
lean_dec(v_fst_2981_);
lean_dec(v_name_2970_);
lean_dec(v_head_2954_);
lean_del_object(v___x_2952_);
lean_dec(v_head_2950_);
v_a_3118_ = lean_ctor_get(v___x_3027_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3120_ = v___x_3027_;
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_3027_);
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
else
{
lean_object* v___x_3126_; lean_object* v___x_3128_; 
lean_del_object(v___x_3016_);
lean_dec_ref(v_env_3014_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_3002_);
lean_dec(v___y_2993_);
lean_dec_ref(v___x_2991_);
lean_del_object(v___x_2984_);
lean_dec(v_fst_2981_);
lean_dec(v_name_2970_);
lean_dec(v_head_2954_);
lean_del_object(v___x_2952_);
lean_dec(v_head_2950_);
v___x_3126_ = l_main___boxed__const__2;
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 0, v___x_3126_);
v___x_3128_ = v___x_3022_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v___x_3126_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
}
else
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3139_; 
lean_del_object(v___x_3016_);
lean_dec_ref(v_env_3014_);
lean_dec_ref(v_messages_3013_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_3002_);
lean_dec(v___y_2993_);
lean_dec_ref(v___x_2991_);
lean_del_object(v___x_2984_);
lean_dec(v_fst_2981_);
lean_dec(v_name_2970_);
lean_dec(v_head_2954_);
lean_del_object(v___x_2952_);
lean_dec(v_head_2950_);
v_a_3132_ = lean_ctor_get(v___x_3020_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3134_ = v___x_3020_;
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3020_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3137_; 
if (v_isShared_3135_ == 0)
{
v___x_3137_ = v___x_3134_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_a_3132_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
}
}
v___jp_3149_:
{
lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; size_t v_sz_3184_; size_t v___x_3185_; lean_object* v___x_3186_; 
lean_inc_ref(v___y_3178_);
v___x_3181_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3181_, 0, v___y_3180_);
lean_ctor_set(v___x_3181_, 1, v_nextMacroScope_3168_);
lean_ctor_set(v___x_3181_, 2, v_ngen_3169_);
lean_ctor_set(v___x_3181_, 3, v_auxDeclNGen_3170_);
lean_ctor_set(v___x_3181_, 4, v_traceState_3171_);
lean_ctor_set(v___x_3181_, 5, v___y_3178_);
lean_ctor_set(v___x_3181_, 6, v_recordedDeps_3172_);
lean_ctor_set(v___x_3181_, 7, v_messages_3173_);
lean_ctor_set(v___x_3181_, 8, v_infoState_3174_);
lean_ctor_set(v___x_3181_, 9, v_snapshotTasks_3175_);
v___x_3182_ = lean_st_ref_put(v___y_3161_, v___x_3181_);
v___x_3183_ = lean_box(0);
v_sz_3184_ = lean_array_size(v___y_3179_);
v___x_3185_ = ((size_t)0ULL);
v___x_3186_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(v___y_3179_, v_sz_3184_, v___x_3185_, v___x_3183_, v___y_3177_, v___y_3161_);
lean_dec_ref(v___y_3179_);
if (lean_obj_tag(v___x_3186_) == 0)
{
lean_dec_ref_known(v___x_3186_, 1);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3161_);
v___y_2993_ = v___y_3150_;
v___y_2994_ = v___y_3151_;
v___y_2995_ = v___y_3153_;
v___y_2996_ = v___y_3152_;
v___y_2997_ = v___y_3154_;
v___y_2998_ = v___y_3155_;
v___y_2999_ = v___y_3156_;
v___y_3000_ = v___y_3157_;
v___y_3001_ = v___y_3158_;
v___y_3002_ = v___y_3164_;
v___y_3003_ = v___y_3165_;
v___y_3004_ = v___y_3159_;
v___y_3005_ = v___y_3166_;
v___y_3006_ = v___y_3167_;
v___y_3007_ = v___y_3176_;
v___y_3008_ = v___y_3178_;
v___y_3009_ = v___y_3160_;
v___y_3010_ = v___y_3162_;
v___y_3011_ = v___y_3163_;
goto v___jp_2992_;
}
else
{
if (lean_obj_tag(v___x_3186_) == 0)
{
lean_dec_ref_known(v___x_3186_, 1);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3161_);
v___y_2993_ = v___y_3150_;
v___y_2994_ = v___y_3151_;
v___y_2995_ = v___y_3153_;
v___y_2996_ = v___y_3152_;
v___y_2997_ = v___y_3154_;
v___y_2998_ = v___y_3155_;
v___y_2999_ = v___y_3156_;
v___y_3000_ = v___y_3157_;
v___y_3001_ = v___y_3158_;
v___y_3002_ = v___y_3164_;
v___y_3003_ = v___y_3165_;
v___y_3004_ = v___y_3159_;
v___y_3005_ = v___y_3166_;
v___y_3006_ = v___y_3167_;
v___y_3007_ = v___y_3176_;
v___y_3008_ = v___y_3178_;
v___y_3009_ = v___y_3160_;
v___y_3010_ = v___y_3162_;
v___y_3011_ = v___y_3163_;
goto v___jp_2992_;
}
else
{
lean_object* v_a_3187_; uint8_t v___x_3188_; 
v_a_3187_ = lean_ctor_get(v___x_3186_, 0);
lean_inc(v_a_3187_);
lean_dec_ref_known(v___x_3186_, 1);
v___x_3188_ = l_Lean_Exception_isInterrupt(v_a_3187_);
if (v___x_3188_ == 0)
{
lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3189_ = l_Lean_Exception_toMessageData(v_a_3187_);
v___x_3190_ = l_Lean_logError___at___00main_spec__13(v___x_3189_, v___y_3177_, v___y_3161_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3177_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_dec_ref_known(v___x_3190_, 1);
v___y_2993_ = v___y_3150_;
v___y_2994_ = v___y_3151_;
v___y_2995_ = v___y_3153_;
v___y_2996_ = v___y_3152_;
v___y_2997_ = v___y_3154_;
v___y_2998_ = v___y_3155_;
v___y_2999_ = v___y_3156_;
v___y_3000_ = v___y_3157_;
v___y_3001_ = v___y_3158_;
v___y_3002_ = v___y_3164_;
v___y_3003_ = v___y_3165_;
v___y_3004_ = v___y_3159_;
v___y_3005_ = v___y_3166_;
v___y_3006_ = v___y_3167_;
v___y_3007_ = v___y_3176_;
v___y_3008_ = v___y_3178_;
v___y_3009_ = v___y_3160_;
v___y_3010_ = v___y_3162_;
v___y_3011_ = v___y_3163_;
goto v___jp_2992_;
}
else
{
lean_object* v___x_3191_; lean_object* v___x_3192_; 
lean_dec_ref_known(v___x_3190_, 1);
lean_dec(v___y_3166_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3159_);
lean_dec(v___y_3150_);
lean_dec_ref(v___x_2991_);
lean_del_object(v___x_2984_);
lean_dec(v_fst_2981_);
lean_dec(v_name_2970_);
lean_dec(v_head_2954_);
lean_del_object(v___x_2952_);
lean_dec(v_head_2950_);
v___x_3191_ = lean_obj_once(&l_main___closed__19, &l_main___closed__19_once, _init_l_main___closed__19);
v___x_3192_ = l_panic___at___00main_spec__5(v___x_3191_);
return v___x_3192_;
}
}
else
{
lean_dec(v_a_3187_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3161_);
v___y_2993_ = v___y_3150_;
v___y_2994_ = v___y_3151_;
v___y_2995_ = v___y_3153_;
v___y_2996_ = v___y_3152_;
v___y_2997_ = v___y_3154_;
v___y_2998_ = v___y_3155_;
v___y_2999_ = v___y_3156_;
v___y_3000_ = v___y_3157_;
v___y_3001_ = v___y_3158_;
v___y_3002_ = v___y_3164_;
v___y_3003_ = v___y_3165_;
v___y_3004_ = v___y_3159_;
v___y_3005_ = v___y_3166_;
v___y_3006_ = v___y_3167_;
v___y_3007_ = v___y_3176_;
v___y_3008_ = v___y_3178_;
v___y_3009_ = v___y_3160_;
v___y_3010_ = v___y_3162_;
v___y_3011_ = v___y_3163_;
goto v___jp_2992_;
}
}
}
}
v___jp_3193_:
{
lean_object* v_toCold_3218_; lean_object* v_currRecDepth_3219_; lean_object* v_ref_3220_; uint8_t v_suppressElabErrors_3221_; uint8_t v_isRecordingDeps_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3273_; 
v_toCold_3218_ = lean_ctor_get(v___y_3216_, 0);
v_currRecDepth_3219_ = lean_ctor_get(v___y_3216_, 1);
v_ref_3220_ = lean_ctor_get(v___y_3216_, 2);
v_suppressElabErrors_3221_ = lean_ctor_get_uint8(v___y_3216_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3222_ = lean_ctor_get_uint8(v___y_3216_, sizeof(void*)*3 + 3);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___y_3216_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3224_ = v___y_3216_;
v_isShared_3225_ = v_isSharedCheck_3273_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_ref_3220_);
lean_inc(v_currRecDepth_3219_);
lean_inc(v_toCold_3218_);
lean_dec(v___y_3216_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3273_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v_fileName_3226_; lean_object* v_fileMap_3227_; lean_object* v_currNamespace_3228_; lean_object* v_openDecls_3229_; lean_object* v_initHeartbeats_3230_; lean_object* v_maxHeartbeats_3231_; lean_object* v_quotContext_3232_; lean_object* v_currMacroScope_3233_; lean_object* v_cancelTk_x3f_3234_; lean_object* v_inheritedTraceOptions_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3270_; 
v_fileName_3226_ = lean_ctor_get(v_toCold_3218_, 0);
v_fileMap_3227_ = lean_ctor_get(v_toCold_3218_, 1);
v_currNamespace_3228_ = lean_ctor_get(v_toCold_3218_, 4);
v_openDecls_3229_ = lean_ctor_get(v_toCold_3218_, 5);
v_initHeartbeats_3230_ = lean_ctor_get(v_toCold_3218_, 6);
v_maxHeartbeats_3231_ = lean_ctor_get(v_toCold_3218_, 7);
v_quotContext_3232_ = lean_ctor_get(v_toCold_3218_, 8);
v_currMacroScope_3233_ = lean_ctor_get(v_toCold_3218_, 9);
v_cancelTk_x3f_3234_ = lean_ctor_get(v_toCold_3218_, 10);
v_inheritedTraceOptions_3235_ = lean_ctor_get(v_toCold_3218_, 11);
v_isSharedCheck_3270_ = !lean_is_exclusive(v_toCold_3218_);
if (v_isSharedCheck_3270_ == 0)
{
lean_object* v_unused_3271_; lean_object* v_unused_3272_; 
v_unused_3271_ = lean_ctor_get(v_toCold_3218_, 3);
lean_dec(v_unused_3271_);
v_unused_3272_ = lean_ctor_get(v_toCold_3218_, 2);
lean_dec(v_unused_3272_);
v___x_3237_ = v_toCold_3218_;
v_isShared_3238_ = v_isSharedCheck_3270_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_inheritedTraceOptions_3235_);
lean_inc(v_cancelTk_x3f_3234_);
lean_inc(v_currMacroScope_3233_);
lean_inc(v_quotContext_3232_);
lean_inc(v_maxHeartbeats_3231_);
lean_inc(v_initHeartbeats_3230_);
lean_inc(v_openDecls_3229_);
lean_inc(v_currNamespace_3228_);
lean_inc(v_fileMap_3227_);
lean_inc(v_fileName_3226_);
lean_dec(v_toCold_3218_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3270_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3242_; 
v___x_3239_ = l_Lean_maxRecDepth;
v___x_3240_ = l_Lean_Option_get___at___00main_spec__8(v___x_2991_, v___x_3239_);
lean_inc_ref(v___x_2991_);
if (v_isShared_3238_ == 0)
{
lean_ctor_set(v___x_3237_, 3, v___x_3240_);
lean_ctor_set(v___x_3237_, 2, v___x_2991_);
v___x_3242_ = v___x_3237_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v_fileName_3226_);
lean_ctor_set(v_reuseFailAlloc_3269_, 1, v_fileMap_3227_);
lean_ctor_set(v_reuseFailAlloc_3269_, 2, v___x_2991_);
lean_ctor_set(v_reuseFailAlloc_3269_, 3, v___x_3240_);
lean_ctor_set(v_reuseFailAlloc_3269_, 4, v_currNamespace_3228_);
lean_ctor_set(v_reuseFailAlloc_3269_, 5, v_openDecls_3229_);
lean_ctor_set(v_reuseFailAlloc_3269_, 6, v_initHeartbeats_3230_);
lean_ctor_set(v_reuseFailAlloc_3269_, 7, v_maxHeartbeats_3231_);
lean_ctor_set(v_reuseFailAlloc_3269_, 8, v_quotContext_3232_);
lean_ctor_set(v_reuseFailAlloc_3269_, 9, v_currMacroScope_3233_);
lean_ctor_set(v_reuseFailAlloc_3269_, 10, v_cancelTk_x3f_3234_);
lean_ctor_set(v_reuseFailAlloc_3269_, 11, v_inheritedTraceOptions_3235_);
v___x_3242_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
lean_object* v___x_3244_; 
if (v_isShared_3225_ == 0)
{
lean_ctor_set(v___x_3224_, 0, v___x_3242_);
v___x_3244_ = v___x_3224_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v___x_3242_);
lean_ctor_set(v_reuseFailAlloc_3268_, 1, v_currRecDepth_3219_);
lean_ctor_set(v_reuseFailAlloc_3268_, 2, v_ref_3220_);
lean_ctor_set_uint8(v_reuseFailAlloc_3268_, sizeof(void*)*3 + 2, v_suppressElabErrors_3221_);
lean_ctor_set_uint8(v_reuseFailAlloc_3268_, sizeof(void*)*3 + 3, v_isRecordingDeps_3222_);
v___x_3244_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
lean_object* v___x_3245_; lean_object* v_env_3246_; lean_object* v_nextMacroScope_3247_; lean_object* v_ngen_3248_; lean_object* v_auxDeclNGen_3249_; lean_object* v_traceState_3250_; lean_object* v_recordedDeps_3251_; lean_object* v_messages_3252_; lean_object* v_infoState_3253_; lean_object* v_snapshotTasks_3254_; lean_object* v___x_3255_; uint8_t v___x_3256_; 
lean_ctor_set_uint16(v___x_3244_, sizeof(void*)*3, v___y_3211_);
v___x_3245_ = lean_st_ref_take(v___y_3217_);
v_env_3246_ = lean_ctor_get(v___x_3245_, 0);
lean_inc_ref(v_env_3246_);
v_nextMacroScope_3247_ = lean_ctor_get(v___x_3245_, 1);
lean_inc(v_nextMacroScope_3247_);
v_ngen_3248_ = lean_ctor_get(v___x_3245_, 2);
lean_inc_ref(v_ngen_3248_);
v_auxDeclNGen_3249_ = lean_ctor_get(v___x_3245_, 3);
lean_inc_ref(v_auxDeclNGen_3249_);
v_traceState_3250_ = lean_ctor_get(v___x_3245_, 4);
lean_inc_ref(v_traceState_3250_);
v_recordedDeps_3251_ = lean_ctor_get(v___x_3245_, 6);
lean_inc_ref(v_recordedDeps_3251_);
v_messages_3252_ = lean_ctor_get(v___x_3245_, 7);
lean_inc_ref(v_messages_3252_);
v_infoState_3253_ = lean_ctor_get(v___x_3245_, 8);
lean_inc_ref(v_infoState_3253_);
v_snapshotTasks_3254_ = lean_ctor_get(v___x_3245_, 9);
lean_inc_ref(v_snapshotTasks_3254_);
lean_dec(v___x_3245_);
v___x_3255_ = lean_array_get_size(v___y_3215_);
v___x_3256_ = lean_nat_dec_lt(v___x_2990_, v___x_3255_);
if (v___x_3256_ == 0)
{
lean_object* v___x_3257_; 
lean_inc_ref(v___y_3213_);
v___x_3257_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3213_, v_env_3246_, v___x_2966_);
v___y_3150_ = v___y_3194_;
v___y_3151_ = v___y_3195_;
v___y_3152_ = v___y_3197_;
v___y_3153_ = v___y_3196_;
v___y_3154_ = v___y_3198_;
v___y_3155_ = v___y_3199_;
v___y_3156_ = v___y_3200_;
v___y_3157_ = v___y_3201_;
v___y_3158_ = v___y_3202_;
v___y_3159_ = v___y_3203_;
v___y_3160_ = v___y_3204_;
v___y_3161_ = v___y_3217_;
v___y_3162_ = v___y_3205_;
v___y_3163_ = v___y_3206_;
v___y_3164_ = v___y_3207_;
v___y_3165_ = v___y_3208_;
v___y_3166_ = v___y_3209_;
v___y_3167_ = v___y_3210_;
v_nextMacroScope_3168_ = v_nextMacroScope_3247_;
v_ngen_3169_ = v_ngen_3248_;
v_auxDeclNGen_3170_ = v_auxDeclNGen_3249_;
v_traceState_3171_ = v_traceState_3250_;
v_recordedDeps_3172_ = v_recordedDeps_3251_;
v_messages_3173_ = v_messages_3252_;
v_infoState_3174_ = v_infoState_3253_;
v_snapshotTasks_3175_ = v_snapshotTasks_3254_;
v___y_3176_ = v___y_3212_;
v___y_3177_ = v___x_3244_;
v___y_3178_ = v___y_3214_;
v___y_3179_ = v___y_3215_;
v___y_3180_ = v___x_3257_;
goto v___jp_3149_;
}
else
{
uint8_t v___x_3258_; 
v___x_3258_ = lean_nat_dec_le(v___x_3255_, v___x_3255_);
if (v___x_3258_ == 0)
{
if (v___x_3256_ == 0)
{
lean_object* v___x_3259_; 
lean_inc_ref(v___y_3213_);
v___x_3259_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3213_, v_env_3246_, v___x_2966_);
v___y_3150_ = v___y_3194_;
v___y_3151_ = v___y_3195_;
v___y_3152_ = v___y_3197_;
v___y_3153_ = v___y_3196_;
v___y_3154_ = v___y_3198_;
v___y_3155_ = v___y_3199_;
v___y_3156_ = v___y_3200_;
v___y_3157_ = v___y_3201_;
v___y_3158_ = v___y_3202_;
v___y_3159_ = v___y_3203_;
v___y_3160_ = v___y_3204_;
v___y_3161_ = v___y_3217_;
v___y_3162_ = v___y_3205_;
v___y_3163_ = v___y_3206_;
v___y_3164_ = v___y_3207_;
v___y_3165_ = v___y_3208_;
v___y_3166_ = v___y_3209_;
v___y_3167_ = v___y_3210_;
v_nextMacroScope_3168_ = v_nextMacroScope_3247_;
v_ngen_3169_ = v_ngen_3248_;
v_auxDeclNGen_3170_ = v_auxDeclNGen_3249_;
v_traceState_3171_ = v_traceState_3250_;
v_recordedDeps_3172_ = v_recordedDeps_3251_;
v_messages_3173_ = v_messages_3252_;
v_infoState_3174_ = v_infoState_3253_;
v_snapshotTasks_3175_ = v_snapshotTasks_3254_;
v___y_3176_ = v___y_3212_;
v___y_3177_ = v___x_3244_;
v___y_3178_ = v___y_3214_;
v___y_3179_ = v___y_3215_;
v___y_3180_ = v___x_3259_;
goto v___jp_3149_;
}
else
{
size_t v___x_3260_; size_t v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3260_ = ((size_t)0ULL);
v___x_3261_ = lean_usize_of_nat(v___x_3255_);
v___x_3262_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(v___y_3215_, v___x_3260_, v___x_3261_, v___x_2966_);
lean_inc_ref(v___y_3213_);
v___x_3263_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3213_, v_env_3246_, v___x_3262_);
v___y_3150_ = v___y_3194_;
v___y_3151_ = v___y_3195_;
v___y_3152_ = v___y_3197_;
v___y_3153_ = v___y_3196_;
v___y_3154_ = v___y_3198_;
v___y_3155_ = v___y_3199_;
v___y_3156_ = v___y_3200_;
v___y_3157_ = v___y_3201_;
v___y_3158_ = v___y_3202_;
v___y_3159_ = v___y_3203_;
v___y_3160_ = v___y_3204_;
v___y_3161_ = v___y_3217_;
v___y_3162_ = v___y_3205_;
v___y_3163_ = v___y_3206_;
v___y_3164_ = v___y_3207_;
v___y_3165_ = v___y_3208_;
v___y_3166_ = v___y_3209_;
v___y_3167_ = v___y_3210_;
v_nextMacroScope_3168_ = v_nextMacroScope_3247_;
v_ngen_3169_ = v_ngen_3248_;
v_auxDeclNGen_3170_ = v_auxDeclNGen_3249_;
v_traceState_3171_ = v_traceState_3250_;
v_recordedDeps_3172_ = v_recordedDeps_3251_;
v_messages_3173_ = v_messages_3252_;
v_infoState_3174_ = v_infoState_3253_;
v_snapshotTasks_3175_ = v_snapshotTasks_3254_;
v___y_3176_ = v___y_3212_;
v___y_3177_ = v___x_3244_;
v___y_3178_ = v___y_3214_;
v___y_3179_ = v___y_3215_;
v___y_3180_ = v___x_3263_;
goto v___jp_3149_;
}
}
else
{
size_t v___x_3264_; size_t v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; 
v___x_3264_ = ((size_t)0ULL);
v___x_3265_ = lean_usize_of_nat(v___x_3255_);
v___x_3266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(v___y_3215_, v___x_3264_, v___x_3265_, v___x_2966_);
lean_inc_ref(v___y_3213_);
v___x_3267_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3213_, v_env_3246_, v___x_3266_);
v___y_3150_ = v___y_3194_;
v___y_3151_ = v___y_3195_;
v___y_3152_ = v___y_3197_;
v___y_3153_ = v___y_3196_;
v___y_3154_ = v___y_3198_;
v___y_3155_ = v___y_3199_;
v___y_3156_ = v___y_3200_;
v___y_3157_ = v___y_3201_;
v___y_3158_ = v___y_3202_;
v___y_3159_ = v___y_3203_;
v___y_3160_ = v___y_3204_;
v___y_3161_ = v___y_3217_;
v___y_3162_ = v___y_3205_;
v___y_3163_ = v___y_3206_;
v___y_3164_ = v___y_3207_;
v___y_3165_ = v___y_3208_;
v___y_3166_ = v___y_3209_;
v___y_3167_ = v___y_3210_;
v_nextMacroScope_3168_ = v_nextMacroScope_3247_;
v_ngen_3169_ = v_ngen_3248_;
v_auxDeclNGen_3170_ = v_auxDeclNGen_3249_;
v_traceState_3171_ = v_traceState_3250_;
v_recordedDeps_3172_ = v_recordedDeps_3251_;
v_messages_3173_ = v_messages_3252_;
v_infoState_3174_ = v_infoState_3253_;
v_snapshotTasks_3175_ = v_snapshotTasks_3254_;
v___y_3176_ = v___y_3212_;
v___y_3177_ = v___x_3244_;
v___y_3178_ = v___y_3214_;
v___y_3179_ = v___y_3215_;
v___y_3180_ = v___x_3267_;
goto v___jp_3149_;
}
}
}
}
}
}
}
v___jp_3274_:
{
lean_object* v___x_3299_; lean_object* v_env_3300_; lean_object* v_nextMacroScope_3301_; lean_object* v_ngen_3302_; lean_object* v_auxDeclNGen_3303_; lean_object* v_traceState_3304_; lean_object* v_recordedDeps_3305_; lean_object* v_messages_3306_; lean_object* v_infoState_3307_; lean_object* v_snapshotTasks_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3317_; 
v___x_3299_ = lean_st_ref_take(v___y_3292_);
v_env_3300_ = lean_ctor_get(v___x_3299_, 0);
v_nextMacroScope_3301_ = lean_ctor_get(v___x_3299_, 1);
v_ngen_3302_ = lean_ctor_get(v___x_3299_, 2);
v_auxDeclNGen_3303_ = lean_ctor_get(v___x_3299_, 3);
v_traceState_3304_ = lean_ctor_get(v___x_3299_, 4);
v_recordedDeps_3305_ = lean_ctor_get(v___x_3299_, 6);
v_messages_3306_ = lean_ctor_get(v___x_3299_, 7);
v_infoState_3307_ = lean_ctor_get(v___x_3299_, 8);
v_snapshotTasks_3308_ = lean_ctor_get(v___x_3299_, 9);
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3317_ == 0)
{
lean_object* v_unused_3318_; 
v_unused_3318_ = lean_ctor_get(v___x_3299_, 5);
lean_dec(v_unused_3318_);
v___x_3310_ = v___x_3299_;
v_isShared_3311_ = v_isSharedCheck_3317_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_snapshotTasks_3308_);
lean_inc(v_infoState_3307_);
lean_inc(v_messages_3306_);
lean_inc(v_recordedDeps_3305_);
lean_inc(v_traceState_3304_);
lean_inc(v_auxDeclNGen_3303_);
lean_inc(v_ngen_3302_);
lean_inc(v_nextMacroScope_3301_);
lean_inc(v_env_3300_);
lean_dec(v___x_3299_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3317_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v___x_3312_; lean_object* v___x_3314_; 
v___x_3312_ = l_Lean_Kernel_enableDiag(v_env_3300_, v___y_3284_);
lean_inc_ref(v___y_3298_);
if (v_isShared_3311_ == 0)
{
lean_ctor_set(v___x_3310_, 5, v___y_3298_);
lean_ctor_set(v___x_3310_, 0, v___x_3312_);
v___x_3314_ = v___x_3310_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v___x_3312_);
lean_ctor_set(v_reuseFailAlloc_3316_, 1, v_nextMacroScope_3301_);
lean_ctor_set(v_reuseFailAlloc_3316_, 2, v_ngen_3302_);
lean_ctor_set(v_reuseFailAlloc_3316_, 3, v_auxDeclNGen_3303_);
lean_ctor_set(v_reuseFailAlloc_3316_, 4, v_traceState_3304_);
lean_ctor_set(v_reuseFailAlloc_3316_, 5, v___y_3298_);
lean_ctor_set(v_reuseFailAlloc_3316_, 6, v_recordedDeps_3305_);
lean_ctor_set(v_reuseFailAlloc_3316_, 7, v_messages_3306_);
lean_ctor_set(v_reuseFailAlloc_3316_, 8, v_infoState_3307_);
lean_ctor_set(v_reuseFailAlloc_3316_, 9, v_snapshotTasks_3308_);
v___x_3314_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
lean_object* v___x_3315_; 
v___x_3315_ = lean_st_ref_put(v___y_3292_, v___x_3314_);
lean_inc(v___y_3292_);
v___y_3194_ = v___y_3275_;
v___y_3195_ = v___y_3276_;
v___y_3196_ = v___y_3278_;
v___y_3197_ = v___y_3277_;
v___y_3198_ = v___y_3279_;
v___y_3199_ = v___y_3280_;
v___y_3200_ = v___y_3281_;
v___y_3201_ = v___y_3282_;
v___y_3202_ = v___y_3283_;
v___y_3203_ = v___y_3285_;
v___y_3204_ = v___y_3287_;
v___y_3205_ = v___y_3288_;
v___y_3206_ = v___y_3289_;
v___y_3207_ = v___y_3290_;
v___y_3208_ = v___y_3291_;
v___y_3209_ = v___y_3292_;
v___y_3210_ = v___y_3293_;
v___y_3211_ = v___y_3294_;
v___y_3212_ = v___y_3295_;
v___y_3213_ = v___y_3297_;
v___y_3214_ = v___y_3298_;
v___y_3215_ = v___y_3296_;
v___y_3216_ = v___y_3286_;
v___y_3217_ = v___y_3292_;
goto v___jp_3193_;
}
}
}
v___jp_3319_:
{
if (v___y_3344_ == 0)
{
v___y_3275_ = v___y_3320_;
v___y_3276_ = v___y_3321_;
v___y_3277_ = v___y_3323_;
v___y_3278_ = v___y_3322_;
v___y_3279_ = v___y_3324_;
v___y_3280_ = v___y_3325_;
v___y_3281_ = v___y_3326_;
v___y_3282_ = v___y_3327_;
v___y_3283_ = v___y_3328_;
v___y_3284_ = v___y_3329_;
v___y_3285_ = v___y_3330_;
v___y_3286_ = v___y_3331_;
v___y_3287_ = v___y_3332_;
v___y_3288_ = v___y_3333_;
v___y_3289_ = v___y_3334_;
v___y_3290_ = v___y_3335_;
v___y_3291_ = v___y_3336_;
v___y_3292_ = v___y_3337_;
v___y_3293_ = v___y_3338_;
v___y_3294_ = v___y_3339_;
v___y_3295_ = v___y_3340_;
v___y_3296_ = v___y_3343_;
v___y_3297_ = v___y_3342_;
v___y_3298_ = v___y_3341_;
goto v___jp_3274_;
}
else
{
lean_inc(v___y_3337_);
v___y_3194_ = v___y_3320_;
v___y_3195_ = v___y_3321_;
v___y_3196_ = v___y_3322_;
v___y_3197_ = v___y_3323_;
v___y_3198_ = v___y_3324_;
v___y_3199_ = v___y_3325_;
v___y_3200_ = v___y_3326_;
v___y_3201_ = v___y_3327_;
v___y_3202_ = v___y_3328_;
v___y_3203_ = v___y_3330_;
v___y_3204_ = v___y_3332_;
v___y_3205_ = v___y_3333_;
v___y_3206_ = v___y_3334_;
v___y_3207_ = v___y_3335_;
v___y_3208_ = v___y_3336_;
v___y_3209_ = v___y_3337_;
v___y_3210_ = v___y_3338_;
v___y_3211_ = v___y_3339_;
v___y_3212_ = v___y_3340_;
v___y_3213_ = v___y_3342_;
v___y_3214_ = v___y_3341_;
v___y_3215_ = v___y_3343_;
v___y_3216_ = v___y_3331_;
v___y_3217_ = v___y_3337_;
goto v___jp_3193_;
}
}
v___jp_3345_:
{
if (v___y_3362_ == 0)
{
v___y_3320_ = v___y_3352_;
v___y_3321_ = v___y_3353_;
v___y_3322_ = v___y_3346_;
v___y_3323_ = v___y_3354_;
v___y_3324_ = v___y_3348_;
v___y_3325_ = v___y_3358_;
v___y_3326_ = v___y_3350_;
v___y_3327_ = v___y_3351_;
v___y_3328_ = v___y_3361_;
v___y_3329_ = v___y_3370_;
v___y_3330_ = v___y_3347_;
v___y_3331_ = v___y_3363_;
v___y_3332_ = v___y_3349_;
v___y_3333_ = v___y_3364_;
v___y_3334_ = v___y_3365_;
v___y_3335_ = v___y_3366_;
v___y_3336_ = v___y_3367_;
v___y_3337_ = v___y_3369_;
v___y_3338_ = v___y_3355_;
v___y_3339_ = v___y_3356_;
v___y_3340_ = v___y_3357_;
v___y_3341_ = v___y_3358_;
v___y_3342_ = v___y_3359_;
v___y_3343_ = v___y_3360_;
v___y_3344_ = v___y_3368_;
goto v___jp_3319_;
}
else
{
v___y_3275_ = v___y_3352_;
v___y_3276_ = v___y_3353_;
v___y_3277_ = v___y_3354_;
v___y_3278_ = v___y_3346_;
v___y_3279_ = v___y_3348_;
v___y_3280_ = v___y_3358_;
v___y_3281_ = v___y_3350_;
v___y_3282_ = v___y_3351_;
v___y_3283_ = v___y_3361_;
v___y_3284_ = v___y_3370_;
v___y_3285_ = v___y_3347_;
v___y_3286_ = v___y_3363_;
v___y_3287_ = v___y_3349_;
v___y_3288_ = v___y_3364_;
v___y_3289_ = v___y_3365_;
v___y_3290_ = v___y_3366_;
v___y_3291_ = v___y_3367_;
v___y_3292_ = v___y_3369_;
v___y_3293_ = v___y_3355_;
v___y_3294_ = v___y_3356_;
v___y_3295_ = v___y_3357_;
v___y_3296_ = v___y_3360_;
v___y_3297_ = v___y_3359_;
v___y_3298_ = v___y_3358_;
goto v___jp_3274_;
}
}
}
}
else
{
lean_object* v_a_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3652_; 
lean_dec(v_importArts_2972_);
lean_dec(v_package_x3f_2971_);
lean_dec(v_name_2970_);
lean_dec(v_head_2954_);
lean_del_object(v___x_2952_);
lean_dec(v_head_2950_);
lean_del_object(v___x_2948_);
v_a_3645_ = lean_ctor_get(v___x_2979_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3647_ = v___x_2979_;
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_a_3645_);
lean_dec(v___x_2979_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___x_3650_; 
if (v_isShared_3648_ == 0)
{
v___x_3650_ = v___x_3647_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_a_3645_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
}
}
}
}
}
else
{
lean_object* v_a_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3661_; 
lean_del_object(v___x_2957_);
lean_dec(v_tail_2955_);
lean_dec(v_head_2954_);
lean_del_object(v___x_2952_);
lean_dec(v_head_2950_);
lean_del_object(v___x_2948_);
v_a_3654_ = lean_ctor_get(v___x_2968_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3656_ = v___x_2968_;
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_a_3654_);
lean_dec(v___x_2968_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v___x_3659_; 
if (v_isShared_3657_ == 0)
{
v___x_3659_ = v___x_3656_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_a_3654_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
return v___x_3659_;
}
}
}
}
}
}
}
else
{
lean_dec(v_tail_2945_);
lean_dec_ref_known(v_tail_2944_, 2);
lean_dec_ref_known(v_args_2919_, 2);
goto v___jp_2924_;
}
}
else
{
lean_dec(v_tail_2944_);
lean_dec_ref_known(v_args_2919_, 2);
goto v___jp_2924_;
}
}
else
{
lean_dec(v_args_2919_);
goto v___jp_2924_;
}
v___jp_2921_:
{
lean_object* v___x_2922_; lean_object* v___x_2923_; 
v___x_2922_ = l_main___boxed__const__1;
v___x_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2922_);
return v___x_2923_;
}
v___jp_2924_:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2925_ = ((lean_object*)(l_main___closed__0));
v___x_2926_ = l_IO_println___at___00Lean_Environment_displayStats_spec__1(v___x_2925_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2934_; 
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_2934_ == 0)
{
lean_object* v_unused_2935_; 
v_unused_2935_ = lean_ctor_get(v___x_2926_, 0);
lean_dec(v_unused_2935_);
v___x_2928_ = v___x_2926_;
v_isShared_2929_ = v_isSharedCheck_2934_;
goto v_resetjp_2927_;
}
else
{
lean_dec(v___x_2926_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2934_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2930_; lean_object* v___x_2932_; 
v___x_2930_ = l_main___boxed__const__2;
if (v_isShared_2929_ == 0)
{
lean_ctor_set(v___x_2928_, 0, v___x_2930_);
v___x_2932_ = v___x_2928_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v___x_2930_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
else
{
lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2943_; 
v_a_2936_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2938_ = v___x_2926_;
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v___x_2926_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2941_; 
if (v_isShared_2939_ == 0)
{
v___x_2941_ = v___x_2938_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_a_2936_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_3667_, lean_object* v_a_3668_){
_start:
{
lean_object* v_res_3669_; 
v_res_3669_ = _lean_main(v_args_3667_);
return v_res_3669_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1(lean_object* v_as_3670_, lean_object* v_as_x27_3671_, lean_object* v_b_3672_, lean_object* v_a_3673_){
_start:
{
lean_object* v___x_3675_; 
v___x_3675_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_3671_, v_b_3672_);
return v___x_3675_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___boxed(lean_object* v_as_3676_, lean_object* v_as_x27_3677_, lean_object* v_b_3678_, lean_object* v_a_3679_, lean_object* v___y_3680_){
_start:
{
lean_object* v_res_3681_; 
v_res_3681_ = l_List_forIn_x27_loop___at___00main_spec__1(v_as_3676_, v_as_x27_3677_, v_b_3678_, v_a_3679_);
lean_dec(v_as_x27_3677_);
lean_dec(v_as_3676_);
return v_res_3681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16(lean_object* v___y_3682_, lean_object* v___y_3683_){
_start:
{
lean_object* v___x_3685_; 
v___x_3685_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v___y_3683_);
return v___x_3685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___boxed(lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_){
_start:
{
lean_object* v_res_3689_; 
v_res_3689_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16(v___y_3686_, v___y_3687_);
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
return v_res_3689_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17(lean_object* v_00_u03b2_3690_, lean_object* v_m_3691_, lean_object* v_a_3692_, lean_object* v_fallback_3693_){
_start:
{
lean_object* v___x_3694_; 
v___x_3694_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_m_3691_, v_a_3692_, v_fallback_3693_);
return v___x_3694_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___boxed(lean_object* v_00_u03b2_3695_, lean_object* v_m_3696_, lean_object* v_a_3697_, lean_object* v_fallback_3698_){
_start:
{
lean_object* v_res_3699_; 
v_res_3699_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17(v_00_u03b2_3695_, v_m_3696_, v_a_3697_, v_fallback_3698_);
lean_dec(v_fallback_3698_);
lean_dec_ref(v_a_3697_);
lean_dec_ref(v_m_3696_);
return v_res_3699_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18(lean_object* v_00_u03b2_3700_, lean_object* v_m_3701_, lean_object* v_a_3702_, lean_object* v_b_3703_){
_start:
{
lean_object* v___x_3704_; 
v___x_3704_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(v_m_3701_, v_a_3702_, v_b_3703_);
return v___x_3704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21(lean_object* v_n_3705_, lean_object* v_as_3706_, lean_object* v_lo_3707_, lean_object* v_hi_3708_, lean_object* v_w_3709_, lean_object* v_hlo_3710_, lean_object* v_hhi_3711_){
_start:
{
lean_object* v___x_3712_; 
v___x_3712_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(v_n_3705_, v_as_3706_, v_lo_3707_, v_hi_3708_);
return v___x_3712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___boxed(lean_object* v_n_3713_, lean_object* v_as_3714_, lean_object* v_lo_3715_, lean_object* v_hi_3716_, lean_object* v_w_3717_, lean_object* v_hlo_3718_, lean_object* v_hhi_3719_){
_start:
{
lean_object* v_res_3720_; 
v_res_3720_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21(v_n_3713_, v_as_3714_, v_lo_3715_, v_hi_3716_, v_w_3717_, v_hlo_3718_, v_hhi_3719_);
lean_dec(v_hi_3716_);
lean_dec(v_n_3713_);
return v_res_3720_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21(lean_object* v_00_u03b2_3721_, lean_object* v_a_3722_, lean_object* v_fallback_3723_, lean_object* v_x_3724_){
_start:
{
lean_object* v___x_3725_; 
v___x_3725_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg(v_a_3722_, v_fallback_3723_, v_x_3724_);
return v___x_3725_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___boxed(lean_object* v_00_u03b2_3726_, lean_object* v_a_3727_, lean_object* v_fallback_3728_, lean_object* v_x_3729_){
_start:
{
lean_object* v_res_3730_; 
v_res_3730_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21(v_00_u03b2_3726_, v_a_3727_, v_fallback_3728_, v_x_3729_);
lean_dec(v_x_3729_);
lean_dec(v_fallback_3728_);
lean_dec_ref(v_a_3727_);
return v_res_3730_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23(lean_object* v_00_u03b2_3731_, lean_object* v_a_3732_, lean_object* v_x_3733_){
_start:
{
uint8_t v___x_3734_; 
v___x_3734_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg(v_a_3732_, v_x_3733_);
return v___x_3734_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___boxed(lean_object* v_00_u03b2_3735_, lean_object* v_a_3736_, lean_object* v_x_3737_){
_start:
{
uint8_t v_res_3738_; lean_object* v_r_3739_; 
v_res_3738_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23(v_00_u03b2_3735_, v_a_3736_, v_x_3737_);
lean_dec(v_x_3737_);
lean_dec_ref(v_a_3736_);
v_r_3739_ = lean_box(v_res_3738_);
return v_r_3739_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24(lean_object* v_00_u03b2_3740_, lean_object* v_data_3741_){
_start:
{
lean_object* v___x_3742_; 
v___x_3742_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24___redArg(v_data_3741_);
return v___x_3742_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25(lean_object* v_00_u03b2_3743_, lean_object* v_a_3744_, lean_object* v_b_3745_, lean_object* v_x_3746_){
_start:
{
lean_object* v___x_3747_; 
v___x_3747_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25___redArg(v_a_3744_, v_b_3745_, v_x_3746_);
return v___x_3747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31(lean_object* v_n_3748_, lean_object* v_lo_3749_, lean_object* v_hi_3750_, lean_object* v_hhi_3751_, lean_object* v_pivot_3752_, lean_object* v_as_3753_, lean_object* v_i_3754_, lean_object* v_k_3755_, lean_object* v_ilo_3756_, lean_object* v_ik_3757_, lean_object* v_w_3758_){
_start:
{
lean_object* v___x_3759_; 
v___x_3759_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg(v_hi_3750_, v_pivot_3752_, v_as_3753_, v_i_3754_, v_k_3755_);
return v___x_3759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___boxed(lean_object* v_n_3760_, lean_object* v_lo_3761_, lean_object* v_hi_3762_, lean_object* v_hhi_3763_, lean_object* v_pivot_3764_, lean_object* v_as_3765_, lean_object* v_i_3766_, lean_object* v_k_3767_, lean_object* v_ilo_3768_, lean_object* v_ik_3769_, lean_object* v_w_3770_){
_start:
{
lean_object* v_res_3771_; 
v_res_3771_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31(v_n_3760_, v_lo_3761_, v_hi_3762_, v_hhi_3763_, v_pivot_3764_, v_as_3765_, v_i_3766_, v_k_3767_, v_ilo_3768_, v_ik_3769_, v_w_3770_);
lean_dec_ref(v_pivot_3764_);
lean_dec(v_hi_3762_);
lean_dec(v_lo_3761_);
lean_dec(v_n_3760_);
return v_res_3771_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40(lean_object* v_as_3772_, size_t v_sz_3773_, size_t v_i_3774_, lean_object* v_b_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_){
_start:
{
lean_object* v___x_3779_; 
v___x_3779_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg(v_as_3772_, v_sz_3773_, v_i_3774_, v_b_3775_, v___y_3776_);
return v___x_3779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___boxed(lean_object* v_as_3780_, lean_object* v_sz_3781_, lean_object* v_i_3782_, lean_object* v_b_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_){
_start:
{
size_t v_sz_boxed_3787_; size_t v_i_boxed_3788_; lean_object* v_res_3789_; 
v_sz_boxed_3787_ = lean_unbox_usize(v_sz_3781_);
lean_dec(v_sz_3781_);
v_i_boxed_3788_ = lean_unbox_usize(v_i_3782_);
lean_dec(v_i_3782_);
v_res_3789_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40(v_as_3780_, v_sz_boxed_3787_, v_i_boxed_3788_, v_b_3783_, v___y_3784_, v___y_3785_);
lean_dec(v___y_3785_);
lean_dec_ref(v___y_3784_);
lean_dec_ref(v_as_3780_);
return v_res_3789_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35(lean_object* v_00_u03b2_3790_, lean_object* v_i_3791_, lean_object* v_source_3792_, lean_object* v_target_3793_){
_start:
{
lean_object* v___x_3794_; 
v___x_3794_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35___redArg(v_i_3791_, v_source_3792_, v_target_3793_);
return v___x_3794_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42(uint8_t v___x_3795_, lean_object* v_as_3796_, size_t v_sz_3797_, size_t v_i_3798_, lean_object* v_b_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_){
_start:
{
lean_object* v___x_3803_; 
v___x_3803_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg(v___x_3795_, v_as_3796_, v_sz_3797_, v_i_3798_, v_b_3799_, v___y_3800_);
return v___x_3803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___boxed(lean_object* v___x_3804_, lean_object* v_as_3805_, lean_object* v_sz_3806_, lean_object* v_i_3807_, lean_object* v_b_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_){
_start:
{
uint8_t v___x_41108__boxed_3812_; size_t v_sz_boxed_3813_; size_t v_i_boxed_3814_; lean_object* v_res_3815_; 
v___x_41108__boxed_3812_ = lean_unbox(v___x_3804_);
v_sz_boxed_3813_ = lean_unbox_usize(v_sz_3806_);
lean_dec(v_sz_3806_);
v_i_boxed_3814_ = lean_unbox_usize(v_i_3807_);
lean_dec(v_i_3807_);
v_res_3815_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42(v___x_41108__boxed_3812_, v_as_3805_, v_sz_boxed_3813_, v_i_boxed_3814_, v_b_3808_, v___y_3809_, v___y_3810_);
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
lean_dec_ref(v_as_3805_);
return v_res_3815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51(lean_object* v_as_3816_, size_t v_sz_3817_, size_t v_i_3818_, lean_object* v_b_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_){
_start:
{
lean_object* v___x_3823_; 
v___x_3823_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg(v_as_3816_, v_sz_3817_, v_i_3818_, v_b_3819_, v___y_3820_);
return v___x_3823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___boxed(lean_object* v_as_3824_, lean_object* v_sz_3825_, lean_object* v_i_3826_, lean_object* v_b_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_){
_start:
{
size_t v_sz_boxed_3831_; size_t v_i_boxed_3832_; lean_object* v_res_3833_; 
v_sz_boxed_3831_ = lean_unbox_usize(v_sz_3825_);
lean_dec(v_sz_3825_);
v_i_boxed_3832_ = lean_unbox_usize(v_i_3826_);
lean_dec(v_i_3826_);
v_res_3833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51(v_as_3824_, v_sz_boxed_3831_, v_i_boxed_3832_, v_b_3827_, v___y_3828_, v___y_3829_);
lean_dec(v___y_3829_);
lean_dec_ref(v___y_3828_);
lean_dec_ref(v_as_3824_);
return v_res_3833_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35_spec__44(lean_object* v_00_u03b2_3834_, lean_object* v_x_3835_, lean_object* v_x_3836_){
_start:
{
lean_object* v___x_3837_; 
v___x_3837_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35_spec__44___redArg(v_x_3835_, v_x_3836_);
return v___x_3837_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49(uint8_t v___x_3838_, lean_object* v_as_3839_, size_t v_sz_3840_, size_t v_i_3841_, lean_object* v_b_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_){
_start:
{
lean_object* v___x_3846_; 
v___x_3846_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg(v___x_3838_, v_as_3839_, v_sz_3840_, v_i_3841_, v_b_3842_, v___y_3843_);
return v___x_3846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___boxed(lean_object* v___x_3847_, lean_object* v_as_3848_, lean_object* v_sz_3849_, lean_object* v_i_3850_, lean_object* v_b_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_){
_start:
{
uint8_t v___x_41139__boxed_3855_; size_t v_sz_boxed_3856_; size_t v_i_boxed_3857_; lean_object* v_res_3858_; 
v___x_41139__boxed_3855_ = lean_unbox(v___x_3847_);
v_sz_boxed_3856_ = lean_unbox_usize(v_sz_3849_);
lean_dec(v_sz_3849_);
v_i_boxed_3857_ = lean_unbox_usize(v_i_3850_);
lean_dec(v_i_3850_);
v_res_3858_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49(v___x_41139__boxed_3855_, v_as_3848_, v_sz_boxed_3856_, v_i_boxed_3857_, v_b_3851_, v___y_3852_, v___y_3853_);
lean_dec(v___y_3853_);
lean_dec_ref(v___y_3852_);
lean_dec_ref(v_as_3848_);
return v_res_3858_;
}
}
lean_object* runtime_initialize_Init(uint8_t builtin);
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_ForEachExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_Path(uint8_t builtin);
lean_object* runtime_initialize_Lean_Environment(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_Options(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_ModPkgExt(uint8_t builtin);
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
res = runtime_initialize_Lean_Compiler_ModPkgExt(builtin);
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
lean_object* initialize_Lean_Compiler_ModPkgExt(uint8_t builtin);
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
res = initialize_Lean_Compiler_ModPkgExt(builtin);
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
