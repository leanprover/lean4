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
uint8_t l_Lean_instOrdOLeanLevel_ord(uint8_t, uint8_t);
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
lean_object* lean_string_utf8_byte_size(lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_ir_export_entries(lean_object*);
lean_object* l_Lean_mkModuleData(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_get_ir_extra_const_names(lean_object*, uint8_t, uint8_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
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
extern lean_object* l_instInhabitedError;
lean_object* l_instInhabitedEIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_setState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_init_search_path();
lean_object* l_Lean_EnvExtension_setState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_postponedCompileDeclsExt;
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedFileMap_default;
extern lean_object* l_Lean_Options_empty;
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
static const lean_string_object l_main___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "failed to create '"};
static const lean_object* l_main___closed__13 = (const lean_object*)&l_main___closed__13_value;
static const lean_string_object l_main___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "LeanIR"};
static const lean_object* l_main___closed__14 = (const lean_object*)&l_main___closed__14_value;
static const lean_string_object l_main___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "main"};
static const lean_object* l_main___closed__15 = (const lean_object*)&l_main___closed__15_value;
static const lean_string_object l_main___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_main___closed__16 = (const lean_object*)&l_main___closed__16_value;
static lean_once_cell_t l_main___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__17;
static const lean_string_object l_main___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "import"};
static const lean_object* l_main___closed__18 = (const lean_object*)&l_main___closed__18_value;
static lean_once_cell_t l_main___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__19;
static lean_once_cell_t l_main___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__20;
static const lean_string_object l_main___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l_main___closed__21 = (const lean_object*)&l_main___closed__21_value;
static const lean_ctor_object l_main___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__21_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l_main___closed__22 = (const lean_object*)&l_main___closed__22_value;
static const lean_ctor_object l_main___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_main___closed__22_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_main___closed__23 = (const lean_object*)&l_main___closed__23_value;
static lean_once_cell_t l_main___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__24;
static lean_once_cell_t l_main___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__25;
static lean_once_cell_t l_main___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__26;
static lean_once_cell_t l_main___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__27;
static const lean_array_object l_main___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_main___closed__28 = (const lean_object*)&l_main___closed__28_value;
static lean_once_cell_t l_main___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__29;
static lean_once_cell_t l_main___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__30;
static lean_once_cell_t l_main___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__31;
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
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(lean_object* v_s_149_){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_150_ = lean_string_utf8_byte_size(v_s_149_);
v___x_151_ = lean_unsigned_to_nat(2u);
v___x_152_ = lean_nat_dec_le(v___x_151_, v___x_150_);
if (v___x_152_ == 0)
{
lean_object* v___x_153_; 
lean_dec_ref(v_s_149_);
v___x_153_ = lean_box(0);
return v___x_153_;
}
else
{
lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_154_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__0));
v___x_155_ = lean_unsigned_to_nat(0u);
v___x_156_ = lean_string_memcmp(v_s_149_, v___x_154_, v___x_155_, v___x_155_, v___x_151_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; 
lean_dec_ref(v_s_149_);
v___x_157_ = lean_box(0);
return v___x_157_;
}
else
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
lean_inc_ref(v_s_149_);
v___x_158_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_158_, 0, v_s_149_);
lean_ctor_set(v___x_158_, 1, v___x_155_);
lean_ctor_set(v___x_158_, 2, v___x_150_);
v___x_159_ = l_String_Slice_pos_x21(v___x_158_, v___x_151_);
lean_dec_ref_known(v___x_158_, 3);
v___x_160_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_160_, 0, v_s_149_);
lean_ctor_set(v___x_160_, 1, v___x_159_);
lean_ctor_set(v___x_160_, 2, v___x_150_);
v___x_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
return v___x_161_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0(lean_object* v_s_162_, lean_object* v_pat_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(v_s_162_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___boxed(lean_object* v_s_165_, lean_object* v_pat_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0(v_s_165_, v_pat_166_);
lean_dec_ref(v_pat_166_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg(lean_object* v_val_168_, lean_object* v_a_169_, lean_object* v_b_170_){
_start:
{
lean_object* v_str_171_; lean_object* v_startInclusive_172_; lean_object* v_endExclusive_173_; lean_object* v___x_174_; uint8_t v_decide_175_; 
v_str_171_ = lean_ctor_get(v_val_168_, 0);
v_startInclusive_172_ = lean_ctor_get(v_val_168_, 1);
v_endExclusive_173_ = lean_ctor_get(v_val_168_, 2);
v___x_174_ = lean_nat_sub(v_endExclusive_173_, v_startInclusive_172_);
v_decide_175_ = lean_nat_dec_eq(v_a_169_, v___x_174_);
lean_dec(v___x_174_);
if (v_decide_175_ == 0)
{
lean_object* v___x_176_; uint32_t v___x_177_; uint32_t v___x_178_; uint8_t v___x_179_; 
v___x_176_ = lean_nat_add(v_startInclusive_172_, v_a_169_);
v___x_177_ = lean_string_utf8_get_fast(v_str_171_, v___x_176_);
v___x_178_ = 61;
v___x_179_ = lean_uint32_dec_eq(v___x_177_, v___x_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
lean_dec(v_a_169_);
v___x_180_ = lean_box(0);
v___x_181_ = lean_string_utf8_next_fast(v_str_171_, v___x_176_);
lean_dec(v___x_176_);
v___x_182_ = lean_nat_sub(v___x_181_, v_startInclusive_172_);
v_a_169_ = v___x_182_;
v_b_170_ = v___x_180_;
goto _start;
}
else
{
lean_object* v___x_184_; 
lean_dec(v___x_176_);
v___x_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_184_, 0, v_a_169_);
return v___x_184_;
}
}
else
{
lean_dec(v_a_169_);
lean_inc(v_b_170_);
return v_b_170_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg___boxed(lean_object* v_val_185_, lean_object* v_a_186_, lean_object* v_b_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg(v_val_185_, v_a_186_, v_b_187_);
lean_dec(v_b_187_);
lean_dec_ref(v_val_185_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__setConfigOption(lean_object* v_opts_196_, lean_object* v_arg_197_){
_start:
{
lean_object* v___x_199_; 
lean_inc_ref(v_arg_197_);
v___x_199_ = l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(v_arg_197_);
if (lean_obj_tag(v___x_199_) == 1)
{
lean_object* v_val_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_264_; 
lean_dec_ref(v_arg_197_);
v_val_200_ = lean_ctor_get(v___x_199_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_264_ == 0)
{
v___x_202_ = v___x_199_;
v_isShared_203_ = v_isSharedCheck_264_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_val_200_);
lean_dec(v___x_199_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_264_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___y_205_; lean_object* v_searcher_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v_searcher_257_ = lean_unsigned_to_nat(0u);
v___x_258_ = lean_box(0);
v___x_259_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg(v_val_200_, v_searcher_257_, v___x_258_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v_startInclusive_260_; lean_object* v_endExclusive_261_; lean_object* v___x_262_; 
v_startInclusive_260_ = lean_ctor_get(v_val_200_, 1);
v_endExclusive_261_ = lean_ctor_get(v_val_200_, 2);
v___x_262_ = lean_nat_sub(v_endExclusive_261_, v_startInclusive_260_);
v___y_205_ = v___x_262_;
goto v___jp_204_;
}
else
{
lean_object* v_val_263_; 
v_val_263_ = lean_ctor_get(v___x_259_, 0);
lean_inc(v_val_263_);
lean_dec_ref_known(v___x_259_, 1);
v___y_205_ = v_val_263_;
goto v___jp_204_;
}
v___jp_204_:
{
lean_object* v_str_206_; lean_object* v_startInclusive_207_; lean_object* v_endExclusive_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_256_; 
v_str_206_ = lean_ctor_get(v_val_200_, 0);
v_startInclusive_207_ = lean_ctor_get(v_val_200_, 1);
v_endExclusive_208_ = lean_ctor_get(v_val_200_, 2);
v_isSharedCheck_256_ = !lean_is_exclusive(v_val_200_);
if (v_isSharedCheck_256_ == 0)
{
v___x_210_ = v_val_200_;
v_isShared_211_ = v_isSharedCheck_256_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_endExclusive_208_);
lean_inc(v_startInclusive_207_);
lean_inc(v_str_206_);
lean_dec(v_val_200_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_256_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_212_; uint8_t v_decide_213_; 
v___x_212_ = lean_nat_sub(v_endExclusive_208_, v_startInclusive_207_);
v_decide_213_ = lean_nat_dec_eq(v___y_205_, v___x_212_);
lean_dec(v___x_212_);
if (v_decide_213_ == 0)
{
lean_object* v___x_214_; lean_object* v___x_216_; 
v___x_214_ = lean_nat_add(v_startInclusive_207_, v___y_205_);
lean_dec(v___y_205_);
lean_inc(v___x_214_);
lean_inc(v_startInclusive_207_);
lean_inc_ref(v_str_206_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 2, v___x_214_);
v___x_216_ = v___x_210_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_str_206_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v_startInclusive_207_);
lean_ctor_set(v_reuseFailAlloc_251_, 2, v___x_214_);
v___x_216_ = v_reuseFailAlloc_251_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
lean_object* v_name_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v_val_221_; lean_object* v___x_222_; 
v_name_217_ = l_String_Slice_toName(v___x_216_);
lean_dec_ref(v___x_216_);
v___x_218_ = lean_string_utf8_next_fast(v_str_206_, v___x_214_);
lean_dec(v___x_214_);
v___x_219_ = lean_nat_sub(v___x_218_, v_startInclusive_207_);
v___x_220_ = lean_nat_add(v_startInclusive_207_, v___x_219_);
lean_dec(v___x_219_);
lean_dec(v_startInclusive_207_);
v_val_221_ = lean_string_utf8_extract_fast(v_str_206_, v___x_220_, v_endExclusive_208_);
lean_dec(v_endExclusive_208_);
lean_dec(v___x_220_);
lean_dec_ref(v_str_206_);
v___x_222_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v_a_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_242_; 
v_a_223_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_242_ == 0)
{
v___x_225_ = v___x_222_;
v_isShared_226_ = v_isSharedCheck_242_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_a_223_);
lean_dec(v___x_222_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_242_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_227_; 
v___x_227_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_223_, v_name_217_);
lean_dec(v_a_223_);
if (lean_obj_tag(v___x_227_) == 1)
{
lean_object* v_val_228_; lean_object* v___x_229_; 
lean_del_object(v___x_225_);
lean_del_object(v___x_202_);
v_val_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_val_228_);
lean_dec_ref_known(v___x_227_, 1);
v___x_229_ = l_Lean_Language_Lean_setOption(v_opts_196_, v_val_228_, v_name_217_, v_val_221_);
return v___x_229_;
}
else
{
lean_object* v___x_230_; uint8_t v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_237_; 
lean_dec(v___x_227_);
lean_dec_ref(v_val_221_);
lean_dec_ref(v_opts_196_);
v___x_230_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__0));
v___x_231_ = 1;
v___x_232_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_217_, v___x_231_);
v___x_233_ = lean_string_append(v___x_230_, v___x_232_);
lean_dec_ref(v___x_232_);
v___x_234_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__1));
v___x_235_ = lean_string_append(v___x_233_, v___x_234_);
if (v_isShared_203_ == 0)
{
lean_ctor_set_tag(v___x_202_, 18);
lean_ctor_set(v___x_202_, 0, v___x_235_);
v___x_237_ = v___x_202_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_235_);
v___x_237_ = v_reuseFailAlloc_241_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
lean_object* v___x_239_; 
if (v_isShared_226_ == 0)
{
lean_ctor_set_tag(v___x_225_, 1);
lean_ctor_set(v___x_225_, 0, v___x_237_);
v___x_239_ = v___x_225_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_237_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
else
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_250_; 
lean_dec_ref(v_val_221_);
lean_dec(v_name_217_);
lean_del_object(v___x_202_);
lean_dec_ref(v_opts_196_);
v_a_243_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_250_ == 0)
{
v___x_245_ = v___x_222_;
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_222_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_248_; 
if (v_isShared_246_ == 0)
{
v___x_248_ = v___x_245_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_a_243_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
}
else
{
lean_object* v___x_252_; lean_object* v___x_254_; 
lean_del_object(v___x_210_);
lean_dec(v_endExclusive_208_);
lean_dec(v_startInclusive_207_);
lean_dec_ref(v_str_206_);
lean_dec(v___y_205_);
lean_dec_ref(v_opts_196_);
v___x_252_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__3));
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 0, v___x_252_);
v___x_254_ = v___x_202_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_252_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
}
}
else
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
lean_dec(v___x_199_);
lean_dec_ref(v_opts_196_);
v___x_265_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__4));
v___x_266_ = lean_string_append(v___x_265_, v_arg_197_);
lean_dec_ref(v_arg_197_);
v___x_267_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__5));
v___x_268_ = lean_string_append(v___x_266_, v___x_267_);
v___x_269_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
v___x_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
return v___x_270_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__setConfigOption___boxed(lean_object* v_opts_271_, lean_object* v_arg_272_, lean_object* v_a_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l___private_LeanIR_0__setConfigOption(v_opts_271_, v_arg_272_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1(lean_object* v_val_275_, lean_object* v_inst_276_, lean_object* v_R_277_, lean_object* v_a_278_, lean_object* v_b_279_, lean_object* v_c_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg(v_val_275_, v_a_278_, v_b_279_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___boxed(lean_object* v_val_282_, lean_object* v_inst_283_, lean_object* v_R_284_, lean_object* v_a_285_, lean_object* v_b_286_, lean_object* v_c_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1(v_val_282_, v_inst_283_, v_R_284_, v_a_285_, v_b_286_, v_c_287_);
lean_dec(v_b_286_);
lean_dec_ref(v_val_282_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0___redArg(lean_object* v___x_289_, lean_object* v_inst_290_, lean_object* v_ext_291_, lean_object* v_env_292_){
_start:
{
lean_object* v_toEnvExtension_294_; lean_object* v_addImportedFn_295_; lean_object* v_asyncMode_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v_importedEntries_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_327_; 
v_toEnvExtension_294_ = lean_ctor_get(v_ext_291_, 0);
lean_inc_ref(v_toEnvExtension_294_);
v_addImportedFn_295_ = lean_ctor_get(v_ext_291_, 2);
lean_inc_ref(v_addImportedFn_295_);
lean_dec_ref(v_ext_291_);
v_asyncMode_296_ = lean_ctor_get(v_toEnvExtension_294_, 2);
v___x_297_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v_inst_290_);
lean_inc_ref(v_env_292_);
v___x_298_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_297_, v_toEnvExtension_294_, v_env_292_, v_asyncMode_296_, v___x_289_);
lean_dec_ref(v___x_297_);
v_importedEntries_299_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_327_ == 0)
{
lean_object* v_unused_328_; 
v_unused_328_ = lean_ctor_get(v___x_298_, 1);
lean_dec(v_unused_328_);
v___x_301_ = v___x_298_;
v_isShared_302_ = v_isSharedCheck_327_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_importedEntries_299_);
lean_dec(v___x_298_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_327_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_303_ = l_Lean_Options_empty;
lean_inc_ref(v_env_292_);
v___x_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_304_, 0, v_env_292_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
lean_inc_ref(v_importedEntries_299_);
v___x_305_ = lean_apply_3(v_addImportedFn_295_, v_importedEntries_299_, v___x_304_, lean_box(0));
if (lean_obj_tag(v___x_305_) == 0)
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_318_; 
v_a_306_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_318_ == 0)
{
v___x_308_ = v___x_305_;
v_isShared_309_ = v_isSharedCheck_318_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_305_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_318_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 1, v_a_306_);
v___x_311_ = v___x_301_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_importedEntries_299_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_a_306_);
v___x_311_ = v_reuseFailAlloc_317_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_315_; 
v___x_312_ = lean_box(0);
v___x_313_ = l_Lean_EnvExtension_setState___redArg(v_toEnvExtension_294_, v_env_292_, v___x_311_, v___x_312_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v___x_313_);
v___x_315_ = v___x_308_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
else
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
lean_del_object(v___x_301_);
lean_dec_ref(v_importedEntries_299_);
lean_dec_ref(v_toEnvExtension_294_);
lean_dec_ref(v_env_292_);
v_a_319_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_326_ == 0)
{
v___x_321_ = v___x_305_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_305_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_a_319_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___elam__0___redArg___boxed(lean_object* v___x_329_, lean_object* v_inst_330_, lean_object* v_ext_331_, lean_object* v_env_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_main___elam__0___redArg(v___x_329_, v_inst_330_, v_ext_331_, v_env_332_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0(lean_object* v___x_335_, lean_object* v_00_u03b1_336_, lean_object* v_00_u03b2_337_, lean_object* v_00_u03c3_338_, lean_object* v_inst_339_, lean_object* v_ext_340_, lean_object* v_env_341_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_main___elam__0___redArg(v___x_335_, v_inst_339_, v_ext_340_, v_env_341_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0___boxed(lean_object* v___x_344_, lean_object* v_00_u03b1_345_, lean_object* v_00_u03b2_346_, lean_object* v_00_u03c3_347_, lean_object* v_inst_348_, lean_object* v_ext_349_, lean_object* v_env_350_, lean_object* v___y_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_main___elam__0(v___x_344_, v_00_u03b1_345_, v_00_u03b2_346_, v_00_u03c3_347_, v_inst_348_, v_ext_349_, v_env_350_);
return v_res_352_;
}
}
static lean_object* _init_l_panic___at___00main_spec__5___closed__0(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = l_instInhabitedError;
v___x_354_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_354_, 0, lean_box(0));
lean_closure_set(v___x_354_, 1, lean_box(0));
lean_closure_set(v___x_354_, 2, v___x_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00main_spec__5(lean_object* v_msg_355_){
_start:
{
lean_object* v___x_357_; lean_object* v___x_19590__overap_358_; lean_object* v___x_359_; 
v___x_357_ = lean_obj_once(&l_panic___at___00main_spec__5___closed__0, &l_panic___at___00main_spec__5___closed__0_once, _init_l_panic___at___00main_spec__5___closed__0);
v___x_19590__overap_358_ = lean_panic_fn_borrowed(v___x_357_, v_msg_355_);
v___x_359_ = lean_apply_1(v___x_19590__overap_358_, lean_box(0));
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00main_spec__5___boxed(lean_object* v_msg_360_, lean_object* v___y_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_panic___at___00main_spec__5(v_msg_360_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__8(lean_object* v_opts_363_, lean_object* v_opt_364_){
_start:
{
lean_object* v_name_365_; lean_object* v_defValue_366_; lean_object* v_map_367_; lean_object* v___x_368_; 
v_name_365_ = lean_ctor_get(v_opt_364_, 0);
v_defValue_366_ = lean_ctor_get(v_opt_364_, 1);
v_map_367_ = lean_ctor_get(v_opts_363_, 0);
v___x_368_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_367_, v_name_365_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_inc(v_defValue_366_);
return v_defValue_366_;
}
else
{
lean_object* v_val_369_; 
v_val_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_val_369_);
lean_dec_ref_known(v___x_368_, 1);
if (lean_obj_tag(v_val_369_) == 3)
{
lean_object* v_v_370_; 
v_v_370_ = lean_ctor_get(v_val_369_, 0);
lean_inc(v_v_370_);
lean_dec_ref_known(v_val_369_, 1);
return v_v_370_;
}
else
{
lean_dec(v_val_369_);
lean_inc(v_defValue_366_);
return v_defValue_366_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__8___boxed(lean_object* v_opts_371_, lean_object* v_opt_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_Option_get___at___00main_spec__8(v_opts_371_, v_opt_372_);
lean_dec_ref(v_opt_372_);
lean_dec_ref(v_opts_371_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(lean_object* v_a_374_, lean_object* v_x_375_){
_start:
{
if (lean_obj_tag(v_x_375_) == 0)
{
lean_dec(v_a_374_);
return v_x_375_;
}
else
{
lean_object* v_key_376_; lean_object* v_value_377_; lean_object* v_tail_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_411_; 
v_key_376_ = lean_ctor_get(v_x_375_, 0);
v_value_377_ = lean_ctor_get(v_x_375_, 1);
v_tail_378_ = lean_ctor_get(v_x_375_, 2);
v_isSharedCheck_411_ = !lean_is_exclusive(v_x_375_);
if (v_isSharedCheck_411_ == 0)
{
v___x_380_ = v_x_375_;
v_isShared_381_ = v_isSharedCheck_411_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_tail_378_);
lean_inc(v_value_377_);
lean_inc(v_key_376_);
lean_dec(v_x_375_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_411_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
uint8_t v___x_382_; 
v___x_382_ = lean_name_eq(v_key_376_, v_a_374_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; lean_object* v___x_385_; 
v___x_383_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(v_a_374_, v_tail_378_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 2, v___x_383_);
v___x_385_ = v___x_380_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_key_376_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v_value_377_);
lean_ctor_set(v_reuseFailAlloc_386_, 2, v___x_383_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
else
{
lean_object* v_toEffectiveImport_387_; lean_object* v_parts_388_; lean_object* v_irParts_389_; uint8_t v_needsIRTrans_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_410_; 
lean_dec(v_key_376_);
v_toEffectiveImport_387_ = lean_ctor_get(v_value_377_, 0);
v_parts_388_ = lean_ctor_get(v_value_377_, 1);
v_irParts_389_ = lean_ctor_get(v_value_377_, 2);
v_needsIRTrans_390_ = lean_ctor_get_uint8(v_value_377_, sizeof(void*)*3);
v_isSharedCheck_410_ = !lean_is_exclusive(v_value_377_);
if (v_isSharedCheck_410_ == 0)
{
v___x_392_ = v_value_377_;
v_isShared_393_ = v_isSharedCheck_410_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_irParts_389_);
lean_inc(v_parts_388_);
lean_inc(v_toEffectiveImport_387_);
lean_dec(v_value_377_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_410_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v_toImport_394_; uint8_t v_hasData_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_409_; 
v_toImport_394_ = lean_ctor_get(v_toEffectiveImport_387_, 0);
v_hasData_395_ = lean_ctor_get_uint8(v_toEffectiveImport_387_, sizeof(void*)*1 + 1);
v_isSharedCheck_409_ = !lean_is_exclusive(v_toEffectiveImport_387_);
if (v_isSharedCheck_409_ == 0)
{
v___x_397_ = v_toEffectiveImport_387_;
v_isShared_398_ = v_isSharedCheck_409_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_toImport_394_);
lean_dec(v_toEffectiveImport_387_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_409_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
uint8_t v___x_399_; lean_object* v___x_401_; 
v___x_399_ = 0;
if (v_isShared_398_ == 0)
{
v___x_401_ = v___x_397_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_toImport_394_);
lean_ctor_set_uint8(v_reuseFailAlloc_408_, sizeof(void*)*1 + 1, v_hasData_395_);
v___x_401_ = v_reuseFailAlloc_408_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
lean_object* v___x_403_; 
lean_ctor_set_uint8(v___x_401_, sizeof(void*)*1, v___x_399_);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 0, v___x_401_);
v___x_403_ = v___x_392_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_401_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_parts_388_);
lean_ctor_set(v_reuseFailAlloc_407_, 2, v_irParts_389_);
lean_ctor_set_uint8(v_reuseFailAlloc_407_, sizeof(void*)*3, v_needsIRTrans_390_);
v___x_403_ = v_reuseFailAlloc_407_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_405_; 
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 1, v___x_403_);
lean_ctor_set(v___x_380_, 0, v_a_374_);
v___x_405_ = v___x_380_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_374_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v___x_403_);
lean_ctor_set(v_reuseFailAlloc_406_, 2, v_tail_378_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(lean_object* v_m_412_, lean_object* v_a_413_){
_start:
{
lean_object* v_size_414_; lean_object* v_buckets_415_; lean_object* v___x_416_; uint64_t v___y_418_; 
v_size_414_ = lean_ctor_get(v_m_412_, 0);
v_buckets_415_ = lean_ctor_get(v_m_412_, 1);
v___x_416_ = lean_array_get_size(v_buckets_415_);
if (lean_obj_tag(v_a_413_) == 0)
{
uint64_t v___x_445_; 
v___x_445_ = 1723ULL;
v___y_418_ = v___x_445_;
goto v___jp_417_;
}
else
{
uint64_t v_hash_446_; 
v_hash_446_ = lean_ctor_get_uint64(v_a_413_, sizeof(void*)*2);
v___y_418_ = v_hash_446_;
goto v___jp_417_;
}
v___jp_417_:
{
uint64_t v___x_419_; uint64_t v___x_420_; uint64_t v_fold_421_; uint64_t v___x_422_; uint64_t v___x_423_; uint64_t v___x_424_; size_t v___x_425_; size_t v___x_426_; size_t v___x_427_; size_t v___x_428_; size_t v___x_429_; lean_object* v_bucket_430_; uint8_t v___x_431_; 
v___x_419_ = 32ULL;
v___x_420_ = lean_uint64_shift_right(v___y_418_, v___x_419_);
v_fold_421_ = lean_uint64_xor(v___y_418_, v___x_420_);
v___x_422_ = 16ULL;
v___x_423_ = lean_uint64_shift_right(v_fold_421_, v___x_422_);
v___x_424_ = lean_uint64_xor(v_fold_421_, v___x_423_);
v___x_425_ = lean_uint64_to_usize(v___x_424_);
v___x_426_ = lean_usize_of_nat(v___x_416_);
v___x_427_ = ((size_t)1ULL);
v___x_428_ = lean_usize_sub(v___x_426_, v___x_427_);
v___x_429_ = lean_usize_land(v___x_425_, v___x_428_);
v_bucket_430_ = lean_array_uget_borrowed(v_buckets_415_, v___x_429_);
v___x_431_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_a_413_, v_bucket_430_);
if (v___x_431_ == 0)
{
lean_dec(v_a_413_);
return v_m_412_;
}
else
{
lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_442_; 
lean_inc(v_bucket_430_);
lean_inc_ref(v_buckets_415_);
lean_inc(v_size_414_);
v_isSharedCheck_442_ = !lean_is_exclusive(v_m_412_);
if (v_isSharedCheck_442_ == 0)
{
lean_object* v_unused_443_; lean_object* v_unused_444_; 
v_unused_443_ = lean_ctor_get(v_m_412_, 1);
lean_dec(v_unused_443_);
v_unused_444_ = lean_ctor_get(v_m_412_, 0);
lean_dec(v_unused_444_);
v___x_433_ = v_m_412_;
v_isShared_434_ = v_isSharedCheck_442_;
goto v_resetjp_432_;
}
else
{
lean_dec(v_m_412_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_442_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_435_; lean_object* v_buckets_436_; lean_object* v_bucket_437_; lean_object* v___x_438_; lean_object* v___x_440_; 
v___x_435_ = lean_box(0);
v_buckets_436_ = lean_array_uset(v_buckets_415_, v___x_429_, v___x_435_);
v_bucket_437_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(v_a_413_, v_bucket_430_);
v___x_438_ = lean_array_uset(v_buckets_436_, v___x_429_, v_bucket_437_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 1, v___x_438_);
v___x_440_ = v___x_433_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_size_414_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v___x_438_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__0(lean_object* v___x_447_, lean_object* v___x_448_, uint8_t v___x_449_, lean_object* v_importArts_450_, uint8_t v___y_451_, uint8_t v___x_452_, lean_object* v_name_453_, uint8_t v___x_454_, lean_object* v___x_455_, uint8_t v___x_456_){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = lean_st_mk_ref(v___x_447_);
v___x_459_ = l_Lean_importModulesCore(v___x_448_, v___x_449_, v_importArts_450_, v___y_451_, v___x_452_, v___x_458_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v___x_460_; lean_object* v_moduleNameMap_461_; lean_object* v_moduleNames_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_476_; 
lean_dec_ref_known(v___x_459_, 1);
v___x_460_ = lean_st_ref_get(v___x_458_);
lean_dec(v___x_458_);
v_moduleNameMap_461_ = lean_ctor_get(v___x_460_, 0);
v_moduleNames_462_ = lean_ctor_get(v___x_460_, 1);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_476_ == 0)
{
v___x_464_ = v___x_460_;
v_isShared_465_ = v_isSharedCheck_476_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_moduleNames_462_);
lean_inc(v_moduleNameMap_461_);
lean_dec(v___x_460_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_476_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_466_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(v_moduleNameMap_461_, v_name_453_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v___x_466_);
v___x_468_ = v___x_464_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_466_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_moduleNames_462_);
v___x_468_ = v_reuseFailAlloc_475_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
uint32_t v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_469_ = 0;
v___x_470_ = l_Lean_OLeanLevel_ctorIdx(v___x_449_);
v___x_471_ = l_Lean_OLeanLevel_ctorIdx(v___x_454_);
v___x_472_ = lean_nat_dec_eq(v___x_470_, v___x_471_);
lean_dec(v___x_471_);
lean_dec(v___x_470_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; 
v___x_473_ = l_Lean_finalizeImport(v___x_468_, v___x_448_, v___x_455_, v___x_469_, v___x_452_, v___x_456_, v___x_449_, v___x_452_, v___x_452_);
lean_dec_ref(v___x_468_);
return v___x_473_;
}
else
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_finalizeImport(v___x_468_, v___x_448_, v___x_455_, v___x_469_, v___x_452_, v___x_456_, v___x_449_, v___x_456_, v___x_452_);
lean_dec_ref(v___x_468_);
return v___x_474_;
}
}
}
}
else
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_484_; 
lean_dec(v___x_458_);
lean_dec_ref(v___x_455_);
lean_dec(v_name_453_);
lean_dec_ref(v___x_448_);
v_a_477_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_484_ == 0)
{
v___x_479_ = v___x_459_;
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_459_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_480_ == 0)
{
v___x_482_ = v___x_479_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_a_477_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__0___boxed(lean_object* v___x_485_, lean_object* v___x_486_, lean_object* v___x_487_, lean_object* v_importArts_488_, lean_object* v___y_489_, lean_object* v___x_490_, lean_object* v_name_491_, lean_object* v___x_492_, lean_object* v___x_493_, lean_object* v___x_494_, lean_object* v___y_495_){
_start:
{
uint8_t v___x_36637__boxed_496_; uint8_t v___y_36638__boxed_497_; uint8_t v___x_36639__boxed_498_; uint8_t v___x_36640__boxed_499_; uint8_t v___x_36642__boxed_500_; lean_object* v_res_501_; 
v___x_36637__boxed_496_ = lean_unbox(v___x_487_);
v___y_36638__boxed_497_ = lean_unbox(v___y_489_);
v___x_36639__boxed_498_ = lean_unbox(v___x_490_);
v___x_36640__boxed_499_ = lean_unbox(v___x_492_);
v___x_36642__boxed_500_ = lean_unbox(v___x_494_);
v_res_501_ = l_main___lam__0(v___x_485_, v___x_486_, v___x_36637__boxed_496_, v_importArts_488_, v___y_36638__boxed_497_, v___x_36639__boxed_498_, v_name_491_, v___x_36640__boxed_499_, v___x_493_, v___x_36642__boxed_500_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_main___lam__1(lean_object* v___x_505_, lean_object* v___x_506_, uint16_t v___x_507_, lean_object* v_name_508_, lean_object* v_a_509_, uint8_t v___x_510_, lean_object* v___x_511_, lean_object* v_head_512_, lean_object* v___x_513_, lean_object* v___x_514_, lean_object* v___x_515_, lean_object* v___x_516_, lean_object* v___x_517_, lean_object* v___x_518_, lean_object* v___x_519_, lean_object* v___x_520_, uint8_t v___x_521_, uint8_t v___x_522_){
_start:
{
lean_object* v_a_525_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v_fileName_531_; lean_object* v_fileMap_532_; lean_object* v_currNamespace_533_; lean_object* v_openDecls_534_; lean_object* v_initHeartbeats_535_; lean_object* v_maxHeartbeats_536_; lean_object* v_quotContext_537_; lean_object* v_currMacroScope_538_; lean_object* v_cancelTk_x3f_539_; lean_object* v_inheritedTraceOptions_540_; lean_object* v_currRecDepth_541_; lean_object* v_ref_542_; uint8_t v_suppressElabErrors_543_; uint8_t v_isRecordingDeps_544_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; uint8_t v___y_580_; uint8_t v___y_602_; uint8_t v___y_603_; lean_object* v_env_604_; uint8_t v___x_605_; uint8_t v___y_607_; uint16_t v___x_608_; uint16_t v___x_609_; uint16_t v___x_610_; uint8_t v___x_611_; 
v___x_528_ = lean_io_get_num_heartbeats();
v___x_529_ = lean_st_mk_ref(v___x_505_);
v___x_576_ = l_Lean_inheritedTraceOptions;
v___x_577_ = lean_st_ref_get(v___x_576_);
v___x_578_ = lean_st_ref_get(v___x_529_);
v_env_604_ = lean_ctor_get(v___x_578_, 0);
lean_inc_ref(v_env_604_);
lean_dec(v___x_578_);
v___x_605_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_604_);
lean_dec_ref(v_env_604_);
v___x_608_ = 512;
v___x_609_ = lean_uint16_land(v___x_507_, v___x_608_);
v___x_610_ = 0;
v___x_611_ = lean_uint16_dec_eq(v___x_609_, v___x_610_);
if (v___x_611_ == 0)
{
v___y_607_ = v___x_510_;
goto v___jp_606_;
}
else
{
v___y_607_ = v___x_522_;
goto v___jp_606_;
}
v___jp_524_:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_mk_io_user_error(v_a_525_);
v___x_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
return v___x_527_;
}
v___jp_530_:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_545_ = l_Lean_maxRecDepth;
v___x_546_ = l_Lean_Option_get___at___00main_spec__8(v___x_506_, v___x_545_);
v___x_547_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_547_, 0, v_fileName_531_);
lean_ctor_set(v___x_547_, 1, v_fileMap_532_);
lean_ctor_set(v___x_547_, 2, v___x_506_);
lean_ctor_set(v___x_547_, 3, v___x_546_);
lean_ctor_set(v___x_547_, 4, v_currNamespace_533_);
lean_ctor_set(v___x_547_, 5, v_openDecls_534_);
lean_ctor_set(v___x_547_, 6, v_initHeartbeats_535_);
lean_ctor_set(v___x_547_, 7, v_maxHeartbeats_536_);
lean_ctor_set(v___x_547_, 8, v_quotContext_537_);
lean_ctor_set(v___x_547_, 9, v_currMacroScope_538_);
lean_ctor_set(v___x_547_, 10, v_cancelTk_x3f_539_);
lean_ctor_set(v___x_547_, 11, v_inheritedTraceOptions_540_);
v___x_548_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_548_, 0, v___x_547_);
lean_ctor_set(v___x_548_, 1, v_currRecDepth_541_);
lean_ctor_set(v___x_548_, 2, v_ref_542_);
lean_ctor_set_uint16(v___x_548_, sizeof(void*)*3, v___x_507_);
lean_ctor_set_uint8(v___x_548_, sizeof(void*)*3 + 2, v_suppressElabErrors_543_);
lean_ctor_set_uint8(v___x_548_, sizeof(void*)*3 + 3, v_isRecordingDeps_544_);
v___x_549_ = l_Lean_Compiler_LCNF_emitC(v_name_508_, v___x_548_, v___x_529_);
lean_dec_ref_known(v___x_548_, 3);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v_a_550_ = lean_ctor_get(v___x_549_, 0);
lean_inc(v_a_550_);
lean_dec_ref_known(v___x_549_, 1);
v___x_551_ = lean_st_ref_get(v___x_529_);
lean_dec(v___x_529_);
lean_dec(v___x_551_);
v___x_552_ = lean_string_to_utf8(v_a_550_);
lean_dec(v_a_550_);
v___x_553_ = lean_io_prim_handle_write(v_a_509_, v___x_552_);
lean_dec_ref(v___x_552_);
return v___x_553_;
}
else
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_575_; 
lean_dec(v___x_529_);
v_a_554_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_575_ == 0)
{
v___x_556_ = v___x_549_;
v_isShared_557_ = v_isSharedCheck_575_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_549_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_575_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
if (lean_obj_tag(v_a_554_) == 0)
{
lean_object* v_msg_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_562_; 
v_msg_558_ = lean_ctor_get(v_a_554_, 1);
lean_inc_ref(v_msg_558_);
lean_dec_ref_known(v_a_554_, 2);
v___x_559_ = l_Lean_MessageData_toString(v_msg_558_);
v___x_560_ = lean_mk_io_user_error(v___x_559_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v___x_560_);
v___x_562_ = v___x_556_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_560_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
else
{
lean_object* v_id_564_; lean_object* v___x_565_; 
lean_del_object(v___x_556_);
v_id_564_ = lean_ctor_get(v_a_554_, 0);
lean_inc(v_id_564_);
lean_dec_ref_known(v_a_554_, 2);
v___x_565_ = l_Lean_InternalExceptionId_getName(v_id_564_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
lean_dec(v_id_564_);
v_a_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_a_566_);
lean_dec_ref_known(v___x_565_, 1);
v___x_567_ = ((lean_object*)(l_main___lam__1___closed__0));
v___x_568_ = l_Lean_Name_toString(v_a_566_, v___x_510_);
v___x_569_ = lean_string_append(v___x_567_, v___x_568_);
lean_dec_ref(v___x_568_);
v_a_525_ = v___x_569_;
goto v___jp_524_;
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec_ref_known(v___x_565_, 1);
v___x_570_ = ((lean_object*)(l_main___lam__1___closed__1));
v___x_571_ = l_Nat_reprFast(v_id_564_);
v___x_572_ = lean_string_append(v___x_570_, v___x_571_);
lean_dec_ref(v___x_571_);
v___x_573_ = ((lean_object*)(l_main___lam__1___closed__2));
v___x_574_ = lean_string_append(v___x_572_, v___x_573_);
v_a_525_ = v___x_574_;
goto v___jp_524_;
}
}
}
}
}
v___jp_579_:
{
lean_object* v___x_581_; lean_object* v_env_582_; lean_object* v_nextMacroScope_583_; lean_object* v_ngen_584_; lean_object* v_auxDeclNGen_585_; lean_object* v_traceState_586_; lean_object* v_recordedDeps_587_; lean_object* v_messages_588_; lean_object* v_infoState_589_; lean_object* v_snapshotTasks_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_599_; 
v___x_581_ = lean_st_ref_take(v___x_529_);
v_env_582_ = lean_ctor_get(v___x_581_, 0);
v_nextMacroScope_583_ = lean_ctor_get(v___x_581_, 1);
v_ngen_584_ = lean_ctor_get(v___x_581_, 2);
v_auxDeclNGen_585_ = lean_ctor_get(v___x_581_, 3);
v_traceState_586_ = lean_ctor_get(v___x_581_, 4);
v_recordedDeps_587_ = lean_ctor_get(v___x_581_, 6);
v_messages_588_ = lean_ctor_get(v___x_581_, 7);
v_infoState_589_ = lean_ctor_get(v___x_581_, 8);
v_snapshotTasks_590_ = lean_ctor_get(v___x_581_, 9);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_599_ == 0)
{
lean_object* v_unused_600_; 
v_unused_600_ = lean_ctor_get(v___x_581_, 5);
lean_dec(v_unused_600_);
v___x_592_ = v___x_581_;
v_isShared_593_ = v_isSharedCheck_599_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_snapshotTasks_590_);
lean_inc(v_infoState_589_);
lean_inc(v_messages_588_);
lean_inc(v_recordedDeps_587_);
lean_inc(v_traceState_586_);
lean_inc(v_auxDeclNGen_585_);
lean_inc(v_ngen_584_);
lean_inc(v_nextMacroScope_583_);
lean_inc(v_env_582_);
lean_dec(v___x_581_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_599_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; lean_object* v___x_596_; 
v___x_594_ = l_Lean_Kernel_enableDiag(v_env_582_, v___y_580_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 5, v___x_511_);
lean_ctor_set(v___x_592_, 0, v___x_594_);
v___x_596_ = v___x_592_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_594_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_nextMacroScope_583_);
lean_ctor_set(v_reuseFailAlloc_598_, 2, v_ngen_584_);
lean_ctor_set(v_reuseFailAlloc_598_, 3, v_auxDeclNGen_585_);
lean_ctor_set(v_reuseFailAlloc_598_, 4, v_traceState_586_);
lean_ctor_set(v_reuseFailAlloc_598_, 5, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_598_, 6, v_recordedDeps_587_);
lean_ctor_set(v_reuseFailAlloc_598_, 7, v_messages_588_);
lean_ctor_set(v_reuseFailAlloc_598_, 8, v_infoState_589_);
lean_ctor_set(v_reuseFailAlloc_598_, 9, v_snapshotTasks_590_);
v___x_596_ = v_reuseFailAlloc_598_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_597_; 
v___x_597_ = lean_st_ref_put(v___x_529_, v___x_596_);
lean_inc(v___x_514_);
v_fileName_531_ = v_head_512_;
v_fileMap_532_ = v___x_513_;
v_currNamespace_533_ = v___x_514_;
v_openDecls_534_ = v___x_515_;
v_initHeartbeats_535_ = v___x_528_;
v_maxHeartbeats_536_ = v___x_516_;
v_quotContext_537_ = v___x_514_;
v_currMacroScope_538_ = v___x_517_;
v_cancelTk_x3f_539_ = v___x_518_;
v_inheritedTraceOptions_540_ = v___x_577_;
v_currRecDepth_541_ = v___x_519_;
v_ref_542_ = v___x_520_;
v_suppressElabErrors_543_ = v___x_521_;
v_isRecordingDeps_544_ = v___x_521_;
goto v___jp_530_;
}
}
}
v___jp_601_:
{
if (v___y_603_ == 0)
{
v___y_580_ = v___y_602_;
goto v___jp_579_;
}
else
{
lean_dec_ref(v___x_511_);
lean_inc(v___x_514_);
v_fileName_531_ = v_head_512_;
v_fileMap_532_ = v___x_513_;
v_currNamespace_533_ = v___x_514_;
v_openDecls_534_ = v___x_515_;
v_initHeartbeats_535_ = v___x_528_;
v_maxHeartbeats_536_ = v___x_516_;
v_quotContext_537_ = v___x_514_;
v_currMacroScope_538_ = v___x_517_;
v_cancelTk_x3f_539_ = v___x_518_;
v_inheritedTraceOptions_540_ = v___x_577_;
v_currRecDepth_541_ = v___x_519_;
v_ref_542_ = v___x_520_;
v_suppressElabErrors_543_ = v___x_521_;
v_isRecordingDeps_544_ = v___x_521_;
goto v___jp_530_;
}
}
v___jp_606_:
{
if (v___y_607_ == 0)
{
if (v___x_605_ == 0)
{
v___y_602_ = v___y_607_;
v___y_603_ = v___x_510_;
goto v___jp_601_;
}
else
{
v___y_580_ = v___y_607_;
goto v___jp_579_;
}
}
else
{
v___y_602_ = v___y_607_;
v___y_603_ = v___x_605_;
goto v___jp_601_;
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__1___boxed(lean_object** _args){
lean_object* v___x_612_ = _args[0];
lean_object* v___x_613_ = _args[1];
lean_object* v___x_614_ = _args[2];
lean_object* v_name_615_ = _args[3];
lean_object* v_a_616_ = _args[4];
lean_object* v___x_617_ = _args[5];
lean_object* v___x_618_ = _args[6];
lean_object* v_head_619_ = _args[7];
lean_object* v___x_620_ = _args[8];
lean_object* v___x_621_ = _args[9];
lean_object* v___x_622_ = _args[10];
lean_object* v___x_623_ = _args[11];
lean_object* v___x_624_ = _args[12];
lean_object* v___x_625_ = _args[13];
lean_object* v___x_626_ = _args[14];
lean_object* v___x_627_ = _args[15];
lean_object* v___x_628_ = _args[16];
lean_object* v___x_629_ = _args[17];
lean_object* v___y_630_ = _args[18];
_start:
{
uint16_t v___x_36721__boxed_631_; uint8_t v___x_36723__boxed_632_; uint8_t v___x_36734__boxed_633_; uint8_t v___x_36735__boxed_634_; lean_object* v_res_635_; 
v___x_36721__boxed_631_ = lean_unbox(v___x_614_);
v___x_36723__boxed_632_ = lean_unbox(v___x_617_);
v___x_36734__boxed_633_ = lean_unbox(v___x_628_);
v___x_36735__boxed_634_ = lean_unbox(v___x_629_);
v_res_635_ = l_main___lam__1(v___x_612_, v___x_613_, v___x_36721__boxed_631_, v_name_615_, v_a_616_, v___x_36723__boxed_632_, v___x_618_, v_head_619_, v___x_620_, v___x_621_, v___x_622_, v___x_623_, v___x_624_, v___x_625_, v___x_626_, v___x_627_, v___x_36734__boxed_633_, v___x_36735__boxed_634_);
lean_dec(v_a_616_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(lean_object* v_x2_636_, lean_object* v_as_637_, size_t v_i_638_, size_t v_stop_639_, lean_object* v_b_640_){
_start:
{
uint8_t v___x_641_; 
v___x_641_ = lean_usize_dec_eq(v_i_638_, v_stop_639_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; lean_object* v___x_643_; size_t v___x_644_; size_t v___x_645_; 
v___x_642_ = lean_array_uget_borrowed(v_as_637_, v_i_638_);
lean_inc_ref(v_x2_636_);
lean_inc(v___x_642_);
v___x_643_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_642_, v_x2_636_, v_b_640_);
v___x_644_ = ((size_t)1ULL);
v___x_645_ = lean_usize_add(v_i_638_, v___x_644_);
v_i_638_ = v___x_645_;
v_b_640_ = v___x_643_;
goto _start;
}
else
{
lean_dec_ref(v_x2_636_);
return v_b_640_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2___boxed(lean_object* v_x2_647_, lean_object* v_as_648_, lean_object* v_i_649_, lean_object* v_stop_650_, lean_object* v_b_651_){
_start:
{
size_t v_i_boxed_652_; size_t v_stop_boxed_653_; lean_object* v_res_654_; 
v_i_boxed_652_ = lean_unbox_usize(v_i_649_);
lean_dec(v_i_649_);
v_stop_boxed_653_ = lean_unbox_usize(v_stop_650_);
lean_dec(v_stop_650_);
v_res_654_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v_x2_647_, v_as_648_, v_i_boxed_652_, v_stop_boxed_653_, v_b_651_);
lean_dec_ref(v_as_648_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(lean_object* v_as_655_, size_t v_i_656_, size_t v_stop_657_, lean_object* v_b_658_){
_start:
{
lean_object* v___y_660_; uint8_t v___x_664_; 
v___x_664_ = lean_usize_dec_eq(v_i_656_, v_stop_657_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; lean_object* v_declNames_666_; lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_665_ = lean_array_uget_borrowed(v_as_655_, v_i_656_);
v_declNames_666_ = lean_ctor_get(v___x_665_, 0);
v___x_667_ = lean_unsigned_to_nat(0u);
v___x_668_ = lean_array_get_size(v_declNames_666_);
v___x_669_ = lean_nat_dec_lt(v___x_667_, v___x_668_);
if (v___x_669_ == 0)
{
v___y_660_ = v_b_658_;
goto v___jp_659_;
}
else
{
uint8_t v___x_670_; 
v___x_670_ = lean_nat_dec_le(v___x_668_, v___x_668_);
if (v___x_670_ == 0)
{
if (v___x_669_ == 0)
{
v___y_660_ = v_b_658_;
goto v___jp_659_;
}
else
{
size_t v___x_671_; size_t v___x_672_; lean_object* v___x_673_; 
v___x_671_ = ((size_t)0ULL);
v___x_672_ = lean_usize_of_nat(v___x_668_);
lean_inc(v___x_665_);
v___x_673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_665_, v_declNames_666_, v___x_671_, v___x_672_, v_b_658_);
v___y_660_ = v___x_673_;
goto v___jp_659_;
}
}
else
{
size_t v___x_674_; size_t v___x_675_; lean_object* v___x_676_; 
v___x_674_ = ((size_t)0ULL);
v___x_675_ = lean_usize_of_nat(v___x_668_);
lean_inc(v___x_665_);
v___x_676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_665_, v_declNames_666_, v___x_674_, v___x_675_, v_b_658_);
v___y_660_ = v___x_676_;
goto v___jp_659_;
}
}
}
else
{
return v_b_658_;
}
v___jp_659_:
{
size_t v___x_661_; size_t v___x_662_; 
v___x_661_ = ((size_t)1ULL);
v___x_662_ = lean_usize_add(v_i_656_, v___x_661_);
v_i_656_ = v___x_662_;
v_b_658_ = v___y_660_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14___boxed(lean_object* v_as_677_, lean_object* v_i_678_, lean_object* v_stop_679_, lean_object* v_b_680_){
_start:
{
size_t v_i_boxed_681_; size_t v_stop_boxed_682_; lean_object* v_res_683_; 
v_i_boxed_681_ = lean_unbox_usize(v_i_678_);
lean_dec(v_i_678_);
v_stop_boxed_682_ = lean_unbox_usize(v_stop_679_);
lean_dec(v_stop_679_);
v_res_683_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(v_as_677_, v_i_boxed_681_, v_stop_boxed_682_, v_b_680_);
lean_dec_ref(v_as_677_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(lean_object* v_s_684_){
_start:
{
lean_object* v___x_686_; lean_object* v_putStr_687_; lean_object* v___x_688_; 
v___x_686_ = lean_get_stderr();
v_putStr_687_ = lean_ctor_get(v___x_686_, 4);
lean_inc_ref(v_putStr_687_);
lean_dec_ref(v___x_686_);
v___x_688_ = lean_apply_2(v_putStr_687_, v_s_684_, lean_box(0));
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8___boxed(lean_object* v_s_689_, lean_object* v_a_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v_s_689_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6(lean_object* v_s_692_){
_start:
{
uint32_t v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_694_ = 10;
v___x_695_ = lean_string_push(v_s_692_, v___x_694_);
v___x_696_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v___x_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6___boxed(lean_object* v_s_697_, lean_object* v_a_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_IO_eprintln___at___00main_spec__6(v_s_697_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(lean_object* v_o_703_, lean_object* v_k_704_, lean_object* v_v_705_){
_start:
{
lean_object* v_map_706_; uint8_t v_hasTrace_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_721_; 
v_map_706_ = lean_ctor_get(v_o_703_, 0);
v_hasTrace_707_ = lean_ctor_get_uint8(v_o_703_, sizeof(void*)*1);
v_isSharedCheck_721_ = !lean_is_exclusive(v_o_703_);
if (v_isSharedCheck_721_ == 0)
{
v___x_709_ = v_o_703_;
v_isShared_710_ = v_isSharedCheck_721_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_map_706_);
lean_dec(v_o_703_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_721_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_711_, 0, v_v_705_);
lean_inc(v_k_704_);
v___x_712_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_704_, v___x_711_, v_map_706_);
if (v_hasTrace_707_ == 0)
{
lean_object* v___x_713_; uint8_t v___x_714_; lean_object* v___x_716_; 
v___x_713_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_714_ = l_Lean_Name_isPrefixOf(v___x_713_, v_k_704_);
lean_dec(v_k_704_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v___x_712_);
v___x_716_ = v___x_709_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_712_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_ctor_set_uint8(v___x_716_, sizeof(void*)*1, v___x_714_);
return v___x_716_;
}
}
else
{
lean_object* v___x_719_; 
lean_dec(v_k_704_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v___x_712_);
v___x_719_ = v___x_709_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_712_);
lean_ctor_set_uint8(v_reuseFailAlloc_720_, sizeof(void*)*1, v_hasTrace_707_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00main_spec__3(lean_object* v_opts_722_, lean_object* v_opt_723_, lean_object* v_val_724_){
_start:
{
lean_object* v_name_725_; lean_object* v___x_726_; 
v_name_725_ = lean_ctor_get(v_opt_723_, 0);
lean_inc(v_name_725_);
lean_dec_ref(v_opt_723_);
v___x_726_ = l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(v_opts_722_, v_name_725_, v_val_724_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(lean_object* v_as_727_, size_t v_i_728_, size_t v_stop_729_, lean_object* v_b_730_){
_start:
{
uint8_t v___x_731_; 
v___x_731_ = lean_usize_dec_eq(v_i_728_, v_stop_729_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; lean_object* v_name_733_; lean_object* v___x_734_; size_t v___x_735_; size_t v___x_736_; 
v___x_732_ = lean_array_uget_borrowed(v_as_727_, v_i_728_);
v_name_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc(v_name_733_);
v___x_734_ = l_Lean_Compiler_LCNF_setDeclPublic(v_b_730_, v_name_733_);
v___x_735_ = ((size_t)1ULL);
v___x_736_ = lean_usize_add(v_i_728_, v___x_735_);
v_i_728_ = v___x_736_;
v_b_730_ = v___x_734_;
goto _start;
}
else
{
return v_b_730_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___boxed(lean_object* v_as_738_, lean_object* v_i_739_, lean_object* v_stop_740_, lean_object* v_b_741_){
_start:
{
size_t v_i_boxed_742_; size_t v_stop_boxed_743_; lean_object* v_res_744_; 
v_i_boxed_742_ = lean_unbox_usize(v_i_739_);
lean_dec(v_i_739_);
v_stop_boxed_743_ = lean_unbox_usize(v_stop_740_);
lean_dec(v_stop_740_);
v_res_744_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v_as_738_, v_i_boxed_742_, v_stop_boxed_743_, v_b_741_);
lean_dec_ref(v_as_738_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg(lean_object* v_as_x27_746_, lean_object* v_b_747_){
_start:
{
if (lean_obj_tag(v_as_x27_746_) == 0)
{
lean_object* v___x_749_; 
v___x_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_749_, 0, v_b_747_);
return v___x_749_;
}
else
{
lean_object* v_head_750_; lean_object* v_tail_751_; lean_object* v_fst_752_; lean_object* v_snd_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_778_; 
v_head_750_ = lean_ctor_get(v_as_x27_746_, 0);
v_tail_751_ = lean_ctor_get(v_as_x27_746_, 1);
v_fst_752_ = lean_ctor_get(v_b_747_, 0);
v_snd_753_ = lean_ctor_get(v_b_747_, 1);
v_isSharedCheck_778_ = !lean_is_exclusive(v_b_747_);
if (v_isSharedCheck_778_ == 0)
{
v___x_755_ = v_b_747_;
v_isShared_756_ = v_isSharedCheck_778_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_snd_753_);
lean_inc(v_fst_752_);
lean_dec(v_b_747_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_778_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_757_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0));
v___x_758_ = lean_string_dec_eq(v_head_750_, v___x_757_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; 
lean_inc(v_head_750_);
v___x_759_ = l___private_LeanIR_0__setConfigOption(v_snd_753_, v_head_750_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v___x_762_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_760_);
lean_dec_ref_known(v___x_759_, 1);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 1, v_a_760_);
v___x_762_ = v___x_755_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_fst_752_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_a_760_);
v___x_762_ = v_reuseFailAlloc_764_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
v_as_x27_746_ = v_tail_751_;
v_b_747_ = v___x_762_;
goto _start;
}
}
else
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
lean_del_object(v___x_755_);
lean_dec(v_fst_752_);
v_a_765_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_759_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_759_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
else
{
lean_object* v___x_773_; lean_object* v___x_775_; 
lean_dec(v_fst_752_);
v___x_773_ = lean_box(v___x_758_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v___x_773_);
v___x_775_ = v___x_755_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_773_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_snd_753_);
v___x_775_ = v_reuseFailAlloc_777_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
v_as_x27_746_ = v_tail_751_;
v_b_747_ = v___x_775_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg___boxed(lean_object* v_as_x27_779_, lean_object* v_b_780_, lean_object* v___y_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_779_, v_b_780_);
lean_dec(v_as_x27_779_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(lean_object* v_a_783_, lean_object* v_as_784_, size_t v_i_785_, size_t v_stop_786_, lean_object* v_b_787_){
_start:
{
lean_object* v___y_789_; uint8_t v___x_793_; 
v___x_793_ = lean_usize_dec_eq(v_i_785_, v_stop_786_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; lean_object* v_name_795_; uint8_t v___x_796_; 
v___x_794_ = lean_array_uget_borrowed(v_as_784_, v_i_785_);
v_name_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_name_795_);
lean_inc_ref(v_a_783_);
v___x_796_ = l_Lean_isExtern(v_a_783_, v_name_795_);
if (v___x_796_ == 0)
{
v___y_789_ = v_b_787_;
goto v___jp_788_;
}
else
{
lean_object* v___x_797_; 
lean_inc(v___x_794_);
v___x_797_ = lean_array_push(v_b_787_, v___x_794_);
v___y_789_ = v___x_797_;
goto v___jp_788_;
}
}
else
{
lean_dec_ref(v_a_783_);
return v_b_787_;
}
v___jp_788_:
{
size_t v___x_790_; size_t v___x_791_; 
v___x_790_ = ((size_t)1ULL);
v___x_791_ = lean_usize_add(v_i_785_, v___x_790_);
v_i_785_ = v___x_791_;
v_b_787_ = v___y_789_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18___boxed(lean_object* v_a_798_, lean_object* v_as_799_, lean_object* v_i_800_, lean_object* v_stop_801_, lean_object* v_b_802_){
_start:
{
size_t v_i_boxed_803_; size_t v_stop_boxed_804_; lean_object* v_res_805_; 
v_i_boxed_803_ = lean_unbox_usize(v_i_800_);
lean_dec(v_i_800_);
v_stop_boxed_804_ = lean_unbox_usize(v_stop_801_);
lean_dec(v_stop_801_);
v_res_805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_a_798_, v_as_799_, v_i_boxed_803_, v_stop_boxed_804_, v_b_802_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(lean_object* v___y_828_, lean_object* v_as_829_, size_t v_i_830_, size_t v_stop_831_, lean_object* v_b_832_){
_start:
{
lean_object* v___y_834_; uint8_t v___x_838_; 
v___x_838_ = lean_usize_dec_eq(v_i_830_, v_stop_831_);
if (v___x_838_ == 0)
{
lean_object* v_fst_839_; lean_object* v_snd_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___y_844_; 
v_fst_839_ = lean_ctor_get(v_b_832_, 0);
v_snd_840_ = lean_ctor_get(v_b_832_, 1);
v___x_841_ = lean_array_uget_borrowed(v_as_829_, v_i_830_);
v___x_842_ = l_Lean_IR_Decl_name(v___x_841_);
if (lean_obj_tag(v___x_842_) == 1)
{
lean_object* v_pre_857_; lean_object* v_str_858_; lean_object* v___x_859_; uint8_t v___x_860_; 
v_pre_857_ = lean_ctor_get(v___x_842_, 0);
v_str_858_ = lean_ctor_get(v___x_842_, 1);
v___x_859_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___closed__0));
v___x_860_ = lean_string_dec_eq(v_str_858_, v___x_859_);
if (v___x_860_ == 0)
{
lean_inc_ref(v___x_842_);
v___y_844_ = v___x_842_;
goto v___jp_843_;
}
else
{
lean_inc(v_pre_857_);
v___y_844_ = v_pre_857_;
goto v___jp_843_;
}
}
else
{
lean_inc(v___x_842_);
v___y_844_ = v___x_842_;
goto v___jp_843_;
}
v___jp_843_:
{
uint8_t v___x_845_; 
lean_inc_ref(v___y_828_);
v___x_845_ = l_Lean_isExtern(v___y_828_, v___y_844_);
if (v___x_845_ == 0)
{
lean_dec(v___x_842_);
v___y_834_ = v_b_832_;
goto v___jp_833_;
}
else
{
lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_854_; 
lean_inc(v_snd_840_);
lean_inc(v_fst_839_);
v_isSharedCheck_854_ = !lean_is_exclusive(v_b_832_);
if (v_isSharedCheck_854_ == 0)
{
lean_object* v_unused_855_; lean_object* v_unused_856_; 
v_unused_855_ = lean_ctor_get(v_b_832_, 1);
lean_dec(v_unused_855_);
v_unused_856_ = lean_ctor_get(v_b_832_, 0);
lean_dec(v_unused_856_);
v___x_847_ = v_b_832_;
v_isShared_848_ = v_isSharedCheck_854_;
goto v_resetjp_846_;
}
else
{
lean_dec(v_b_832_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_854_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_852_; 
lean_inc_n(v___x_841_, 2);
v___x_849_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_841_);
lean_ctor_set(v___x_849_, 1, v_fst_839_);
v___x_850_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(v_snd_840_, v___x_842_, v___x_841_);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 1, v___x_850_);
lean_ctor_set(v___x_847_, 0, v___x_849_);
v___x_852_ = v___x_847_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_849_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v___x_850_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
v___y_834_ = v___x_852_;
goto v___jp_833_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_828_);
return v_b_832_;
}
v___jp_833_:
{
size_t v___x_835_; size_t v___x_836_; 
v___x_835_ = ((size_t)1ULL);
v___x_836_ = lean_usize_add(v_i_830_, v___x_835_);
v_i_830_ = v___x_836_;
v_b_832_ = v___y_834_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___boxed(lean_object* v___y_861_, lean_object* v_as_862_, lean_object* v_i_863_, lean_object* v_stop_864_, lean_object* v_b_865_){
_start:
{
size_t v_i_boxed_866_; size_t v_stop_boxed_867_; lean_object* v_res_868_; 
v_i_boxed_866_ = lean_unbox_usize(v_i_863_);
lean_dec(v_i_863_);
v_stop_boxed_867_ = lean_unbox_usize(v_stop_864_);
lean_dec(v_stop_864_);
v_res_868_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_861_, v_as_862_, v_i_boxed_866_, v_stop_boxed_867_, v_b_865_);
lean_dec_ref(v_as_862_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27(lean_object* v_as_872_, size_t v_sz_873_, size_t v_i_874_, lean_object* v_b_875_){
_start:
{
uint8_t v___x_877_; 
v___x_877_ = lean_usize_dec_lt(v_i_874_, v_sz_873_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; 
v___x_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_878_, 0, v_b_875_);
return v___x_878_;
}
else
{
uint8_t v___x_879_; lean_object* v_a_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
lean_dec_ref(v_b_875_);
v___x_879_ = 0;
v_a_880_ = lean_array_uget_borrowed(v_as_872_, v_i_874_);
lean_inc(v_a_880_);
v___x_881_ = l_Lean_Message_toString(v_a_880_, v___x_879_);
v___x_882_ = l_IO_eprintln___at___00main_spec__6(v___x_881_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v___x_883_; size_t v___x_884_; size_t v___x_885_; 
lean_dec_ref_known(v___x_882_, 1);
v___x_883_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___closed__0));
v___x_884_ = ((size_t)1ULL);
v___x_885_ = lean_usize_add(v_i_874_, v___x_884_);
v_i_874_ = v___x_885_;
v_b_875_ = v___x_883_;
goto _start;
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
v_a_887_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_894_ == 0)
{
v___x_889_ = v___x_882_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_882_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_887_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___boxed(lean_object* v_as_895_, lean_object* v_sz_896_, lean_object* v_i_897_, lean_object* v_b_898_, lean_object* v___y_899_){
_start:
{
size_t v_sz_boxed_900_; size_t v_i_boxed_901_; lean_object* v_res_902_; 
v_sz_boxed_900_ = lean_unbox_usize(v_sz_896_);
lean_dec(v_sz_896_);
v_i_boxed_901_ = lean_unbox_usize(v_i_897_);
lean_dec(v_i_897_);
v_res_902_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27(v_as_895_, v_sz_boxed_900_, v_i_boxed_901_, v_b_898_);
lean_dec_ref(v_as_895_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(lean_object* v_as_903_, size_t v_sz_904_, size_t v_i_905_, lean_object* v_b_906_){
_start:
{
uint8_t v___x_908_; 
v___x_908_ = lean_usize_dec_lt(v_i_905_, v_sz_904_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; 
v___x_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_909_, 0, v_b_906_);
return v___x_909_;
}
else
{
uint8_t v___x_910_; lean_object* v_a_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
lean_dec_ref(v_b_906_);
v___x_910_ = 0;
v_a_911_ = lean_array_uget_borrowed(v_as_903_, v_i_905_);
lean_inc(v_a_911_);
v___x_912_ = l_Lean_Message_toString(v_a_911_, v___x_910_);
v___x_913_ = l_IO_eprintln___at___00main_spec__6(v___x_912_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v___x_914_; size_t v___x_915_; size_t v___x_916_; lean_object* v___x_917_; 
lean_dec_ref_known(v___x_913_, 1);
v___x_914_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___closed__0));
v___x_915_ = ((size_t)1ULL);
v___x_916_ = lean_usize_add(v_i_905_, v___x_915_);
v___x_917_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27(v_as_903_, v_sz_904_, v___x_916_, v___x_914_);
return v___x_917_;
}
else
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
v_a_918_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_913_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_913_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_918_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13___boxed(lean_object* v_as_926_, lean_object* v_sz_927_, lean_object* v_i_928_, lean_object* v_b_929_, lean_object* v___y_930_){
_start:
{
size_t v_sz_boxed_931_; size_t v_i_boxed_932_; lean_object* v_res_933_; 
v_sz_boxed_931_ = lean_unbox_usize(v_sz_927_);
lean_dec(v_sz_927_);
v_i_boxed_932_ = lean_unbox_usize(v_i_928_);
lean_dec(v_i_928_);
v_res_933_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_as_926_, v_sz_boxed_931_, v_i_boxed_932_, v_b_929_);
lean_dec_ref(v_as_926_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(lean_object* v_init_934_, lean_object* v_n_935_, lean_object* v_b_936_){
_start:
{
if (lean_obj_tag(v_n_935_) == 0)
{
lean_object* v_cs_938_; lean_object* v___x_939_; lean_object* v___x_940_; size_t v_sz_941_; size_t v___x_942_; lean_object* v___x_943_; 
v_cs_938_ = lean_ctor_get(v_n_935_, 0);
v___x_939_ = lean_box(0);
v___x_940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
lean_ctor_set(v___x_940_, 1, v_b_936_);
v_sz_941_ = lean_array_size(v_cs_938_);
v___x_942_ = ((size_t)0ULL);
v___x_943_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__12(v_init_934_, v_cs_938_, v_sz_941_, v___x_942_, v___x_940_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_958_; 
v_a_944_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_958_ == 0)
{
v___x_946_ = v___x_943_;
v_isShared_947_ = v_isSharedCheck_958_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_943_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_958_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v_fst_948_; 
v_fst_948_ = lean_ctor_get(v_a_944_, 0);
if (lean_obj_tag(v_fst_948_) == 0)
{
lean_object* v_snd_949_; lean_object* v___x_950_; lean_object* v___x_952_; 
v_snd_949_ = lean_ctor_get(v_a_944_, 1);
lean_inc(v_snd_949_);
lean_dec(v_a_944_);
v___x_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_950_, 0, v_snd_949_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 0, v___x_950_);
v___x_952_ = v___x_946_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_950_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
else
{
lean_object* v_val_954_; lean_object* v___x_956_; 
lean_inc_ref(v_fst_948_);
lean_dec(v_a_944_);
v_val_954_ = lean_ctor_get(v_fst_948_, 0);
lean_inc(v_val_954_);
lean_dec_ref_known(v_fst_948_, 1);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 0, v_val_954_);
v___x_956_ = v___x_946_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_val_954_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
else
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_966_; 
v_a_959_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_966_ == 0)
{
v___x_961_ = v___x_943_;
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_943_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_959_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
else
{
lean_object* v_vs_967_; lean_object* v___x_968_; lean_object* v___x_969_; size_t v_sz_970_; size_t v___x_971_; lean_object* v___x_972_; 
v_vs_967_ = lean_ctor_get(v_n_935_, 0);
v___x_968_ = lean_box(0);
v___x_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
lean_ctor_set(v___x_969_, 1, v_b_936_);
v_sz_970_ = lean_array_size(v_vs_967_);
v___x_971_ = ((size_t)0ULL);
v___x_972_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_vs_967_, v_sz_970_, v___x_971_, v___x_969_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_987_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_987_ == 0)
{
v___x_975_ = v___x_972_;
v_isShared_976_ = v_isSharedCheck_987_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_972_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_987_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v_fst_977_; 
v_fst_977_ = lean_ctor_get(v_a_973_, 0);
if (lean_obj_tag(v_fst_977_) == 0)
{
lean_object* v_snd_978_; lean_object* v___x_979_; lean_object* v___x_981_; 
v_snd_978_ = lean_ctor_get(v_a_973_, 1);
lean_inc(v_snd_978_);
lean_dec(v_a_973_);
v___x_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_979_, 0, v_snd_978_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v___x_979_);
v___x_981_ = v___x_975_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_979_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
else
{
lean_object* v_val_983_; lean_object* v___x_985_; 
lean_inc_ref(v_fst_977_);
lean_dec(v_a_973_);
v_val_983_ = lean_ctor_get(v_fst_977_, 0);
lean_inc(v_val_983_);
lean_dec_ref_known(v_fst_977_, 1);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v_val_983_);
v___x_985_ = v___x_975_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_val_983_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
v_a_988_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_972_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_972_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__12(lean_object* v_init_996_, lean_object* v_as_997_, size_t v_sz_998_, size_t v_i_999_, lean_object* v_b_1000_){
_start:
{
uint8_t v___x_1002_; 
v___x_1002_ = lean_usize_dec_lt(v_i_999_, v_sz_998_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1003_; 
v___x_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1003_, 0, v_b_1000_);
return v___x_1003_;
}
else
{
lean_object* v_snd_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1038_; 
v_snd_1004_ = lean_ctor_get(v_b_1000_, 1);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_b_1000_);
if (v_isSharedCheck_1038_ == 0)
{
lean_object* v_unused_1039_; 
v_unused_1039_ = lean_ctor_get(v_b_1000_, 0);
lean_dec(v_unused_1039_);
v___x_1006_ = v_b_1000_;
v_isShared_1007_ = v_isSharedCheck_1038_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_snd_1004_);
lean_dec(v_b_1000_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1038_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1008_; lean_object* v_a_1009_; lean_object* v___x_1010_; 
v___x_1008_ = lean_box(0);
v_a_1009_ = lean_array_uget_borrowed(v_as_997_, v_i_999_);
lean_inc(v_snd_1004_);
v___x_1010_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_996_, v_a_1009_, v_snd_1004_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1029_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1013_ = v___x_1010_;
v_isShared_1014_ = v_isSharedCheck_1029_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1010_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1029_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
if (lean_obj_tag(v_a_1011_) == 0)
{
lean_object* v___x_1015_; lean_object* v___x_1017_; 
v___x_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1015_, 0, v_a_1011_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v___x_1015_);
v___x_1017_ = v___x_1006_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v_snd_1004_);
v___x_1017_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1019_; 
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 0, v___x_1017_);
v___x_1019_ = v___x_1013_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1017_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; 
lean_del_object(v___x_1013_);
lean_dec(v_snd_1004_);
v_a_1022_ = lean_ctor_get(v_a_1011_, 0);
lean_inc(v_a_1022_);
lean_dec_ref_known(v_a_1011_, 1);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 1, v_a_1022_);
lean_ctor_set(v___x_1006_, 0, v___x_1008_);
v___x_1024_ = v___x_1006_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1008_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_a_1022_);
v___x_1024_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
size_t v___x_1025_; size_t v___x_1026_; 
v___x_1025_ = ((size_t)1ULL);
v___x_1026_ = lean_usize_add(v_i_999_, v___x_1025_);
v_i_999_ = v___x_1026_;
v_b_1000_ = v___x_1024_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
lean_del_object(v___x_1006_);
lean_dec(v_snd_1004_);
v_a_1030_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_1010_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1010_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1030_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__12___boxed(lean_object* v_init_1040_, lean_object* v_as_1041_, lean_object* v_sz_1042_, lean_object* v_i_1043_, lean_object* v_b_1044_, lean_object* v___y_1045_){
_start:
{
size_t v_sz_boxed_1046_; size_t v_i_boxed_1047_; lean_object* v_res_1048_; 
v_sz_boxed_1046_ = lean_unbox_usize(v_sz_1042_);
lean_dec(v_sz_1042_);
v_i_boxed_1047_ = lean_unbox_usize(v_i_1043_);
lean_dec(v_i_1043_);
v_res_1048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__12(v_init_1040_, v_as_1041_, v_sz_boxed_1046_, v_i_boxed_1047_, v_b_1044_);
lean_dec_ref(v_as_1041_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10___boxed(lean_object* v_init_1049_, lean_object* v_n_1050_, lean_object* v_b_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_1049_, v_n_1050_, v_b_1051_);
lean_dec_ref(v_n_1050_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15(lean_object* v_as_1057_, size_t v_sz_1058_, size_t v_i_1059_, lean_object* v_b_1060_){
_start:
{
uint8_t v___x_1062_; 
v___x_1062_ = lean_usize_dec_lt(v_i_1059_, v_sz_1058_);
if (v___x_1062_ == 0)
{
lean_object* v___x_1063_; 
v___x_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1063_, 0, v_b_1060_);
return v___x_1063_;
}
else
{
uint8_t v___x_1064_; lean_object* v_a_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
lean_dec_ref(v_b_1060_);
v___x_1064_ = 0;
v_a_1065_ = lean_array_uget_borrowed(v_as_1057_, v_i_1059_);
lean_inc(v_a_1065_);
v___x_1066_ = l_Lean_Message_toString(v_a_1065_, v___x_1064_);
v___x_1067_ = l_IO_eprintln___at___00main_spec__6(v___x_1066_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v___x_1068_; size_t v___x_1069_; size_t v___x_1070_; 
lean_dec_ref_known(v___x_1067_, 1);
v___x_1068_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___closed__0));
v___x_1069_ = ((size_t)1ULL);
v___x_1070_ = lean_usize_add(v_i_1059_, v___x_1069_);
v_i_1059_ = v___x_1070_;
v_b_1060_ = v___x_1068_;
goto _start;
}
else
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
v_a_1072_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1074_ = v___x_1067_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1067_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1072_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___boxed(lean_object* v_as_1080_, lean_object* v_sz_1081_, lean_object* v_i_1082_, lean_object* v_b_1083_, lean_object* v___y_1084_){
_start:
{
size_t v_sz_boxed_1085_; size_t v_i_boxed_1086_; lean_object* v_res_1087_; 
v_sz_boxed_1085_ = lean_unbox_usize(v_sz_1081_);
lean_dec(v_sz_1081_);
v_i_boxed_1086_ = lean_unbox_usize(v_i_1082_);
lean_dec(v_i_1082_);
v_res_1087_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15(v_as_1080_, v_sz_boxed_1085_, v_i_boxed_1086_, v_b_1083_);
lean_dec_ref(v_as_1080_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(lean_object* v_as_1088_, size_t v_sz_1089_, size_t v_i_1090_, lean_object* v_b_1091_){
_start:
{
uint8_t v___x_1093_; 
v___x_1093_ = lean_usize_dec_lt(v_i_1090_, v_sz_1089_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; 
v___x_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1094_, 0, v_b_1091_);
return v___x_1094_;
}
else
{
uint8_t v___x_1095_; lean_object* v_a_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
lean_dec_ref(v_b_1091_);
v___x_1095_ = 0;
v_a_1096_ = lean_array_uget_borrowed(v_as_1088_, v_i_1090_);
lean_inc(v_a_1096_);
v___x_1097_ = l_Lean_Message_toString(v_a_1096_, v___x_1095_);
v___x_1098_ = l_IO_eprintln___at___00main_spec__6(v___x_1097_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v___x_1099_; size_t v___x_1100_; size_t v___x_1101_; lean_object* v___x_1102_; 
lean_dec_ref_known(v___x_1098_, 1);
v___x_1099_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___closed__0));
v___x_1100_ = ((size_t)1ULL);
v___x_1101_ = lean_usize_add(v_i_1090_, v___x_1100_);
v___x_1102_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15(v_as_1088_, v_sz_1089_, v___x_1101_, v___x_1099_);
return v___x_1102_;
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
v_a_1103_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1098_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1098_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11___boxed(lean_object* v_as_1111_, lean_object* v_sz_1112_, lean_object* v_i_1113_, lean_object* v_b_1114_, lean_object* v___y_1115_){
_start:
{
size_t v_sz_boxed_1116_; size_t v_i_boxed_1117_; lean_object* v_res_1118_; 
v_sz_boxed_1116_ = lean_unbox_usize(v_sz_1112_);
lean_dec(v_sz_1112_);
v_i_boxed_1117_ = lean_unbox_usize(v_i_1113_);
lean_dec(v_i_1113_);
v_res_1118_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_as_1111_, v_sz_boxed_1116_, v_i_boxed_1117_, v_b_1114_);
lean_dec_ref(v_as_1111_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7(lean_object* v_t_1119_, lean_object* v_init_1120_){
_start:
{
lean_object* v_root_1122_; lean_object* v_tail_1123_; lean_object* v___x_1124_; 
v_root_1122_ = lean_ctor_get(v_t_1119_, 0);
v_tail_1123_ = lean_ctor_get(v_t_1119_, 1);
v___x_1124_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_1120_, v_root_1122_, v_init_1120_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1161_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1127_ = v___x_1124_;
v_isShared_1128_ = v_isSharedCheck_1161_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1124_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1161_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
if (lean_obj_tag(v_a_1125_) == 0)
{
lean_object* v_a_1129_; lean_object* v___x_1131_; 
v_a_1129_ = lean_ctor_get(v_a_1125_, 0);
lean_inc(v_a_1129_);
lean_dec_ref_known(v_a_1125_, 1);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v_a_1129_);
v___x_1131_ = v___x_1127_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1129_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; size_t v_sz_1136_; size_t v___x_1137_; lean_object* v___x_1138_; 
lean_del_object(v___x_1127_);
v_a_1133_ = lean_ctor_get(v_a_1125_, 0);
lean_inc(v_a_1133_);
lean_dec_ref_known(v_a_1125_, 1);
v___x_1134_ = lean_box(0);
v___x_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
lean_ctor_set(v___x_1135_, 1, v_a_1133_);
v_sz_1136_ = lean_array_size(v_tail_1123_);
v___x_1137_ = ((size_t)0ULL);
v___x_1138_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_tail_1123_, v_sz_1136_, v___x_1137_, v___x_1135_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1152_; 
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1141_ = v___x_1138_;
v_isShared_1142_ = v_isSharedCheck_1152_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1138_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1152_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v_fst_1143_; 
v_fst_1143_ = lean_ctor_get(v_a_1139_, 0);
if (lean_obj_tag(v_fst_1143_) == 0)
{
lean_object* v_snd_1144_; lean_object* v___x_1146_; 
v_snd_1144_ = lean_ctor_get(v_a_1139_, 1);
lean_inc(v_snd_1144_);
lean_dec(v_a_1139_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 0, v_snd_1144_);
v___x_1146_ = v___x_1141_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_snd_1144_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
else
{
lean_object* v_val_1148_; lean_object* v___x_1150_; 
lean_inc_ref(v_fst_1143_);
lean_dec(v_a_1139_);
v_val_1148_ = lean_ctor_get(v_fst_1143_, 0);
lean_inc(v_val_1148_);
lean_dec_ref_known(v_fst_1143_, 1);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 0, v_val_1148_);
v___x_1150_ = v___x_1141_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_val_1148_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
v_a_1153_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1138_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1138_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
}
}
else
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1169_; 
v_a_1162_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1164_ = v___x_1124_;
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1124_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1165_ == 0)
{
v___x_1167_ = v___x_1164_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1162_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7___boxed(lean_object* v_t_1170_, lean_object* v_init_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_t_1170_, v_init_1171_);
lean_dec_ref(v_t_1170_);
return v_res_1173_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0(uint8_t v_suppressElabErrors_1181_, uint8_t v___y_1182_, lean_object* v_x_1183_){
_start:
{
if (lean_obj_tag(v_x_1183_) == 1)
{
lean_object* v_pre_1184_; 
v_pre_1184_ = lean_ctor_get(v_x_1183_, 0);
switch(lean_obj_tag(v_pre_1184_))
{
case 1:
{
lean_object* v_pre_1185_; 
v_pre_1185_ = lean_ctor_get(v_pre_1184_, 0);
switch(lean_obj_tag(v_pre_1185_))
{
case 0:
{
lean_object* v_str_1186_; lean_object* v_str_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; 
v_str_1186_ = lean_ctor_get(v_x_1183_, 1);
v_str_1187_ = lean_ctor_get(v_pre_1184_, 1);
v___x_1188_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__0));
v___x_1189_ = lean_string_dec_eq(v_str_1187_, v___x_1188_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; uint8_t v___x_1191_; 
v___x_1190_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__1));
v___x_1191_ = lean_string_dec_eq(v_str_1187_, v___x_1190_);
if (v___x_1191_ == 0)
{
return v___x_1191_;
}
else
{
lean_object* v___x_1192_; uint8_t v___x_1193_; 
v___x_1192_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__2));
v___x_1193_ = lean_string_dec_eq(v_str_1186_, v___x_1192_);
if (v___x_1193_ == 0)
{
return v___x_1193_;
}
else
{
return v_suppressElabErrors_1181_;
}
}
}
else
{
lean_object* v___x_1194_; uint8_t v___x_1195_; 
v___x_1194_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__3));
v___x_1195_ = lean_string_dec_eq(v_str_1186_, v___x_1194_);
if (v___x_1195_ == 0)
{
return v___x_1195_;
}
else
{
return v_suppressElabErrors_1181_;
}
}
}
case 1:
{
lean_object* v_pre_1196_; 
v_pre_1196_ = lean_ctor_get(v_pre_1185_, 0);
if (lean_obj_tag(v_pre_1196_) == 0)
{
lean_object* v_str_1197_; lean_object* v_str_1198_; lean_object* v_str_1199_; lean_object* v___x_1200_; uint8_t v___x_1201_; 
v_str_1197_ = lean_ctor_get(v_x_1183_, 1);
v_str_1198_ = lean_ctor_get(v_pre_1184_, 1);
v_str_1199_ = lean_ctor_get(v_pre_1185_, 1);
v___x_1200_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__4));
v___x_1201_ = lean_string_dec_eq(v_str_1199_, v___x_1200_);
if (v___x_1201_ == 0)
{
return v___x_1201_;
}
else
{
lean_object* v___x_1202_; uint8_t v___x_1203_; 
v___x_1202_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__5));
v___x_1203_ = lean_string_dec_eq(v_str_1198_, v___x_1202_);
if (v___x_1203_ == 0)
{
return v___x_1203_;
}
else
{
lean_object* v___x_1204_; uint8_t v___x_1205_; 
v___x_1204_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__6));
v___x_1205_ = lean_string_dec_eq(v_str_1197_, v___x_1204_);
if (v___x_1205_ == 0)
{
return v___x_1205_;
}
else
{
return v_suppressElabErrors_1181_;
}
}
}
}
else
{
return v___y_1182_;
}
}
default: 
{
return v___y_1182_;
}
}
}
case 0:
{
lean_object* v_str_1206_; lean_object* v___x_1207_; uint8_t v___x_1208_; 
v_str_1206_ = lean_ctor_get(v_x_1183_, 1);
v___x_1207_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_1208_ = lean_string_dec_eq(v_str_1206_, v___x_1207_);
if (v___x_1208_ == 0)
{
return v___x_1208_;
}
else
{
return v_suppressElabErrors_1181_;
}
}
default: 
{
return v___y_1182_;
}
}
}
else
{
return v___y_1182_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___boxed(lean_object* v_suppressElabErrors_1209_, lean_object* v___y_1210_, lean_object* v_x_1211_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1212_; uint8_t v___y_37651__boxed_1213_; uint8_t v_res_1214_; lean_object* v_r_1215_; 
v_suppressElabErrors_boxed_1212_ = lean_unbox(v_suppressElabErrors_1209_);
v___y_37651__boxed_1213_ = lean_unbox(v___y_1210_);
v_res_1214_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0(v_suppressElabErrors_boxed_1212_, v___y_37651__boxed_1213_, v_x_1211_);
lean_dec(v_x_1211_);
v_r_1215_ = lean_box(v_res_1214_);
return v_r_1215_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(lean_object* v_opts_1216_, lean_object* v_opt_1217_){
_start:
{
lean_object* v_name_1218_; lean_object* v_defValue_1219_; lean_object* v_map_1220_; lean_object* v___x_1221_; 
v_name_1218_ = lean_ctor_get(v_opt_1217_, 0);
v_defValue_1219_ = lean_ctor_get(v_opt_1217_, 1);
v_map_1220_ = lean_ctor_get(v_opts_1216_, 0);
v___x_1221_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1220_, v_name_1218_);
if (lean_obj_tag(v___x_1221_) == 0)
{
uint8_t v___x_1222_; 
v___x_1222_ = lean_unbox(v_defValue_1219_);
return v___x_1222_;
}
else
{
lean_object* v_val_1223_; 
v_val_1223_ = lean_ctor_get(v___x_1221_, 0);
lean_inc(v_val_1223_);
lean_dec_ref_known(v___x_1221_, 1);
if (lean_obj_tag(v_val_1223_) == 1)
{
uint8_t v_v_1224_; 
v_v_1224_ = lean_ctor_get_uint8(v_val_1223_, 0);
lean_dec_ref_known(v_val_1223_, 0);
return v_v_1224_;
}
else
{
uint8_t v___x_1225_; 
lean_dec(v_val_1223_);
v___x_1225_ = lean_unbox(v_defValue_1219_);
return v___x_1225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___boxed(lean_object* v_opts_1226_, lean_object* v_opt_1227_){
_start:
{
uint8_t v_res_1228_; lean_object* v_r_1229_; 
v_res_1228_ = l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(v_opts_1226_, v_opt_1227_);
lean_dec_ref(v_opt_1227_);
lean_dec_ref(v_opts_1226_);
v_r_1229_ = lean_box(v_res_1228_);
return v_r_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44(lean_object* v_ref_1231_, lean_object* v_msgData_1232_, uint8_t v_severity_1233_, uint8_t v_isSilent_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v___y_1239_; lean_object* v___y_1240_; uint8_t v___y_1241_; uint8_t v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v_toCold_1246_; lean_object* v___y_1247_; lean_object* v___y_1276_; lean_object* v___y_1277_; uint8_t v___y_1278_; uint8_t v___y_1279_; lean_object* v___y_1280_; uint8_t v___y_1281_; lean_object* v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1303_; uint8_t v___y_1304_; lean_object* v___y_1305_; uint8_t v___y_1306_; uint8_t v___y_1307_; lean_object* v___y_1308_; lean_object* v___y_1309_; uint8_t v___y_1313_; uint8_t v___y_1314_; uint8_t v___y_1315_; uint8_t v___x_1326_; uint8_t v___y_1328_; uint8_t v___y_1329_; uint8_t v___y_1330_; uint8_t v___y_1332_; uint8_t v___x_1340_; 
v___x_1326_ = 2;
v___x_1340_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1233_, v___x_1326_);
if (v___x_1340_ == 0)
{
v___y_1332_ = v___x_1340_;
goto v___jp_1331_;
}
else
{
uint8_t v___x_1341_; 
lean_inc_ref(v_msgData_1232_);
v___x_1341_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1232_);
v___y_1332_ = v___x_1341_;
goto v___jp_1331_;
}
v___jp_1238_:
{
lean_object* v_currNamespace_1248_; lean_object* v_openDecls_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v_env_1254_; lean_object* v_nextMacroScope_1255_; lean_object* v_ngen_1256_; lean_object* v_auxDeclNGen_1257_; lean_object* v_traceState_1258_; lean_object* v_cache_1259_; lean_object* v_recordedDeps_1260_; lean_object* v_messages_1261_; lean_object* v_infoState_1262_; lean_object* v_snapshotTasks_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1274_; 
v_currNamespace_1248_ = lean_ctor_get(v_toCold_1246_, 4);
v_openDecls_1249_ = lean_ctor_get(v_toCold_1246_, 5);
lean_inc(v_openDecls_1249_);
lean_inc(v_currNamespace_1248_);
v___x_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1250_, 0, v_currNamespace_1248_);
lean_ctor_set(v___x_1250_, 1, v_openDecls_1249_);
v___x_1251_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
lean_ctor_set(v___x_1251_, 1, v___y_1245_);
lean_inc_ref(v___y_1240_);
lean_inc_ref(v___y_1243_);
v___x_1252_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1252_, 0, v___y_1243_);
lean_ctor_set(v___x_1252_, 1, v___y_1239_);
lean_ctor_set(v___x_1252_, 2, v___y_1244_);
lean_ctor_set(v___x_1252_, 3, v___y_1240_);
lean_ctor_set(v___x_1252_, 4, v___x_1251_);
lean_ctor_set_uint8(v___x_1252_, sizeof(void*)*5, v___y_1242_);
lean_ctor_set_uint8(v___x_1252_, sizeof(void*)*5 + 1, v___y_1241_);
lean_ctor_set_uint8(v___x_1252_, sizeof(void*)*5 + 2, v_isSilent_1234_);
v___x_1253_ = lean_st_ref_take(v___y_1247_);
v_env_1254_ = lean_ctor_get(v___x_1253_, 0);
v_nextMacroScope_1255_ = lean_ctor_get(v___x_1253_, 1);
v_ngen_1256_ = lean_ctor_get(v___x_1253_, 2);
v_auxDeclNGen_1257_ = lean_ctor_get(v___x_1253_, 3);
v_traceState_1258_ = lean_ctor_get(v___x_1253_, 4);
v_cache_1259_ = lean_ctor_get(v___x_1253_, 5);
v_recordedDeps_1260_ = lean_ctor_get(v___x_1253_, 6);
v_messages_1261_ = lean_ctor_get(v___x_1253_, 7);
v_infoState_1262_ = lean_ctor_get(v___x_1253_, 8);
v_snapshotTasks_1263_ = lean_ctor_get(v___x_1253_, 9);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1265_ = v___x_1253_;
v_isShared_1266_ = v_isSharedCheck_1274_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_snapshotTasks_1263_);
lean_inc(v_infoState_1262_);
lean_inc(v_messages_1261_);
lean_inc(v_recordedDeps_1260_);
lean_inc(v_cache_1259_);
lean_inc(v_traceState_1258_);
lean_inc(v_auxDeclNGen_1257_);
lean_inc(v_ngen_1256_);
lean_inc(v_nextMacroScope_1255_);
lean_inc(v_env_1254_);
lean_dec(v___x_1253_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1274_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1270_; 
v___x_1267_ = lean_box(0);
v___x_1268_ = l_Lean_MessageLog_add(v___x_1252_, v_messages_1261_);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 7, v___x_1268_);
v___x_1270_ = v___x_1265_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_env_1254_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_nextMacroScope_1255_);
lean_ctor_set(v_reuseFailAlloc_1273_, 2, v_ngen_1256_);
lean_ctor_set(v_reuseFailAlloc_1273_, 3, v_auxDeclNGen_1257_);
lean_ctor_set(v_reuseFailAlloc_1273_, 4, v_traceState_1258_);
lean_ctor_set(v_reuseFailAlloc_1273_, 5, v_cache_1259_);
lean_ctor_set(v_reuseFailAlloc_1273_, 6, v_recordedDeps_1260_);
lean_ctor_set(v_reuseFailAlloc_1273_, 7, v___x_1268_);
lean_ctor_set(v_reuseFailAlloc_1273_, 8, v_infoState_1262_);
lean_ctor_set(v_reuseFailAlloc_1273_, 9, v_snapshotTasks_1263_);
v___x_1270_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = lean_st_ref_put(v___y_1247_, v___x_1270_);
v___x_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1267_);
return v___x_1272_;
}
}
}
v___jp_1275_:
{
lean_object* v_fileName_1284_; lean_object* v_fileMap_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1301_; 
v_fileName_1284_ = lean_ctor_get(v___y_1280_, 0);
v_fileMap_1285_ = lean_ctor_get(v___y_1280_, 1);
v___x_1286_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1232_);
v___x_1287_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(v___x_1286_, v___y_1235_, v___y_1236_);
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1290_ = v___x_1287_;
v_isShared_1291_ = v_isSharedCheck_1301_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1287_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1301_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
lean_inc_ref_n(v_fileMap_1285_, 2);
v___x_1292_ = l_Lean_FileMap_toPosition(v_fileMap_1285_, v___y_1282_);
lean_dec(v___y_1282_);
v___x_1293_ = l_Lean_FileMap_toPosition(v_fileMap_1285_, v___y_1283_);
lean_dec(v___y_1283_);
v___x_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
v___x_1295_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___closed__0));
if (v___y_1279_ == 0)
{
lean_del_object(v___x_1290_);
lean_dec_ref(v___y_1277_);
v___y_1239_ = v___x_1292_;
v___y_1240_ = v___x_1295_;
v___y_1241_ = v___y_1278_;
v___y_1242_ = v___y_1281_;
v___y_1243_ = v_fileName_1284_;
v___y_1244_ = v___x_1294_;
v___y_1245_ = v_a_1288_;
v_toCold_1246_ = v___y_1276_;
v___y_1247_ = v___y_1236_;
goto v___jp_1238_;
}
else
{
uint8_t v___x_1296_; 
lean_inc(v_a_1288_);
v___x_1296_ = l_Lean_MessageData_hasTag(v___y_1277_, v_a_1288_);
if (v___x_1296_ == 0)
{
lean_object* v___x_1297_; lean_object* v___x_1299_; 
lean_dec_ref_known(v___x_1294_, 1);
lean_dec_ref(v___x_1292_);
lean_dec(v_a_1288_);
v___x_1297_ = lean_box(0);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 0, v___x_1297_);
v___x_1299_ = v___x_1290_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v___x_1297_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
else
{
lean_del_object(v___x_1290_);
v___y_1239_ = v___x_1292_;
v___y_1240_ = v___x_1295_;
v___y_1241_ = v___y_1278_;
v___y_1242_ = v___y_1281_;
v___y_1243_ = v_fileName_1284_;
v___y_1244_ = v___x_1294_;
v___y_1245_ = v_a_1288_;
v_toCold_1246_ = v___y_1276_;
v___y_1247_ = v___y_1236_;
goto v___jp_1238_;
}
}
}
}
v___jp_1302_:
{
lean_object* v___x_1310_; 
v___x_1310_ = l_Lean_Syntax_getTailPos_x3f(v___y_1308_, v___y_1307_);
lean_dec(v___y_1308_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_inc(v___y_1309_);
v___y_1276_ = v___y_1303_;
v___y_1277_ = v___y_1305_;
v___y_1278_ = v___y_1306_;
v___y_1279_ = v___y_1304_;
v___y_1280_ = v___y_1303_;
v___y_1281_ = v___y_1307_;
v___y_1282_ = v___y_1309_;
v___y_1283_ = v___y_1309_;
goto v___jp_1275_;
}
else
{
lean_object* v_val_1311_; 
v_val_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_val_1311_);
lean_dec_ref_known(v___x_1310_, 1);
v___y_1276_ = v___y_1303_;
v___y_1277_ = v___y_1305_;
v___y_1278_ = v___y_1306_;
v___y_1279_ = v___y_1304_;
v___y_1280_ = v___y_1303_;
v___y_1281_ = v___y_1307_;
v___y_1282_ = v___y_1309_;
v___y_1283_ = v_val_1311_;
goto v___jp_1275_;
}
}
v___jp_1312_:
{
lean_object* v_toCold_1316_; lean_object* v_ref_1317_; uint8_t v_suppressElabErrors_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___f_1321_; lean_object* v_ref_1322_; lean_object* v___x_1323_; 
v_toCold_1316_ = lean_ctor_get(v___y_1235_, 0);
v_ref_1317_ = lean_ctor_get(v___y_1235_, 2);
v_suppressElabErrors_1318_ = lean_ctor_get_uint8(v___y_1235_, sizeof(void*)*3 + 2);
v___x_1319_ = lean_box(v_suppressElabErrors_1318_);
v___x_1320_ = lean_box(v___y_1313_);
v___f_1321_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1321_, 0, v___x_1319_);
lean_closure_set(v___f_1321_, 1, v___x_1320_);
v_ref_1322_ = l_Lean_replaceRef(v_ref_1231_, v_ref_1317_);
v___x_1323_ = l_Lean_Syntax_getPos_x3f(v_ref_1322_, v___y_1314_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v___x_1324_; 
v___x_1324_ = lean_unsigned_to_nat(0u);
v___y_1303_ = v_toCold_1316_;
v___y_1304_ = v_suppressElabErrors_1318_;
v___y_1305_ = v___f_1321_;
v___y_1306_ = v___y_1315_;
v___y_1307_ = v___y_1314_;
v___y_1308_ = v_ref_1322_;
v___y_1309_ = v___x_1324_;
goto v___jp_1302_;
}
else
{
lean_object* v_val_1325_; 
v_val_1325_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_val_1325_);
lean_dec_ref_known(v___x_1323_, 1);
v___y_1303_ = v_toCold_1316_;
v___y_1304_ = v_suppressElabErrors_1318_;
v___y_1305_ = v___f_1321_;
v___y_1306_ = v___y_1315_;
v___y_1307_ = v___y_1314_;
v___y_1308_ = v_ref_1322_;
v___y_1309_ = v_val_1325_;
goto v___jp_1302_;
}
}
v___jp_1327_:
{
if (v___y_1330_ == 0)
{
v___y_1313_ = v___y_1328_;
v___y_1314_ = v___y_1329_;
v___y_1315_ = v_severity_1233_;
goto v___jp_1312_;
}
else
{
v___y_1313_ = v___y_1328_;
v___y_1314_ = v___y_1329_;
v___y_1315_ = v___x_1326_;
goto v___jp_1312_;
}
}
v___jp_1331_:
{
if (v___y_1332_ == 0)
{
uint8_t v___x_1333_; uint8_t v___x_1334_; 
v___x_1333_ = 1;
v___x_1334_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1233_, v___x_1333_);
if (v___x_1334_ == 0)
{
v___y_1328_ = v___y_1332_;
v___y_1329_ = v___y_1332_;
v___y_1330_ = v___x_1334_;
goto v___jp_1327_;
}
else
{
lean_object* v___x_1335_; lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1335_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1235_);
v___x_1336_ = l_Lean_warningAsError;
v___x_1337_ = l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(v___x_1335_, v___x_1336_);
lean_dec_ref(v___x_1335_);
v___y_1328_ = v___y_1332_;
v___y_1329_ = v___y_1332_;
v___y_1330_ = v___x_1337_;
goto v___jp_1327_;
}
}
else
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
lean_dec_ref(v_msgData_1232_);
v___x_1338_ = lean_box(0);
v___x_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1338_);
return v___x_1339_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___boxed(lean_object* v_ref_1342_, lean_object* v_msgData_1343_, lean_object* v_severity_1344_, lean_object* v_isSilent_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
uint8_t v_severity_boxed_1349_; uint8_t v_isSilent_boxed_1350_; lean_object* v_res_1351_; 
v_severity_boxed_1349_ = lean_unbox(v_severity_1344_);
v_isSilent_boxed_1350_ = lean_unbox(v_isSilent_1345_);
v_res_1351_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44(v_ref_1342_, v_msgData_1343_, v_severity_boxed_1349_, v_isSilent_boxed_1350_, v___y_1346_, v___y_1347_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v_ref_1342_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30(lean_object* v_msgData_1352_, uint8_t v_severity_1353_, uint8_t v_isSilent_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v_ref_1358_; lean_object* v___x_1359_; 
v_ref_1358_ = lean_ctor_get(v___y_1355_, 2);
v___x_1359_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44(v_ref_1358_, v_msgData_1352_, v_severity_1353_, v_isSilent_1354_, v___y_1355_, v___y_1356_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30___boxed(lean_object* v_msgData_1360_, lean_object* v_severity_1361_, lean_object* v_isSilent_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
uint8_t v_severity_boxed_1366_; uint8_t v_isSilent_boxed_1367_; lean_object* v_res_1368_; 
v_severity_boxed_1366_ = lean_unbox(v_severity_1361_);
v_isSilent_boxed_1367_ = lean_unbox(v_isSilent_1362_);
v_res_1368_ = l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30(v_msgData_1360_, v_severity_boxed_1366_, v_isSilent_boxed_1367_, v___y_1363_, v___y_1364_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__13(lean_object* v_msgData_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
uint8_t v___x_1373_; uint8_t v___x_1374_; lean_object* v___x_1375_; 
v___x_1373_ = 2;
v___x_1374_ = 0;
v___x_1375_ = l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30(v_msgData_1369_, v___x_1373_, v___x_1374_, v___y_1370_, v___y_1371_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__13___boxed(lean_object* v_msgData_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_Lean_logError___at___00main_spec__13(v_msgData_1376_, v___y_1377_, v___y_1378_);
lean_dec(v___y_1378_);
lean_dec_ref(v___y_1377_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14(lean_object* v_opts_1381_, lean_object* v_opt_1382_){
_start:
{
lean_object* v_name_1383_; lean_object* v_map_1384_; lean_object* v___x_1385_; 
v_name_1383_ = lean_ctor_get(v_opt_1382_, 0);
v_map_1384_ = lean_ctor_get(v_opts_1381_, 0);
v___x_1385_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1384_, v_name_1383_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v___x_1386_; 
v___x_1386_ = lean_box(0);
return v___x_1386_;
}
else
{
lean_object* v_val_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1396_; 
v_val_1387_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1389_ = v___x_1385_;
v_isShared_1390_ = v_isSharedCheck_1396_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_val_1387_);
lean_dec(v___x_1385_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1396_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
if (lean_obj_tag(v_val_1387_) == 0)
{
lean_object* v_v_1391_; lean_object* v___x_1393_; 
v_v_1391_ = lean_ctor_get(v_val_1387_, 0);
lean_inc_ref(v_v_1391_);
lean_dec_ref_known(v_val_1387_, 1);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v_v_1391_);
v___x_1393_ = v___x_1389_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_v_1391_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
else
{
lean_object* v___x_1395_; 
lean_del_object(v___x_1389_);
lean_dec(v_val_1387_);
v___x_1395_ = lean_box(0);
return v___x_1395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___boxed(lean_object* v_opts_1397_, lean_object* v_opt_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14(v_opts_1397_, v_opt_1398_);
lean_dec_ref(v_opt_1398_);
lean_dec_ref(v_opts_1397_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22(lean_object* v_x_1400_, lean_object* v_x_1401_){
_start:
{
if (lean_obj_tag(v_x_1401_) == 0)
{
return v_x_1400_;
}
else
{
lean_object* v_key_1402_; lean_object* v_value_1403_; lean_object* v_tail_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v_key_1402_ = lean_ctor_get(v_x_1401_, 0);
v_value_1403_ = lean_ctor_get(v_x_1401_, 1);
v_tail_1404_ = lean_ctor_get(v_x_1401_, 2);
lean_inc(v_value_1403_);
lean_inc(v_key_1402_);
v___x_1405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1405_, 0, v_key_1402_);
lean_ctor_set(v___x_1405_, 1, v_value_1403_);
v___x_1406_ = lean_array_push(v_x_1400_, v___x_1405_);
v_x_1400_ = v___x_1406_;
v_x_1401_ = v_tail_1404_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22___boxed(lean_object* v_x_1408_, lean_object* v_x_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22(v_x_1408_, v_x_1409_);
lean_dec(v_x_1409_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__23(lean_object* v_as_1411_, size_t v_i_1412_, size_t v_stop_1413_, lean_object* v_b_1414_){
_start:
{
uint8_t v___x_1415_; 
v___x_1415_ = lean_usize_dec_eq(v_i_1412_, v_stop_1413_);
if (v___x_1415_ == 0)
{
lean_object* v___x_1416_; lean_object* v___x_1417_; size_t v___x_1418_; size_t v___x_1419_; 
v___x_1416_ = lean_array_uget_borrowed(v_as_1411_, v_i_1412_);
v___x_1417_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22(v_b_1414_, v___x_1416_);
v___x_1418_ = ((size_t)1ULL);
v___x_1419_ = lean_usize_add(v_i_1412_, v___x_1418_);
v_i_1412_ = v___x_1419_;
v_b_1414_ = v___x_1417_;
goto _start;
}
else
{
return v_b_1414_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__23___boxed(lean_object* v_as_1421_, lean_object* v_i_1422_, lean_object* v_stop_1423_, lean_object* v_b_1424_){
_start:
{
size_t v_i_boxed_1425_; size_t v_stop_boxed_1426_; lean_object* v_res_1427_; 
v_i_boxed_1425_ = lean_unbox_usize(v_i_1422_);
lean_dec(v_i_1422_);
v_stop_boxed_1426_ = lean_unbox_usize(v_stop_1423_);
lean_dec(v_stop_1423_);
v_res_1427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__23(v_as_1421_, v_i_boxed_1425_, v_stop_boxed_1426_, v_b_1424_);
lean_dec_ref(v_as_1421_);
return v_res_1427_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(lean_object* v_x_1428_, lean_object* v_x_1429_){
_start:
{
lean_object* v_fst_1430_; lean_object* v_fst_1431_; lean_object* v_fst_1432_; lean_object* v_fst_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; 
v_fst_1430_ = lean_ctor_get(v_x_1428_, 0);
v_fst_1431_ = lean_ctor_get(v_x_1429_, 0);
v_fst_1432_ = lean_ctor_get(v_fst_1430_, 0);
v_fst_1433_ = lean_ctor_get(v_fst_1431_, 0);
v___x_1434_ = lean_unsigned_to_nat(1u);
v___x_1435_ = lean_nat_add(v_fst_1432_, v___x_1434_);
v___x_1436_ = lean_nat_dec_le(v___x_1435_, v_fst_1433_);
lean_dec(v___x_1435_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0___boxed(lean_object* v_x_1437_, lean_object* v_x_1438_){
_start:
{
uint8_t v_res_1439_; lean_object* v_r_1440_; 
v_res_1439_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(v_x_1437_, v_x_1438_);
lean_dec_ref(v_x_1438_);
lean_dec_ref(v_x_1437_);
v_r_1440_ = lean_box(v_res_1439_);
return v_r_1440_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg(lean_object* v_hi_1441_, lean_object* v_pivot_1442_, lean_object* v_as_1443_, lean_object* v_i_1444_, lean_object* v_k_1445_){
_start:
{
uint8_t v___x_1446_; 
v___x_1446_ = lean_nat_dec_lt(v_k_1445_, v_hi_1441_);
if (v___x_1446_ == 0)
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
lean_dec(v_k_1445_);
v___x_1447_ = lean_array_fswap(v_as_1443_, v_i_1444_, v_hi_1441_);
v___x_1448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1448_, 0, v_i_1444_);
lean_ctor_set(v___x_1448_, 1, v___x_1447_);
return v___x_1448_;
}
else
{
lean_object* v___x_1449_; lean_object* v_fst_1450_; lean_object* v_fst_1451_; lean_object* v_fst_1452_; lean_object* v_fst_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; uint8_t v___x_1456_; 
v___x_1449_ = lean_array_fget_borrowed(v_as_1443_, v_k_1445_);
v_fst_1450_ = lean_ctor_get(v___x_1449_, 0);
v_fst_1451_ = lean_ctor_get(v_pivot_1442_, 0);
v_fst_1452_ = lean_ctor_get(v_fst_1450_, 0);
v_fst_1453_ = lean_ctor_get(v_fst_1451_, 0);
v___x_1454_ = lean_unsigned_to_nat(1u);
v___x_1455_ = lean_nat_add(v_fst_1452_, v___x_1454_);
v___x_1456_ = lean_nat_dec_le(v___x_1455_, v_fst_1453_);
lean_dec(v___x_1455_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1457_; 
v___x_1457_ = lean_nat_add(v_k_1445_, v___x_1454_);
lean_dec(v_k_1445_);
v_k_1445_ = v___x_1457_;
goto _start;
}
else
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1459_ = lean_array_fswap(v_as_1443_, v_i_1444_, v_k_1445_);
v___x_1460_ = lean_nat_add(v_i_1444_, v___x_1454_);
lean_dec(v_i_1444_);
v___x_1461_ = lean_nat_add(v_k_1445_, v___x_1454_);
lean_dec(v_k_1445_);
v_as_1443_ = v___x_1459_;
v_i_1444_ = v___x_1460_;
v_k_1445_ = v___x_1461_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg___boxed(lean_object* v_hi_1463_, lean_object* v_pivot_1464_, lean_object* v_as_1465_, lean_object* v_i_1466_, lean_object* v_k_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg(v_hi_1463_, v_pivot_1464_, v_as_1465_, v_i_1466_, v_k_1467_);
lean_dec_ref(v_pivot_1464_);
lean_dec(v_hi_1463_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(lean_object* v_n_1469_, lean_object* v_as_1470_, lean_object* v_lo_1471_, lean_object* v_hi_1472_){
_start:
{
lean_object* v___y_1474_; uint8_t v___x_1484_; 
v___x_1484_ = lean_nat_dec_lt(v_lo_1471_, v_hi_1472_);
if (v___x_1484_ == 0)
{
lean_dec(v_lo_1471_);
return v_as_1470_;
}
else
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v_mid_1487_; lean_object* v___y_1489_; lean_object* v___y_1495_; lean_object* v___x_1500_; lean_object* v___x_1501_; uint8_t v___x_1502_; 
v___x_1485_ = lean_nat_add(v_lo_1471_, v_hi_1472_);
v___x_1486_ = lean_unsigned_to_nat(1u);
v_mid_1487_ = lean_nat_shiftr(v___x_1485_, v___x_1486_);
lean_dec(v___x_1485_);
v___x_1500_ = lean_array_fget_borrowed(v_as_1470_, v_mid_1487_);
v___x_1501_ = lean_array_fget_borrowed(v_as_1470_, v_lo_1471_);
v___x_1502_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(v___x_1500_, v___x_1501_);
if (v___x_1502_ == 0)
{
v___y_1495_ = v_as_1470_;
goto v___jp_1494_;
}
else
{
lean_object* v___x_1503_; 
v___x_1503_ = lean_array_fswap(v_as_1470_, v_lo_1471_, v_mid_1487_);
v___y_1495_ = v___x_1503_;
goto v___jp_1494_;
}
v___jp_1488_:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; uint8_t v___x_1492_; 
v___x_1490_ = lean_array_fget_borrowed(v___y_1489_, v_mid_1487_);
v___x_1491_ = lean_array_fget_borrowed(v___y_1489_, v_hi_1472_);
v___x_1492_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(v___x_1490_, v___x_1491_);
if (v___x_1492_ == 0)
{
lean_dec(v_mid_1487_);
v___y_1474_ = v___y_1489_;
goto v___jp_1473_;
}
else
{
lean_object* v___x_1493_; 
v___x_1493_ = lean_array_fswap(v___y_1489_, v_mid_1487_, v_hi_1472_);
lean_dec(v_mid_1487_);
v___y_1474_ = v___x_1493_;
goto v___jp_1473_;
}
}
v___jp_1494_:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; uint8_t v___x_1498_; 
v___x_1496_ = lean_array_fget_borrowed(v___y_1495_, v_hi_1472_);
v___x_1497_ = lean_array_fget_borrowed(v___y_1495_, v_lo_1471_);
v___x_1498_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(v___x_1496_, v___x_1497_);
if (v___x_1498_ == 0)
{
v___y_1489_ = v___y_1495_;
goto v___jp_1488_;
}
else
{
lean_object* v___x_1499_; 
v___x_1499_ = lean_array_fswap(v___y_1495_, v_lo_1471_, v_hi_1472_);
v___y_1489_ = v___x_1499_;
goto v___jp_1488_;
}
}
}
v___jp_1473_:
{
lean_object* v_pivot_1475_; lean_object* v___x_1476_; lean_object* v_fst_1477_; lean_object* v_snd_1478_; uint8_t v___x_1479_; 
v_pivot_1475_ = lean_array_fget(v___y_1474_, v_hi_1472_);
lean_inc_n(v_lo_1471_, 2);
v___x_1476_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg(v_hi_1472_, v_pivot_1475_, v___y_1474_, v_lo_1471_, v_lo_1471_);
lean_dec(v_pivot_1475_);
v_fst_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_fst_1477_);
v_snd_1478_ = lean_ctor_get(v___x_1476_, 1);
lean_inc(v_snd_1478_);
lean_dec_ref(v___x_1476_);
v___x_1479_ = lean_nat_dec_le(v_hi_1472_, v_fst_1477_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1480_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(v_n_1469_, v_snd_1478_, v_lo_1471_, v_fst_1477_);
v___x_1481_ = lean_unsigned_to_nat(1u);
v___x_1482_ = lean_nat_add(v_fst_1477_, v___x_1481_);
lean_dec(v_fst_1477_);
v_as_1470_ = v___x_1480_;
v_lo_1471_ = v___x_1482_;
goto _start;
}
else
{
lean_dec(v_fst_1477_);
lean_dec(v_lo_1471_);
return v_snd_1478_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___boxed(lean_object* v_n_1504_, lean_object* v_as_1505_, lean_object* v_lo_1506_, lean_object* v_hi_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(v_n_1504_, v_as_1505_, v_lo_1506_, v_hi_1507_);
lean_dec(v_hi_1507_);
lean_dec(v_n_1504_);
return v_res_1508_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0(uint8_t v_suppressElabErrors_1509_, uint8_t v___x_1510_, lean_object* v___x_1511_, lean_object* v_x_1512_){
_start:
{
if (lean_obj_tag(v_x_1512_) == 1)
{
lean_object* v_pre_1513_; 
v_pre_1513_ = lean_ctor_get(v_x_1512_, 0);
switch(lean_obj_tag(v_pre_1513_))
{
case 1:
{
lean_object* v_pre_1514_; 
v_pre_1514_ = lean_ctor_get(v_pre_1513_, 0);
switch(lean_obj_tag(v_pre_1514_))
{
case 0:
{
lean_object* v_str_1515_; lean_object* v_str_1516_; lean_object* v___x_1517_; uint8_t v___x_1518_; 
v_str_1515_ = lean_ctor_get(v_x_1512_, 1);
v_str_1516_ = lean_ctor_get(v_pre_1513_, 1);
v___x_1517_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__0));
v___x_1518_ = lean_string_dec_eq(v_str_1516_, v___x_1517_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; uint8_t v___x_1520_; 
v___x_1519_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__1));
v___x_1520_ = lean_string_dec_eq(v_str_1516_, v___x_1519_);
if (v___x_1520_ == 0)
{
return v___x_1520_;
}
else
{
lean_object* v___x_1521_; uint8_t v___x_1522_; 
v___x_1521_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__2));
v___x_1522_ = lean_string_dec_eq(v_str_1515_, v___x_1521_);
if (v___x_1522_ == 0)
{
return v___x_1522_;
}
else
{
return v_suppressElabErrors_1509_;
}
}
}
else
{
lean_object* v___x_1523_; uint8_t v___x_1524_; 
v___x_1523_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__3));
v___x_1524_ = lean_string_dec_eq(v_str_1515_, v___x_1523_);
if (v___x_1524_ == 0)
{
return v___x_1524_;
}
else
{
return v_suppressElabErrors_1509_;
}
}
}
case 1:
{
lean_object* v_pre_1525_; 
v_pre_1525_ = lean_ctor_get(v_pre_1514_, 0);
if (lean_obj_tag(v_pre_1525_) == 0)
{
lean_object* v_str_1526_; lean_object* v_str_1527_; lean_object* v_str_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; 
v_str_1526_ = lean_ctor_get(v_x_1512_, 1);
v_str_1527_ = lean_ctor_get(v_pre_1513_, 1);
v_str_1528_ = lean_ctor_get(v_pre_1514_, 1);
v___x_1529_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__4));
v___x_1530_ = lean_string_dec_eq(v_str_1528_, v___x_1529_);
if (v___x_1530_ == 0)
{
return v___x_1530_;
}
else
{
lean_object* v___x_1531_; uint8_t v___x_1532_; 
v___x_1531_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__5));
v___x_1532_ = lean_string_dec_eq(v_str_1527_, v___x_1531_);
if (v___x_1532_ == 0)
{
return v___x_1532_;
}
else
{
lean_object* v___x_1533_; uint8_t v___x_1534_; 
v___x_1533_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__6));
v___x_1534_ = lean_string_dec_eq(v_str_1526_, v___x_1533_);
if (v___x_1534_ == 0)
{
return v___x_1534_;
}
else
{
return v_suppressElabErrors_1509_;
}
}
}
}
else
{
return v___x_1510_;
}
}
default: 
{
return v___x_1510_;
}
}
}
case 0:
{
lean_object* v_str_1535_; uint8_t v___x_1536_; 
v_str_1535_ = lean_ctor_get(v_x_1512_, 1);
v___x_1536_ = lean_string_dec_eq(v_str_1535_, v___x_1511_);
if (v___x_1536_ == 0)
{
return v___x_1536_;
}
else
{
return v_suppressElabErrors_1509_;
}
}
default: 
{
return v___x_1510_;
}
}
}
else
{
return v___x_1510_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0___boxed(lean_object* v_suppressElabErrors_1537_, lean_object* v___x_1538_, lean_object* v___x_1539_, lean_object* v_x_1540_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1541_; uint8_t v___x_38115__boxed_1542_; uint8_t v_res_1543_; lean_object* v_r_1544_; 
v_suppressElabErrors_boxed_1541_ = lean_unbox(v_suppressElabErrors_1537_);
v___x_38115__boxed_1542_ = lean_unbox(v___x_1538_);
v_res_1543_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0(v_suppressElabErrors_boxed_1541_, v___x_38115__boxed_1542_, v___x_1539_, v_x_1540_);
lean_dec(v_x_1540_);
lean_dec_ref(v___x_1539_);
v_r_1544_ = lean_box(v_res_1543_);
return v_r_1544_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0(void){
_start:
{
lean_object* v___x_1545_; double v___x_1546_; 
v___x_1545_ = lean_unsigned_to_nat(0u);
v___x_1546_ = lean_float_of_nat(v___x_1545_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20(uint8_t v___x_1547_, lean_object* v_as_1548_, size_t v_sz_1549_, size_t v_i_1550_, lean_object* v_b_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v_a_1556_; uint8_t v___x_1560_; 
v___x_1560_ = lean_usize_dec_lt(v_i_1550_, v_sz_1549_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1561_; 
v___x_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1561_, 0, v_b_1551_);
return v___x_1561_;
}
else
{
lean_object* v_a_1562_; lean_object* v_fst_1563_; lean_object* v_snd_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1643_; 
v_a_1562_ = lean_array_uget(v_as_1548_, v_i_1550_);
v_fst_1563_ = lean_ctor_get(v_a_1562_, 0);
v_snd_1564_ = lean_ctor_get(v_a_1562_, 1);
v_isSharedCheck_1643_ = !lean_is_exclusive(v_a_1562_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1566_ = v_a_1562_;
v_isShared_1567_ = v_isSharedCheck_1643_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_snd_1564_);
lean_inc(v_fst_1563_);
lean_dec(v_a_1562_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1643_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v_fst_1568_; lean_object* v_snd_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1642_; 
v_fst_1568_ = lean_ctor_get(v_fst_1563_, 0);
v_snd_1569_ = lean_ctor_get(v_fst_1563_, 1);
v_isSharedCheck_1642_ = !lean_is_exclusive(v_fst_1563_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1571_ = v_fst_1563_;
v_isShared_1572_ = v_isSharedCheck_1642_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_snd_1569_);
lean_inc(v_fst_1568_);
lean_dec(v_fst_1563_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1642_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; double v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v_toCold_1578_; uint8_t v_suppressElabErrors_1579_; lean_object* v_fileName_1580_; lean_object* v_fileMap_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1588_; 
v___x_1573_ = lean_box(0);
v___x_1574_ = lean_box(0);
v___x_1575_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0);
v___x_1576_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___closed__0));
v___x_1577_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1577_, 0, v___x_1573_);
lean_ctor_set(v___x_1577_, 1, v___x_1574_);
lean_ctor_set(v___x_1577_, 2, v___x_1576_);
lean_ctor_set_float(v___x_1577_, sizeof(void*)*3, v___x_1575_);
lean_ctor_set_float(v___x_1577_, sizeof(void*)*3 + 8, v___x_1575_);
lean_ctor_set_uint8(v___x_1577_, sizeof(void*)*3 + 16, v___x_1560_);
v_toCold_1578_ = lean_ctor_get(v___y_1552_, 0);
v_suppressElabErrors_1579_ = lean_ctor_get_uint8(v___y_1552_, sizeof(void*)*3 + 2);
v_fileName_1580_ = lean_ctor_get(v_toCold_1578_, 0);
v_fileMap_1581_ = lean_ctor_get(v_toCold_1578_, 1);
v___x_1582_ = lean_box(0);
v___x_1583_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_1584_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_1585_ = l_Lean_MessageData_nil;
v___x_1586_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1577_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
lean_ctor_set(v___x_1586_, 2, v_snd_1564_);
if (v_isShared_1572_ == 0)
{
lean_ctor_set_tag(v___x_1571_, 8);
lean_ctor_set(v___x_1571_, 1, v___x_1586_);
lean_ctor_set(v___x_1571_, 0, v___x_1584_);
v___x_1588_ = v___x_1571_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v___x_1584_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v___x_1586_);
v___x_1588_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
uint8_t v___x_1589_; lean_object* v___x_1590_; lean_object* v___y_1592_; lean_object* v___y_1593_; 
v___x_1589_ = 0;
lean_inc_ref(v_fileMap_1581_);
lean_inc_ref(v_fileName_1580_);
v___x_1590_ = l_Lean_Elab_mkMessageCore(v_fileName_1580_, v_fileMap_1581_, v___x_1588_, v___x_1589_, v_fst_1568_, v_snd_1569_);
lean_dec(v_snd_1569_);
lean_dec(v_fst_1568_);
if (v_suppressElabErrors_1579_ == 0)
{
v___y_1592_ = v___y_1552_;
v___y_1593_ = v___y_1553_;
goto v___jp_1591_;
}
else
{
lean_object* v_data_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___f_1639_; uint8_t v___x_1640_; 
v_data_1636_ = lean_ctor_get(v___x_1590_, 4);
v___x_1637_ = lean_box(v_suppressElabErrors_1579_);
v___x_1638_ = lean_box(v___x_1547_);
v___f_1639_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1639_, 0, v___x_1637_);
lean_closure_set(v___f_1639_, 1, v___x_1638_);
lean_closure_set(v___f_1639_, 2, v___x_1583_);
lean_inc(v_data_1636_);
v___x_1640_ = l_Lean_MessageData_hasTag(v___f_1639_, v_data_1636_);
if (v___x_1640_ == 0)
{
lean_dec_ref(v___x_1590_);
lean_del_object(v___x_1566_);
v_a_1556_ = v___x_1582_;
goto v___jp_1555_;
}
else
{
v___y_1592_ = v___y_1552_;
v___y_1593_ = v___y_1553_;
goto v___jp_1591_;
}
}
v___jp_1591_:
{
lean_object* v_toCold_1594_; lean_object* v_fileName_1595_; lean_object* v_pos_1596_; lean_object* v_endPos_1597_; uint8_t v_keepFullRange_1598_; uint8_t v_severity_1599_; uint8_t v_isSilent_1600_; lean_object* v_caption_1601_; lean_object* v_data_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1635_; 
v_toCold_1594_ = lean_ctor_get(v___y_1592_, 0);
v_fileName_1595_ = lean_ctor_get(v___x_1590_, 0);
v_pos_1596_ = lean_ctor_get(v___x_1590_, 1);
v_endPos_1597_ = lean_ctor_get(v___x_1590_, 2);
v_keepFullRange_1598_ = lean_ctor_get_uint8(v___x_1590_, sizeof(void*)*5);
v_severity_1599_ = lean_ctor_get_uint8(v___x_1590_, sizeof(void*)*5 + 1);
v_isSilent_1600_ = lean_ctor_get_uint8(v___x_1590_, sizeof(void*)*5 + 2);
v_caption_1601_ = lean_ctor_get(v___x_1590_, 3);
v_data_1602_ = lean_ctor_get(v___x_1590_, 4);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1604_ = v___x_1590_;
v_isShared_1605_ = v_isSharedCheck_1635_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_data_1602_);
lean_inc(v_caption_1601_);
lean_inc(v_endPos_1597_);
lean_inc(v_pos_1596_);
lean_inc(v_fileName_1595_);
lean_dec(v___x_1590_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1635_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v_currNamespace_1606_; lean_object* v_openDecls_1607_; lean_object* v___x_1609_; 
v_currNamespace_1606_ = lean_ctor_get(v_toCold_1594_, 4);
v_openDecls_1607_ = lean_ctor_get(v_toCold_1594_, 5);
lean_inc(v_openDecls_1607_);
lean_inc(v_currNamespace_1606_);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 1, v_openDecls_1607_);
lean_ctor_set(v___x_1566_, 0, v_currNamespace_1606_);
v___x_1609_ = v___x_1566_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_currNamespace_1606_);
lean_ctor_set(v_reuseFailAlloc_1634_, 1, v_openDecls_1607_);
v___x_1609_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
lean_object* v___x_1610_; lean_object* v___x_1612_; 
v___x_1610_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
lean_ctor_set(v___x_1610_, 1, v_data_1602_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 4, v___x_1610_);
v___x_1612_ = v___x_1604_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_fileName_1595_);
lean_ctor_set(v_reuseFailAlloc_1633_, 1, v_pos_1596_);
lean_ctor_set(v_reuseFailAlloc_1633_, 2, v_endPos_1597_);
lean_ctor_set(v_reuseFailAlloc_1633_, 3, v_caption_1601_);
lean_ctor_set(v_reuseFailAlloc_1633_, 4, v___x_1610_);
lean_ctor_set_uint8(v_reuseFailAlloc_1633_, sizeof(void*)*5, v_keepFullRange_1598_);
lean_ctor_set_uint8(v_reuseFailAlloc_1633_, sizeof(void*)*5 + 1, v_severity_1599_);
lean_ctor_set_uint8(v_reuseFailAlloc_1633_, sizeof(void*)*5 + 2, v_isSilent_1600_);
v___x_1612_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
lean_object* v___x_1613_; lean_object* v_env_1614_; lean_object* v_nextMacroScope_1615_; lean_object* v_ngen_1616_; lean_object* v_auxDeclNGen_1617_; lean_object* v_traceState_1618_; lean_object* v_cache_1619_; lean_object* v_recordedDeps_1620_; lean_object* v_messages_1621_; lean_object* v_infoState_1622_; lean_object* v_snapshotTasks_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1632_; 
v___x_1613_ = lean_st_ref_take(v___y_1593_);
v_env_1614_ = lean_ctor_get(v___x_1613_, 0);
v_nextMacroScope_1615_ = lean_ctor_get(v___x_1613_, 1);
v_ngen_1616_ = lean_ctor_get(v___x_1613_, 2);
v_auxDeclNGen_1617_ = lean_ctor_get(v___x_1613_, 3);
v_traceState_1618_ = lean_ctor_get(v___x_1613_, 4);
v_cache_1619_ = lean_ctor_get(v___x_1613_, 5);
v_recordedDeps_1620_ = lean_ctor_get(v___x_1613_, 6);
v_messages_1621_ = lean_ctor_get(v___x_1613_, 7);
v_infoState_1622_ = lean_ctor_get(v___x_1613_, 8);
v_snapshotTasks_1623_ = lean_ctor_get(v___x_1613_, 9);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1625_ = v___x_1613_;
v_isShared_1626_ = v_isSharedCheck_1632_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_snapshotTasks_1623_);
lean_inc(v_infoState_1622_);
lean_inc(v_messages_1621_);
lean_inc(v_recordedDeps_1620_);
lean_inc(v_cache_1619_);
lean_inc(v_traceState_1618_);
lean_inc(v_auxDeclNGen_1617_);
lean_inc(v_ngen_1616_);
lean_inc(v_nextMacroScope_1615_);
lean_inc(v_env_1614_);
lean_dec(v___x_1613_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1632_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1627_; lean_object* v___x_1629_; 
v___x_1627_ = l_Lean_MessageLog_add(v___x_1612_, v_messages_1621_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 7, v___x_1627_);
v___x_1629_ = v___x_1625_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_env_1614_);
lean_ctor_set(v_reuseFailAlloc_1631_, 1, v_nextMacroScope_1615_);
lean_ctor_set(v_reuseFailAlloc_1631_, 2, v_ngen_1616_);
lean_ctor_set(v_reuseFailAlloc_1631_, 3, v_auxDeclNGen_1617_);
lean_ctor_set(v_reuseFailAlloc_1631_, 4, v_traceState_1618_);
lean_ctor_set(v_reuseFailAlloc_1631_, 5, v_cache_1619_);
lean_ctor_set(v_reuseFailAlloc_1631_, 6, v_recordedDeps_1620_);
lean_ctor_set(v_reuseFailAlloc_1631_, 7, v___x_1627_);
lean_ctor_set(v_reuseFailAlloc_1631_, 8, v_infoState_1622_);
lean_ctor_set(v_reuseFailAlloc_1631_, 9, v_snapshotTasks_1623_);
v___x_1629_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
lean_object* v___x_1630_; 
v___x_1630_ = lean_st_ref_put(v___y_1593_, v___x_1629_);
v_a_1556_ = v___x_1582_;
goto v___jp_1555_;
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
v___jp_1555_:
{
size_t v___x_1557_; size_t v___x_1558_; 
v___x_1557_ = ((size_t)1ULL);
v___x_1558_ = lean_usize_add(v_i_1550_, v___x_1557_);
v_i_1550_ = v___x_1558_;
v_b_1551_ = v_a_1556_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___boxed(lean_object* v___x_1644_, lean_object* v_as_1645_, lean_object* v_sz_1646_, lean_object* v_i_1647_, lean_object* v_b_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
uint8_t v___x_38180__boxed_1652_; size_t v_sz_boxed_1653_; size_t v_i_boxed_1654_; lean_object* v_res_1655_; 
v___x_38180__boxed_1652_ = lean_unbox(v___x_1644_);
v_sz_boxed_1653_ = lean_unbox_usize(v_sz_1646_);
lean_dec(v_sz_1646_);
v_i_boxed_1654_ = lean_unbox_usize(v_i_1647_);
lean_dec(v_i_1647_);
v_res_1655_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20(v___x_38180__boxed_1652_, v_as_1645_, v_sz_boxed_1653_, v_i_boxed_1654_, v_b_1648_, v___y_1649_, v___y_1650_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec_ref(v_as_1645_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg(lean_object* v_a_1656_, lean_object* v_fallback_1657_, lean_object* v_x_1658_){
_start:
{
if (lean_obj_tag(v_x_1658_) == 0)
{
lean_inc(v_fallback_1657_);
return v_fallback_1657_;
}
else
{
lean_object* v_key_1659_; lean_object* v_value_1660_; lean_object* v_tail_1661_; lean_object* v_fst_1662_; lean_object* v_snd_1663_; lean_object* v_fst_1664_; lean_object* v_snd_1665_; uint8_t v_decide_1666_; 
v_key_1659_ = lean_ctor_get(v_x_1658_, 0);
v_value_1660_ = lean_ctor_get(v_x_1658_, 1);
v_tail_1661_ = lean_ctor_get(v_x_1658_, 2);
v_fst_1662_ = lean_ctor_get(v_key_1659_, 0);
v_snd_1663_ = lean_ctor_get(v_key_1659_, 1);
v_fst_1664_ = lean_ctor_get(v_a_1656_, 0);
v_snd_1665_ = lean_ctor_get(v_a_1656_, 1);
v_decide_1666_ = lean_nat_dec_eq(v_fst_1662_, v_fst_1664_);
if (v_decide_1666_ == 0)
{
v_x_1658_ = v_tail_1661_;
goto _start;
}
else
{
uint8_t v_decide_1668_; 
v_decide_1668_ = lean_nat_dec_eq(v_snd_1663_, v_snd_1665_);
if (v_decide_1668_ == 0)
{
v_x_1658_ = v_tail_1661_;
goto _start;
}
else
{
lean_inc(v_value_1660_);
return v_value_1660_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg___boxed(lean_object* v_a_1670_, lean_object* v_fallback_1671_, lean_object* v_x_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg(v_a_1670_, v_fallback_1671_, v_x_1672_);
lean_dec(v_x_1672_);
lean_dec(v_fallback_1671_);
lean_dec_ref(v_a_1670_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(lean_object* v_m_1674_, lean_object* v_a_1675_, lean_object* v_fallback_1676_){
_start:
{
lean_object* v_buckets_1677_; lean_object* v_fst_1678_; lean_object* v_snd_1679_; lean_object* v___x_1680_; uint64_t v___x_1681_; uint64_t v___x_1682_; uint64_t v___x_1683_; uint64_t v___x_1684_; uint64_t v___x_1685_; uint64_t v_fold_1686_; uint64_t v___x_1687_; uint64_t v___x_1688_; uint64_t v___x_1689_; size_t v___x_1690_; size_t v___x_1691_; size_t v___x_1692_; size_t v___x_1693_; size_t v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v_buckets_1677_ = lean_ctor_get(v_m_1674_, 1);
v_fst_1678_ = lean_ctor_get(v_a_1675_, 0);
v_snd_1679_ = lean_ctor_get(v_a_1675_, 1);
v___x_1680_ = lean_array_get_size(v_buckets_1677_);
v___x_1681_ = l_String_instHashableRaw_hash(v_fst_1678_);
v___x_1682_ = l_String_instHashableRaw_hash(v_snd_1679_);
v___x_1683_ = lean_uint64_mix_hash(v___x_1681_, v___x_1682_);
v___x_1684_ = 32ULL;
v___x_1685_ = lean_uint64_shift_right(v___x_1683_, v___x_1684_);
v_fold_1686_ = lean_uint64_xor(v___x_1683_, v___x_1685_);
v___x_1687_ = 16ULL;
v___x_1688_ = lean_uint64_shift_right(v_fold_1686_, v___x_1687_);
v___x_1689_ = lean_uint64_xor(v_fold_1686_, v___x_1688_);
v___x_1690_ = lean_uint64_to_usize(v___x_1689_);
v___x_1691_ = lean_usize_of_nat(v___x_1680_);
v___x_1692_ = ((size_t)1ULL);
v___x_1693_ = lean_usize_sub(v___x_1691_, v___x_1692_);
v___x_1694_ = lean_usize_land(v___x_1690_, v___x_1693_);
v___x_1695_ = lean_array_uget_borrowed(v_buckets_1677_, v___x_1694_);
v___x_1696_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg(v_a_1675_, v_fallback_1676_, v___x_1695_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg___boxed(lean_object* v_m_1697_, lean_object* v_a_1698_, lean_object* v_fallback_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_m_1697_, v_a_1698_, v_fallback_1699_);
lean_dec(v_fallback_1699_);
lean_dec_ref(v_a_1698_);
lean_dec_ref(v_m_1697_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35_spec__44___redArg(lean_object* v_x_1701_, lean_object* v_x_1702_){
_start:
{
if (lean_obj_tag(v_x_1702_) == 0)
{
return v_x_1701_;
}
else
{
lean_object* v_key_1703_; lean_object* v_value_1704_; lean_object* v_tail_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1732_; 
v_key_1703_ = lean_ctor_get(v_x_1702_, 0);
v_value_1704_ = lean_ctor_get(v_x_1702_, 1);
v_tail_1705_ = lean_ctor_get(v_x_1702_, 2);
v_isSharedCheck_1732_ = !lean_is_exclusive(v_x_1702_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1707_ = v_x_1702_;
v_isShared_1708_ = v_isSharedCheck_1732_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_tail_1705_);
lean_inc(v_value_1704_);
lean_inc(v_key_1703_);
lean_dec(v_x_1702_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1732_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v_fst_1709_; lean_object* v_snd_1710_; lean_object* v___x_1711_; uint64_t v___x_1712_; uint64_t v___x_1713_; uint64_t v___x_1714_; uint64_t v___x_1715_; uint64_t v___x_1716_; uint64_t v_fold_1717_; uint64_t v___x_1718_; uint64_t v___x_1719_; uint64_t v___x_1720_; size_t v___x_1721_; size_t v___x_1722_; size_t v___x_1723_; size_t v___x_1724_; size_t v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1728_; 
v_fst_1709_ = lean_ctor_get(v_key_1703_, 0);
v_snd_1710_ = lean_ctor_get(v_key_1703_, 1);
v___x_1711_ = lean_array_get_size(v_x_1701_);
v___x_1712_ = l_String_instHashableRaw_hash(v_fst_1709_);
v___x_1713_ = l_String_instHashableRaw_hash(v_snd_1710_);
v___x_1714_ = lean_uint64_mix_hash(v___x_1712_, v___x_1713_);
v___x_1715_ = 32ULL;
v___x_1716_ = lean_uint64_shift_right(v___x_1714_, v___x_1715_);
v_fold_1717_ = lean_uint64_xor(v___x_1714_, v___x_1716_);
v___x_1718_ = 16ULL;
v___x_1719_ = lean_uint64_shift_right(v_fold_1717_, v___x_1718_);
v___x_1720_ = lean_uint64_xor(v_fold_1717_, v___x_1719_);
v___x_1721_ = lean_uint64_to_usize(v___x_1720_);
v___x_1722_ = lean_usize_of_nat(v___x_1711_);
v___x_1723_ = ((size_t)1ULL);
v___x_1724_ = lean_usize_sub(v___x_1722_, v___x_1723_);
v___x_1725_ = lean_usize_land(v___x_1721_, v___x_1724_);
v___x_1726_ = lean_array_uget_borrowed(v_x_1701_, v___x_1725_);
lean_inc(v___x_1726_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 2, v___x_1726_);
v___x_1728_ = v___x_1707_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_key_1703_);
lean_ctor_set(v_reuseFailAlloc_1731_, 1, v_value_1704_);
lean_ctor_set(v_reuseFailAlloc_1731_, 2, v___x_1726_);
v___x_1728_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
lean_object* v___x_1729_; 
v___x_1729_ = lean_array_uset(v_x_1701_, v___x_1725_, v___x_1728_);
v_x_1701_ = v___x_1729_;
v_x_1702_ = v_tail_1705_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35___redArg(lean_object* v_i_1733_, lean_object* v_source_1734_, lean_object* v_target_1735_){
_start:
{
lean_object* v___x_1736_; uint8_t v___x_1737_; 
v___x_1736_ = lean_array_get_size(v_source_1734_);
v___x_1737_ = lean_nat_dec_lt(v_i_1733_, v___x_1736_);
if (v___x_1737_ == 0)
{
lean_dec_ref(v_source_1734_);
lean_dec(v_i_1733_);
return v_target_1735_;
}
else
{
lean_object* v_es_1738_; lean_object* v___x_1739_; lean_object* v_source_1740_; lean_object* v_target_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v_es_1738_ = lean_array_fget(v_source_1734_, v_i_1733_);
v___x_1739_ = lean_box(0);
v_source_1740_ = lean_array_fset(v_source_1734_, v_i_1733_, v___x_1739_);
v_target_1741_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35_spec__44___redArg(v_target_1735_, v_es_1738_);
v___x_1742_ = lean_unsigned_to_nat(1u);
v___x_1743_ = lean_nat_add(v_i_1733_, v___x_1742_);
lean_dec(v_i_1733_);
v_i_1733_ = v___x_1743_;
v_source_1734_ = v_source_1740_;
v_target_1735_ = v_target_1741_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24___redArg(lean_object* v_data_1745_){
_start:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v_nbuckets_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1746_ = lean_array_get_size(v_data_1745_);
v___x_1747_ = lean_unsigned_to_nat(2u);
v_nbuckets_1748_ = lean_nat_mul(v___x_1746_, v___x_1747_);
v___x_1749_ = lean_unsigned_to_nat(0u);
v___x_1750_ = lean_box(0);
v___x_1751_ = lean_mk_array(v_nbuckets_1748_, v___x_1750_);
v___x_1752_ = lean_array_propagate_mark(v_data_1745_, v___x_1751_);
v___x_1753_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35___redArg(v___x_1749_, v_data_1745_, v___x_1752_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25___redArg(lean_object* v_a_1754_, lean_object* v_b_1755_, lean_object* v_x_1756_){
_start:
{
if (lean_obj_tag(v_x_1756_) == 0)
{
lean_dec(v_b_1755_);
lean_dec_ref(v_a_1754_);
return v_x_1756_;
}
else
{
lean_object* v_key_1757_; lean_object* v_value_1758_; lean_object* v_tail_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1775_; 
v_key_1757_ = lean_ctor_get(v_x_1756_, 0);
v_value_1758_ = lean_ctor_get(v_x_1756_, 1);
v_tail_1759_ = lean_ctor_get(v_x_1756_, 2);
v_isSharedCheck_1775_ = !lean_is_exclusive(v_x_1756_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1761_ = v_x_1756_;
v_isShared_1762_ = v_isSharedCheck_1775_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_tail_1759_);
lean_inc(v_value_1758_);
lean_inc(v_key_1757_);
lean_dec(v_x_1756_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1775_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v_fst_1768_; lean_object* v_snd_1769_; lean_object* v_fst_1770_; lean_object* v_snd_1771_; uint8_t v_decide_1772_; 
v_fst_1768_ = lean_ctor_get(v_key_1757_, 0);
v_snd_1769_ = lean_ctor_get(v_key_1757_, 1);
v_fst_1770_ = lean_ctor_get(v_a_1754_, 0);
v_snd_1771_ = lean_ctor_get(v_a_1754_, 1);
v_decide_1772_ = lean_nat_dec_eq(v_fst_1768_, v_fst_1770_);
if (v_decide_1772_ == 0)
{
goto v___jp_1763_;
}
else
{
uint8_t v_decide_1773_; 
v_decide_1773_ = lean_nat_dec_eq(v_snd_1769_, v_snd_1771_);
if (v_decide_1773_ == 0)
{
goto v___jp_1763_;
}
else
{
lean_object* v___x_1774_; 
lean_del_object(v___x_1761_);
lean_dec(v_value_1758_);
lean_dec(v_key_1757_);
v___x_1774_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1774_, 0, v_a_1754_);
lean_ctor_set(v___x_1774_, 1, v_b_1755_);
lean_ctor_set(v___x_1774_, 2, v_tail_1759_);
return v___x_1774_;
}
}
v___jp_1763_:
{
lean_object* v___x_1764_; lean_object* v___x_1766_; 
v___x_1764_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25___redArg(v_a_1754_, v_b_1755_, v_tail_1759_);
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 2, v___x_1764_);
v___x_1766_ = v___x_1761_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_key_1757_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v_value_1758_);
lean_ctor_set(v_reuseFailAlloc_1767_, 2, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg(lean_object* v_a_1776_, lean_object* v_x_1777_){
_start:
{
if (lean_obj_tag(v_x_1777_) == 0)
{
uint8_t v___x_1778_; 
v___x_1778_ = 0;
return v___x_1778_;
}
else
{
lean_object* v_key_1779_; lean_object* v_tail_1780_; lean_object* v_fst_1781_; lean_object* v_snd_1782_; lean_object* v_fst_1783_; lean_object* v_snd_1784_; uint8_t v_decide_1785_; 
v_key_1779_ = lean_ctor_get(v_x_1777_, 0);
v_tail_1780_ = lean_ctor_get(v_x_1777_, 2);
v_fst_1781_ = lean_ctor_get(v_key_1779_, 0);
v_snd_1782_ = lean_ctor_get(v_key_1779_, 1);
v_fst_1783_ = lean_ctor_get(v_a_1776_, 0);
v_snd_1784_ = lean_ctor_get(v_a_1776_, 1);
v_decide_1785_ = lean_nat_dec_eq(v_fst_1781_, v_fst_1783_);
if (v_decide_1785_ == 0)
{
v_x_1777_ = v_tail_1780_;
goto _start;
}
else
{
uint8_t v_decide_1787_; 
v_decide_1787_ = lean_nat_dec_eq(v_snd_1782_, v_snd_1784_);
if (v_decide_1787_ == 0)
{
v_x_1777_ = v_tail_1780_;
goto _start;
}
else
{
return v_decide_1787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg___boxed(lean_object* v_a_1789_, lean_object* v_x_1790_){
_start:
{
uint8_t v_res_1791_; lean_object* v_r_1792_; 
v_res_1791_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg(v_a_1789_, v_x_1790_);
lean_dec(v_x_1790_);
lean_dec_ref(v_a_1789_);
v_r_1792_ = lean_box(v_res_1791_);
return v_r_1792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(lean_object* v_m_1793_, lean_object* v_a_1794_, lean_object* v_b_1795_){
_start:
{
lean_object* v_size_1796_; lean_object* v_buckets_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1844_; 
v_size_1796_ = lean_ctor_get(v_m_1793_, 0);
v_buckets_1797_ = lean_ctor_get(v_m_1793_, 1);
v_isSharedCheck_1844_ = !lean_is_exclusive(v_m_1793_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1799_ = v_m_1793_;
v_isShared_1800_ = v_isSharedCheck_1844_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_buckets_1797_);
lean_inc(v_size_1796_);
lean_dec(v_m_1793_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1844_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v_fst_1801_; lean_object* v_snd_1802_; lean_object* v___x_1803_; uint64_t v___x_1804_; uint64_t v___x_1805_; uint64_t v___x_1806_; uint64_t v___x_1807_; uint64_t v___x_1808_; uint64_t v_fold_1809_; uint64_t v___x_1810_; uint64_t v___x_1811_; uint64_t v___x_1812_; size_t v___x_1813_; size_t v___x_1814_; size_t v___x_1815_; size_t v___x_1816_; size_t v___x_1817_; lean_object* v_bkt_1818_; uint8_t v___x_1819_; 
v_fst_1801_ = lean_ctor_get(v_a_1794_, 0);
v_snd_1802_ = lean_ctor_get(v_a_1794_, 1);
v___x_1803_ = lean_array_get_size(v_buckets_1797_);
v___x_1804_ = l_String_instHashableRaw_hash(v_fst_1801_);
v___x_1805_ = l_String_instHashableRaw_hash(v_snd_1802_);
v___x_1806_ = lean_uint64_mix_hash(v___x_1804_, v___x_1805_);
v___x_1807_ = 32ULL;
v___x_1808_ = lean_uint64_shift_right(v___x_1806_, v___x_1807_);
v_fold_1809_ = lean_uint64_xor(v___x_1806_, v___x_1808_);
v___x_1810_ = 16ULL;
v___x_1811_ = lean_uint64_shift_right(v_fold_1809_, v___x_1810_);
v___x_1812_ = lean_uint64_xor(v_fold_1809_, v___x_1811_);
v___x_1813_ = lean_uint64_to_usize(v___x_1812_);
v___x_1814_ = lean_usize_of_nat(v___x_1803_);
v___x_1815_ = ((size_t)1ULL);
v___x_1816_ = lean_usize_sub(v___x_1814_, v___x_1815_);
v___x_1817_ = lean_usize_land(v___x_1813_, v___x_1816_);
v_bkt_1818_ = lean_array_uget_borrowed(v_buckets_1797_, v___x_1817_);
v___x_1819_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg(v_a_1794_, v_bkt_1818_);
if (v___x_1819_ == 0)
{
lean_object* v___x_1820_; lean_object* v_size_x27_1821_; lean_object* v___x_1822_; lean_object* v_buckets_x27_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; uint8_t v___x_1829_; 
v___x_1820_ = lean_unsigned_to_nat(1u);
v_size_x27_1821_ = lean_nat_add(v_size_1796_, v___x_1820_);
lean_dec(v_size_1796_);
lean_inc(v_bkt_1818_);
v___x_1822_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1822_, 0, v_a_1794_);
lean_ctor_set(v___x_1822_, 1, v_b_1795_);
lean_ctor_set(v___x_1822_, 2, v_bkt_1818_);
v_buckets_x27_1823_ = lean_array_uset(v_buckets_1797_, v___x_1817_, v___x_1822_);
v___x_1824_ = lean_unsigned_to_nat(4u);
v___x_1825_ = lean_nat_mul(v_size_x27_1821_, v___x_1824_);
v___x_1826_ = lean_unsigned_to_nat(3u);
v___x_1827_ = lean_nat_div(v___x_1825_, v___x_1826_);
lean_dec(v___x_1825_);
v___x_1828_ = lean_array_get_size(v_buckets_x27_1823_);
v___x_1829_ = lean_nat_dec_le(v___x_1827_, v___x_1828_);
lean_dec(v___x_1827_);
if (v___x_1829_ == 0)
{
lean_object* v_val_1830_; lean_object* v___x_1832_; 
v_val_1830_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24___redArg(v_buckets_x27_1823_);
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 1, v_val_1830_);
lean_ctor_set(v___x_1799_, 0, v_size_x27_1821_);
v___x_1832_ = v___x_1799_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_size_x27_1821_);
lean_ctor_set(v_reuseFailAlloc_1833_, 1, v_val_1830_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
else
{
lean_object* v___x_1835_; 
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 1, v_buckets_x27_1823_);
lean_ctor_set(v___x_1799_, 0, v_size_x27_1821_);
v___x_1835_ = v___x_1799_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_size_x27_1821_);
lean_ctor_set(v_reuseFailAlloc_1836_, 1, v_buckets_x27_1823_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
else
{
lean_object* v___x_1837_; lean_object* v_buckets_x27_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1842_; 
lean_inc(v_bkt_1818_);
v___x_1837_ = lean_box(0);
v_buckets_x27_1838_ = lean_array_uset(v_buckets_1797_, v___x_1817_, v___x_1837_);
v___x_1839_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25___redArg(v_a_1794_, v_b_1795_, v_bkt_1818_);
v___x_1840_ = lean_array_uset(v_buckets_x27_1838_, v___x_1817_, v___x_1839_);
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 1, v___x_1840_);
v___x_1842_ = v___x_1799_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_size_1796_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg(uint8_t v___x_1847_, lean_object* v_as_1848_, size_t v_sz_1849_, size_t v_i_1850_, lean_object* v_b_1851_, lean_object* v___y_1852_){
_start:
{
uint8_t v___x_1854_; 
v___x_1854_ = lean_usize_dec_lt(v_i_1850_, v_sz_1849_);
if (v___x_1854_ == 0)
{
lean_object* v___x_1855_; 
v___x_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1855_, 0, v_b_1851_);
return v___x_1855_;
}
else
{
lean_object* v_snd_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1893_; 
v_snd_1856_ = lean_ctor_get(v_b_1851_, 1);
v_isSharedCheck_1893_ = !lean_is_exclusive(v_b_1851_);
if (v_isSharedCheck_1893_ == 0)
{
lean_object* v_unused_1894_; 
v_unused_1894_ = lean_ctor_get(v_b_1851_, 0);
lean_dec(v_unused_1894_);
v___x_1858_ = v_b_1851_;
v_isShared_1859_ = v_isSharedCheck_1893_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_snd_1856_);
lean_dec(v_b_1851_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1893_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v_ref_1860_; lean_object* v_a_1861_; lean_object* v_ref_1862_; lean_object* v_msg_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1892_; 
v_ref_1860_ = lean_ctor_get(v___y_1852_, 2);
v_a_1861_ = lean_array_uget(v_as_1848_, v_i_1850_);
v_ref_1862_ = lean_ctor_get(v_a_1861_, 0);
v_msg_1863_ = lean_ctor_get(v_a_1861_, 1);
v_isSharedCheck_1892_ = !lean_is_exclusive(v_a_1861_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1865_ = v_a_1861_;
v_isShared_1866_ = v_isSharedCheck_1892_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_msg_1863_);
lean_inc(v_ref_1862_);
lean_dec(v_a_1861_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1892_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1867_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v_ref_1884_; lean_object* v___y_1886_; lean_object* v___x_1889_; 
v___x_1867_ = lean_box(0);
v_ref_1884_ = l_Lean_replaceRef(v_ref_1862_, v_ref_1860_);
lean_dec(v_ref_1862_);
v___x_1889_ = l_Lean_Syntax_getPos_x3f(v_ref_1884_, v___x_1847_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v___x_1890_; 
v___x_1890_ = lean_unsigned_to_nat(0u);
v___y_1886_ = v___x_1890_;
goto v___jp_1885_;
}
else
{
lean_object* v_val_1891_; 
v_val_1891_ = lean_ctor_get(v___x_1889_, 0);
lean_inc(v_val_1891_);
lean_dec_ref_known(v___x_1889_, 1);
v___y_1886_ = v_val_1891_;
goto v___jp_1885_;
}
v___jp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 1, v___y_1870_);
lean_ctor_set(v___x_1858_, 0, v___y_1869_);
v___x_1872_ = v___x_1858_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___y_1869_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v___y_1870_);
v___x_1872_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v_pos2traces_1876_; lean_object* v___x_1878_; 
v___x_1873_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1874_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_1856_, v___x_1872_, v___x_1873_);
v___x_1875_ = lean_array_push(v___x_1874_, v_msg_1863_);
v_pos2traces_1876_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(v_snd_1856_, v___x_1872_, v___x_1875_);
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 1, v_pos2traces_1876_);
lean_ctor_set(v___x_1865_, 0, v___x_1867_);
v___x_1878_ = v___x_1865_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1867_);
lean_ctor_set(v_reuseFailAlloc_1882_, 1, v_pos2traces_1876_);
v___x_1878_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
size_t v___x_1879_; size_t v___x_1880_; 
v___x_1879_ = ((size_t)1ULL);
v___x_1880_ = lean_usize_add(v_i_1850_, v___x_1879_);
v_i_1850_ = v___x_1880_;
v_b_1851_ = v___x_1878_;
goto _start;
}
}
}
v___jp_1885_:
{
lean_object* v___x_1887_; 
v___x_1887_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1884_, v___x_1847_);
lean_dec(v_ref_1884_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_inc(v___y_1886_);
v___y_1869_ = v___y_1886_;
v___y_1870_ = v___y_1886_;
goto v___jp_1868_;
}
else
{
lean_object* v_val_1888_; 
v_val_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_val_1888_);
lean_dec_ref_known(v___x_1887_, 1);
v___y_1869_ = v___y_1886_;
v___y_1870_ = v_val_1888_;
goto v___jp_1868_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___boxed(lean_object* v___x_1895_, lean_object* v_as_1896_, lean_object* v_sz_1897_, lean_object* v_i_1898_, lean_object* v_b_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
uint8_t v___x_38626__boxed_1902_; size_t v_sz_boxed_1903_; size_t v_i_boxed_1904_; lean_object* v_res_1905_; 
v___x_38626__boxed_1902_ = lean_unbox(v___x_1895_);
v_sz_boxed_1903_ = lean_unbox_usize(v_sz_1897_);
lean_dec(v_sz_1897_);
v_i_boxed_1904_ = lean_unbox_usize(v_i_1898_);
lean_dec(v_i_1898_);
v_res_1905_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg(v___x_38626__boxed_1902_, v_as_1896_, v_sz_boxed_1903_, v_i_boxed_1904_, v_b_1899_, v___y_1900_);
lean_dec_ref(v___y_1900_);
lean_dec_ref(v_as_1896_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40(uint8_t v___x_1906_, lean_object* v_as_1907_, size_t v_sz_1908_, size_t v_i_1909_, lean_object* v_b_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
uint8_t v___x_1914_; 
v___x_1914_ = lean_usize_dec_lt(v_i_1909_, v_sz_1908_);
if (v___x_1914_ == 0)
{
lean_object* v___x_1915_; 
v___x_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1915_, 0, v_b_1910_);
return v___x_1915_;
}
else
{
lean_object* v_snd_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1953_; 
v_snd_1916_ = lean_ctor_get(v_b_1910_, 1);
v_isSharedCheck_1953_ = !lean_is_exclusive(v_b_1910_);
if (v_isSharedCheck_1953_ == 0)
{
lean_object* v_unused_1954_; 
v_unused_1954_ = lean_ctor_get(v_b_1910_, 0);
lean_dec(v_unused_1954_);
v___x_1918_ = v_b_1910_;
v_isShared_1919_ = v_isSharedCheck_1953_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_snd_1916_);
lean_dec(v_b_1910_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1953_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v_ref_1920_; lean_object* v_a_1921_; lean_object* v_ref_1922_; lean_object* v_msg_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1952_; 
v_ref_1920_ = lean_ctor_get(v___y_1911_, 2);
v_a_1921_ = lean_array_uget(v_as_1907_, v_i_1909_);
v_ref_1922_ = lean_ctor_get(v_a_1921_, 0);
v_msg_1923_ = lean_ctor_get(v_a_1921_, 1);
v_isSharedCheck_1952_ = !lean_is_exclusive(v_a_1921_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1925_ = v_a_1921_;
v_isShared_1926_ = v_isSharedCheck_1952_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_msg_1923_);
lean_inc(v_ref_1922_);
lean_dec(v_a_1921_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1952_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1927_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v_ref_1944_; lean_object* v___y_1946_; lean_object* v___x_1949_; 
v___x_1927_ = lean_box(0);
v_ref_1944_ = l_Lean_replaceRef(v_ref_1922_, v_ref_1920_);
lean_dec(v_ref_1922_);
v___x_1949_ = l_Lean_Syntax_getPos_x3f(v_ref_1944_, v___x_1906_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v___x_1950_; 
v___x_1950_ = lean_unsigned_to_nat(0u);
v___y_1946_ = v___x_1950_;
goto v___jp_1945_;
}
else
{
lean_object* v_val_1951_; 
v_val_1951_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_val_1951_);
lean_dec_ref_known(v___x_1949_, 1);
v___y_1946_ = v_val_1951_;
goto v___jp_1945_;
}
v___jp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 1, v___y_1930_);
lean_ctor_set(v___x_1918_, 0, v___y_1929_);
v___x_1932_ = v___x_1918_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v___y_1929_);
lean_ctor_set(v_reuseFailAlloc_1943_, 1, v___y_1930_);
v___x_1932_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v_pos2traces_1936_; lean_object* v___x_1938_; 
v___x_1933_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1934_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_1916_, v___x_1932_, v___x_1933_);
v___x_1935_ = lean_array_push(v___x_1934_, v_msg_1923_);
v_pos2traces_1936_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(v_snd_1916_, v___x_1932_, v___x_1935_);
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 1, v_pos2traces_1936_);
lean_ctor_set(v___x_1925_, 0, v___x_1927_);
v___x_1938_ = v___x_1925_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1927_);
lean_ctor_set(v_reuseFailAlloc_1942_, 1, v_pos2traces_1936_);
v___x_1938_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
size_t v___x_1939_; size_t v___x_1940_; lean_object* v___x_1941_; 
v___x_1939_ = ((size_t)1ULL);
v___x_1940_ = lean_usize_add(v_i_1909_, v___x_1939_);
v___x_1941_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg(v___x_1906_, v_as_1907_, v_sz_1908_, v___x_1940_, v___x_1938_, v___y_1911_);
return v___x_1941_;
}
}
}
v___jp_1945_:
{
lean_object* v___x_1947_; 
v___x_1947_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1944_, v___x_1906_);
lean_dec(v_ref_1944_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_inc(v___y_1946_);
v___y_1929_ = v___y_1946_;
v___y_1930_ = v___y_1946_;
goto v___jp_1928_;
}
else
{
lean_object* v_val_1948_; 
v_val_1948_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_val_1948_);
lean_dec_ref_known(v___x_1947_, 1);
v___y_1929_ = v___y_1946_;
v___y_1930_ = v_val_1948_;
goto v___jp_1928_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40___boxed(lean_object* v___x_1955_, lean_object* v_as_1956_, lean_object* v_sz_1957_, lean_object* v_i_1958_, lean_object* v_b_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
uint8_t v___x_38707__boxed_1963_; size_t v_sz_boxed_1964_; size_t v_i_boxed_1965_; lean_object* v_res_1966_; 
v___x_38707__boxed_1963_ = lean_unbox(v___x_1955_);
v_sz_boxed_1964_ = lean_unbox_usize(v_sz_1957_);
lean_dec(v_sz_1957_);
v_i_boxed_1965_ = lean_unbox_usize(v_i_1958_);
lean_dec(v_i_1958_);
v_res_1966_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40(v___x_38707__boxed_1963_, v_as_1956_, v_sz_boxed_1964_, v_i_boxed_1965_, v_b_1959_, v___y_1960_, v___y_1961_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec_ref(v_as_1956_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27(lean_object* v_init_1967_, uint8_t v___x_1968_, lean_object* v_n_1969_, lean_object* v_b_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
if (lean_obj_tag(v_n_1969_) == 0)
{
lean_object* v_cs_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; size_t v_sz_1977_; size_t v___x_1978_; lean_object* v___x_1979_; 
v_cs_1974_ = lean_ctor_get(v_n_1969_, 0);
v___x_1975_ = lean_box(0);
v___x_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1975_);
lean_ctor_set(v___x_1976_, 1, v_b_1970_);
v_sz_1977_ = lean_array_size(v_cs_1974_);
v___x_1978_ = ((size_t)0ULL);
v___x_1979_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__39(v_init_1967_, v___x_1968_, v_cs_1974_, v_sz_1977_, v___x_1978_, v___x_1976_, v___y_1971_, v___y_1972_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1994_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1982_ = v___x_1979_;
v_isShared_1983_ = v_isSharedCheck_1994_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1979_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1994_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v_fst_1984_; 
v_fst_1984_ = lean_ctor_get(v_a_1980_, 0);
if (lean_obj_tag(v_fst_1984_) == 0)
{
lean_object* v_snd_1985_; lean_object* v___x_1986_; lean_object* v___x_1988_; 
v_snd_1985_ = lean_ctor_get(v_a_1980_, 1);
lean_inc(v_snd_1985_);
lean_dec(v_a_1980_);
v___x_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1986_, 0, v_snd_1985_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v___x_1986_);
v___x_1988_ = v___x_1982_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___x_1986_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
else
{
lean_object* v_val_1990_; lean_object* v___x_1992_; 
lean_inc_ref(v_fst_1984_);
lean_dec(v_a_1980_);
v_val_1990_ = lean_ctor_get(v_fst_1984_, 0);
lean_inc(v_val_1990_);
lean_dec_ref_known(v_fst_1984_, 1);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v_val_1990_);
v___x_1992_ = v___x_1982_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_val_1990_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
else
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
v_a_1995_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1979_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1979_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1995_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
else
{
lean_object* v_vs_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; size_t v_sz_2006_; size_t v___x_2007_; lean_object* v___x_2008_; 
v_vs_2003_ = lean_ctor_get(v_n_1969_, 0);
v___x_2004_ = lean_box(0);
v___x_2005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2005_, 0, v___x_2004_);
lean_ctor_set(v___x_2005_, 1, v_b_1970_);
v_sz_2006_ = lean_array_size(v_vs_2003_);
v___x_2007_ = ((size_t)0ULL);
v___x_2008_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40(v___x_1968_, v_vs_2003_, v_sz_2006_, v___x_2007_, v___x_2005_, v___y_1971_, v___y_1972_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2023_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2011_ = v___x_2008_;
v_isShared_2012_ = v_isSharedCheck_2023_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_2008_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2023_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v_fst_2013_; 
v_fst_2013_ = lean_ctor_get(v_a_2009_, 0);
if (lean_obj_tag(v_fst_2013_) == 0)
{
lean_object* v_snd_2014_; lean_object* v___x_2015_; lean_object* v___x_2017_; 
v_snd_2014_ = lean_ctor_get(v_a_2009_, 1);
lean_inc(v_snd_2014_);
lean_dec(v_a_2009_);
v___x_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2015_, 0, v_snd_2014_);
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 0, v___x_2015_);
v___x_2017_ = v___x_2011_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2015_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
else
{
lean_object* v_val_2019_; lean_object* v___x_2021_; 
lean_inc_ref(v_fst_2013_);
lean_dec(v_a_2009_);
v_val_2019_ = lean_ctor_get(v_fst_2013_, 0);
lean_inc(v_val_2019_);
lean_dec_ref_known(v_fst_2013_, 1);
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 0, v_val_2019_);
v___x_2021_ = v___x_2011_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_val_2019_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
else
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
v_a_2024_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2026_ = v___x_2008_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2008_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2024_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__39(lean_object* v_init_2032_, uint8_t v___x_2033_, lean_object* v_as_2034_, size_t v_sz_2035_, size_t v_i_2036_, lean_object* v_b_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
uint8_t v___x_2041_; 
v___x_2041_ = lean_usize_dec_lt(v_i_2036_, v_sz_2035_);
if (v___x_2041_ == 0)
{
lean_object* v___x_2042_; 
v___x_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2042_, 0, v_b_2037_);
return v___x_2042_;
}
else
{
lean_object* v_snd_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2077_; 
v_snd_2043_ = lean_ctor_get(v_b_2037_, 1);
v_isSharedCheck_2077_ = !lean_is_exclusive(v_b_2037_);
if (v_isSharedCheck_2077_ == 0)
{
lean_object* v_unused_2078_; 
v_unused_2078_ = lean_ctor_get(v_b_2037_, 0);
lean_dec(v_unused_2078_);
v___x_2045_ = v_b_2037_;
v_isShared_2046_ = v_isSharedCheck_2077_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_snd_2043_);
lean_dec(v_b_2037_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2077_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2047_; lean_object* v_a_2048_; lean_object* v___x_2049_; 
v___x_2047_ = lean_box(0);
v_a_2048_ = lean_array_uget_borrowed(v_as_2034_, v_i_2036_);
lean_inc(v_snd_2043_);
v___x_2049_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27(v_init_2032_, v___x_2033_, v_a_2048_, v_snd_2043_, v___y_2038_, v___y_2039_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2068_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2052_ = v___x_2049_;
v_isShared_2053_ = v_isSharedCheck_2068_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2049_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2068_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
if (lean_obj_tag(v_a_2050_) == 0)
{
lean_object* v___x_2054_; lean_object* v___x_2056_; 
v___x_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2054_, 0, v_a_2050_);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 0, v___x_2054_);
v___x_2056_ = v___x_2045_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2054_);
lean_ctor_set(v_reuseFailAlloc_2060_, 1, v_snd_2043_);
v___x_2056_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
lean_object* v___x_2058_; 
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 0, v___x_2056_);
v___x_2058_ = v___x_2052_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v___x_2056_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; 
lean_del_object(v___x_2052_);
lean_dec(v_snd_2043_);
v_a_2061_ = lean_ctor_get(v_a_2050_, 0);
lean_inc(v_a_2061_);
lean_dec_ref_known(v_a_2050_, 1);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 1, v_a_2061_);
lean_ctor_set(v___x_2045_, 0, v___x_2047_);
v___x_2063_ = v___x_2045_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2047_);
lean_ctor_set(v_reuseFailAlloc_2067_, 1, v_a_2061_);
v___x_2063_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
size_t v___x_2064_; size_t v___x_2065_; 
v___x_2064_ = ((size_t)1ULL);
v___x_2065_ = lean_usize_add(v_i_2036_, v___x_2064_);
v_i_2036_ = v___x_2065_;
v_b_2037_ = v___x_2063_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
lean_del_object(v___x_2045_);
lean_dec(v_snd_2043_);
v_a_2069_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_2049_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2049_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2069_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__39___boxed(lean_object* v_init_2079_, lean_object* v___x_2080_, lean_object* v_as_2081_, lean_object* v_sz_2082_, lean_object* v_i_2083_, lean_object* v_b_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
uint8_t v___x_38788__boxed_2088_; size_t v_sz_boxed_2089_; size_t v_i_boxed_2090_; lean_object* v_res_2091_; 
v___x_38788__boxed_2088_ = lean_unbox(v___x_2080_);
v_sz_boxed_2089_ = lean_unbox_usize(v_sz_2082_);
lean_dec(v_sz_2082_);
v_i_boxed_2090_ = lean_unbox_usize(v_i_2083_);
lean_dec(v_i_2083_);
v_res_2091_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__39(v_init_2079_, v___x_38788__boxed_2088_, v_as_2081_, v_sz_boxed_2089_, v_i_boxed_2090_, v_b_2084_, v___y_2085_, v___y_2086_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
lean_dec_ref(v_as_2081_);
lean_dec_ref(v_init_2079_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27___boxed(lean_object* v_init_2092_, lean_object* v___x_2093_, lean_object* v_n_2094_, lean_object* v_b_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
uint8_t v___x_38808__boxed_2099_; lean_object* v_res_2100_; 
v___x_38808__boxed_2099_ = lean_unbox(v___x_2093_);
v_res_2100_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27(v_init_2092_, v___x_38808__boxed_2099_, v_n_2094_, v_b_2095_, v___y_2096_, v___y_2097_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec_ref(v_n_2094_);
lean_dec_ref(v_init_2092_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg(uint8_t v___x_2101_, lean_object* v_as_2102_, size_t v_sz_2103_, size_t v_i_2104_, lean_object* v_b_2105_, lean_object* v___y_2106_){
_start:
{
uint8_t v___x_2108_; 
v___x_2108_ = lean_usize_dec_lt(v_i_2104_, v_sz_2103_);
if (v___x_2108_ == 0)
{
lean_object* v___x_2109_; 
v___x_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2109_, 0, v_b_2105_);
return v___x_2109_;
}
else
{
lean_object* v_snd_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2147_; 
v_snd_2110_ = lean_ctor_get(v_b_2105_, 1);
v_isSharedCheck_2147_ = !lean_is_exclusive(v_b_2105_);
if (v_isSharedCheck_2147_ == 0)
{
lean_object* v_unused_2148_; 
v_unused_2148_ = lean_ctor_get(v_b_2105_, 0);
lean_dec(v_unused_2148_);
v___x_2112_ = v_b_2105_;
v_isShared_2113_ = v_isSharedCheck_2147_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_snd_2110_);
lean_dec(v_b_2105_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2147_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v_ref_2114_; lean_object* v_a_2115_; lean_object* v_ref_2116_; lean_object* v_msg_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2146_; 
v_ref_2114_ = lean_ctor_get(v___y_2106_, 2);
v_a_2115_ = lean_array_uget(v_as_2102_, v_i_2104_);
v_ref_2116_ = lean_ctor_get(v_a_2115_, 0);
v_msg_2117_ = lean_ctor_get(v_a_2115_, 1);
v_isSharedCheck_2146_ = !lean_is_exclusive(v_a_2115_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2119_ = v_a_2115_;
v_isShared_2120_ = v_isSharedCheck_2146_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_msg_2117_);
lean_inc(v_ref_2116_);
lean_dec(v_a_2115_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2146_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2121_; lean_object* v___y_2123_; lean_object* v___y_2124_; lean_object* v_ref_2138_; lean_object* v___y_2140_; lean_object* v___x_2143_; 
v___x_2121_ = lean_box(0);
v_ref_2138_ = l_Lean_replaceRef(v_ref_2116_, v_ref_2114_);
lean_dec(v_ref_2116_);
v___x_2143_ = l_Lean_Syntax_getPos_x3f(v_ref_2138_, v___x_2101_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v___x_2144_; 
v___x_2144_ = lean_unsigned_to_nat(0u);
v___y_2140_ = v___x_2144_;
goto v___jp_2139_;
}
else
{
lean_object* v_val_2145_; 
v_val_2145_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_val_2145_);
lean_dec_ref_known(v___x_2143_, 1);
v___y_2140_ = v_val_2145_;
goto v___jp_2139_;
}
v___jp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 1, v___y_2124_);
lean_ctor_set(v___x_2112_, 0, v___y_2123_);
v___x_2126_ = v___x_2112_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___y_2123_);
lean_ctor_set(v_reuseFailAlloc_2137_, 1, v___y_2124_);
v___x_2126_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v_pos2traces_2130_; lean_object* v___x_2132_; 
v___x_2127_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_2128_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_2110_, v___x_2126_, v___x_2127_);
v___x_2129_ = lean_array_push(v___x_2128_, v_msg_2117_);
v_pos2traces_2130_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(v_snd_2110_, v___x_2126_, v___x_2129_);
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 1, v_pos2traces_2130_);
lean_ctor_set(v___x_2119_, 0, v___x_2121_);
v___x_2132_ = v___x_2119_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2121_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v_pos2traces_2130_);
v___x_2132_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
size_t v___x_2133_; size_t v___x_2134_; 
v___x_2133_ = ((size_t)1ULL);
v___x_2134_ = lean_usize_add(v_i_2104_, v___x_2133_);
v_i_2104_ = v___x_2134_;
v_b_2105_ = v___x_2132_;
goto _start;
}
}
}
v___jp_2139_:
{
lean_object* v___x_2141_; 
v___x_2141_ = l_Lean_Syntax_getTailPos_x3f(v_ref_2138_, v___x_2101_);
lean_dec(v_ref_2138_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_inc(v___y_2140_);
v___y_2123_ = v___y_2140_;
v___y_2124_ = v___y_2140_;
goto v___jp_2122_;
}
else
{
lean_object* v_val_2142_; 
v_val_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_val_2142_);
lean_dec_ref_known(v___x_2141_, 1);
v___y_2123_ = v___y_2140_;
v___y_2124_ = v_val_2142_;
goto v___jp_2122_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg___boxed(lean_object* v___x_2149_, lean_object* v_as_2150_, lean_object* v_sz_2151_, lean_object* v_i_2152_, lean_object* v_b_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
uint8_t v___x_38991__boxed_2156_; size_t v_sz_boxed_2157_; size_t v_i_boxed_2158_; lean_object* v_res_2159_; 
v___x_38991__boxed_2156_ = lean_unbox(v___x_2149_);
v_sz_boxed_2157_ = lean_unbox_usize(v_sz_2151_);
lean_dec(v_sz_2151_);
v_i_boxed_2158_ = lean_unbox_usize(v_i_2152_);
lean_dec(v_i_2152_);
v_res_2159_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg(v___x_38991__boxed_2156_, v_as_2150_, v_sz_boxed_2157_, v_i_boxed_2158_, v_b_2153_, v___y_2154_);
lean_dec_ref(v___y_2154_);
lean_dec_ref(v_as_2150_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28(uint8_t v___x_2160_, lean_object* v_as_2161_, size_t v_sz_2162_, size_t v_i_2163_, lean_object* v_b_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
uint8_t v___x_2168_; 
v___x_2168_ = lean_usize_dec_lt(v_i_2163_, v_sz_2162_);
if (v___x_2168_ == 0)
{
lean_object* v___x_2169_; 
v___x_2169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2169_, 0, v_b_2164_);
return v___x_2169_;
}
else
{
lean_object* v_snd_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2207_; 
v_snd_2170_ = lean_ctor_get(v_b_2164_, 1);
v_isSharedCheck_2207_ = !lean_is_exclusive(v_b_2164_);
if (v_isSharedCheck_2207_ == 0)
{
lean_object* v_unused_2208_; 
v_unused_2208_ = lean_ctor_get(v_b_2164_, 0);
lean_dec(v_unused_2208_);
v___x_2172_ = v_b_2164_;
v_isShared_2173_ = v_isSharedCheck_2207_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_snd_2170_);
lean_dec(v_b_2164_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2207_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v_ref_2174_; lean_object* v_a_2175_; lean_object* v_ref_2176_; lean_object* v_msg_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2206_; 
v_ref_2174_ = lean_ctor_get(v___y_2165_, 2);
v_a_2175_ = lean_array_uget(v_as_2161_, v_i_2163_);
v_ref_2176_ = lean_ctor_get(v_a_2175_, 0);
v_msg_2177_ = lean_ctor_get(v_a_2175_, 1);
v_isSharedCheck_2206_ = !lean_is_exclusive(v_a_2175_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2179_ = v_a_2175_;
v_isShared_2180_ = v_isSharedCheck_2206_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_msg_2177_);
lean_inc(v_ref_2176_);
lean_dec(v_a_2175_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2206_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2181_; lean_object* v___y_2183_; lean_object* v___y_2184_; lean_object* v_ref_2198_; lean_object* v___y_2200_; lean_object* v___x_2203_; 
v___x_2181_ = lean_box(0);
v_ref_2198_ = l_Lean_replaceRef(v_ref_2176_, v_ref_2174_);
lean_dec(v_ref_2176_);
v___x_2203_ = l_Lean_Syntax_getPos_x3f(v_ref_2198_, v___x_2160_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v___x_2204_; 
v___x_2204_ = lean_unsigned_to_nat(0u);
v___y_2200_ = v___x_2204_;
goto v___jp_2199_;
}
else
{
lean_object* v_val_2205_; 
v_val_2205_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_val_2205_);
lean_dec_ref_known(v___x_2203_, 1);
v___y_2200_ = v_val_2205_;
goto v___jp_2199_;
}
v___jp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 1, v___y_2184_);
lean_ctor_set(v___x_2172_, 0, v___y_2183_);
v___x_2186_ = v___x_2172_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___y_2183_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v___y_2184_);
v___x_2186_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v_pos2traces_2190_; lean_object* v___x_2192_; 
v___x_2187_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_2188_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_2170_, v___x_2186_, v___x_2187_);
v___x_2189_ = lean_array_push(v___x_2188_, v_msg_2177_);
v_pos2traces_2190_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(v_snd_2170_, v___x_2186_, v___x_2189_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 1, v_pos2traces_2190_);
lean_ctor_set(v___x_2179_, 0, v___x_2181_);
v___x_2192_ = v___x_2179_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2181_);
lean_ctor_set(v_reuseFailAlloc_2196_, 1, v_pos2traces_2190_);
v___x_2192_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
size_t v___x_2193_; size_t v___x_2194_; lean_object* v___x_2195_; 
v___x_2193_ = ((size_t)1ULL);
v___x_2194_ = lean_usize_add(v_i_2163_, v___x_2193_);
v___x_2195_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg(v___x_2160_, v_as_2161_, v_sz_2162_, v___x_2194_, v___x_2192_, v___y_2165_);
return v___x_2195_;
}
}
}
v___jp_2199_:
{
lean_object* v___x_2201_; 
v___x_2201_ = l_Lean_Syntax_getTailPos_x3f(v_ref_2198_, v___x_2160_);
lean_dec(v_ref_2198_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_inc(v___y_2200_);
v___y_2183_ = v___y_2200_;
v___y_2184_ = v___y_2200_;
goto v___jp_2182_;
}
else
{
lean_object* v_val_2202_; 
v_val_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_val_2202_);
lean_dec_ref_known(v___x_2201_, 1);
v___y_2183_ = v___y_2200_;
v___y_2184_ = v_val_2202_;
goto v___jp_2182_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28___boxed(lean_object* v___x_2209_, lean_object* v_as_2210_, lean_object* v_sz_2211_, lean_object* v_i_2212_, lean_object* v_b_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
uint8_t v___x_39071__boxed_2217_; size_t v_sz_boxed_2218_; size_t v_i_boxed_2219_; lean_object* v_res_2220_; 
v___x_39071__boxed_2217_ = lean_unbox(v___x_2209_);
v_sz_boxed_2218_ = lean_unbox_usize(v_sz_2211_);
lean_dec(v_sz_2211_);
v_i_boxed_2219_ = lean_unbox_usize(v_i_2212_);
lean_dec(v_i_2212_);
v_res_2220_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28(v___x_39071__boxed_2217_, v_as_2210_, v_sz_boxed_2218_, v_i_boxed_2219_, v_b_2213_, v___y_2214_, v___y_2215_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec_ref(v_as_2210_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19(uint8_t v___x_2221_, lean_object* v_t_2222_, lean_object* v_init_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_){
_start:
{
lean_object* v_root_2227_; lean_object* v_tail_2228_; lean_object* v___x_2229_; 
v_root_2227_ = lean_ctor_get(v_t_2222_, 0);
v_tail_2228_ = lean_ctor_get(v_t_2222_, 1);
lean_inc_ref(v_init_2223_);
v___x_2229_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27(v_init_2223_, v___x_2221_, v_root_2227_, v_init_2223_, v___y_2224_, v___y_2225_);
lean_dec_ref(v_init_2223_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2266_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2232_ = v___x_2229_;
v_isShared_2233_ = v_isSharedCheck_2266_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2229_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2266_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
if (lean_obj_tag(v_a_2230_) == 0)
{
lean_object* v_a_2234_; lean_object* v___x_2236_; 
v_a_2234_ = lean_ctor_get(v_a_2230_, 0);
lean_inc(v_a_2234_);
lean_dec_ref_known(v_a_2230_, 1);
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 0, v_a_2234_);
v___x_2236_ = v___x_2232_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2234_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
else
{
lean_object* v_a_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; size_t v_sz_2241_; size_t v___x_2242_; lean_object* v___x_2243_; 
lean_del_object(v___x_2232_);
v_a_2238_ = lean_ctor_get(v_a_2230_, 0);
lean_inc(v_a_2238_);
lean_dec_ref_known(v_a_2230_, 1);
v___x_2239_ = lean_box(0);
v___x_2240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2239_);
lean_ctor_set(v___x_2240_, 1, v_a_2238_);
v_sz_2241_ = lean_array_size(v_tail_2228_);
v___x_2242_ = ((size_t)0ULL);
v___x_2243_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28(v___x_2221_, v_tail_2228_, v_sz_2241_, v___x_2242_, v___x_2240_, v___y_2224_, v___y_2225_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2257_; 
v_a_2244_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2246_ = v___x_2243_;
v_isShared_2247_ = v_isSharedCheck_2257_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___x_2243_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2257_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v_fst_2248_; 
v_fst_2248_ = lean_ctor_get(v_a_2244_, 0);
if (lean_obj_tag(v_fst_2248_) == 0)
{
lean_object* v_snd_2249_; lean_object* v___x_2251_; 
v_snd_2249_ = lean_ctor_get(v_a_2244_, 1);
lean_inc(v_snd_2249_);
lean_dec(v_a_2244_);
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 0, v_snd_2249_);
v___x_2251_ = v___x_2246_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_snd_2249_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
else
{
lean_object* v_val_2253_; lean_object* v___x_2255_; 
lean_inc_ref(v_fst_2248_);
lean_dec(v_a_2244_);
v_val_2253_ = lean_ctor_get(v_fst_2248_, 0);
lean_inc(v_val_2253_);
lean_dec_ref_known(v_fst_2248_, 1);
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 0, v_val_2253_);
v___x_2255_ = v___x_2246_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_val_2253_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
}
else
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2265_; 
v_a_2258_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2260_ = v___x_2243_;
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2243_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2263_; 
if (v_isShared_2261_ == 0)
{
v___x_2263_ = v___x_2260_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_a_2258_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
}
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
v_a_2267_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2269_ = v___x_2229_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2229_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2272_; 
if (v_isShared_2270_ == 0)
{
v___x_2272_ = v___x_2269_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_a_2267_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___boxed(lean_object* v___x_2275_, lean_object* v_t_2276_, lean_object* v_init_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_){
_start:
{
uint8_t v___x_39152__boxed_2281_; lean_object* v_res_2282_; 
v___x_39152__boxed_2281_ = lean_unbox(v___x_2275_);
v_res_2282_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19(v___x_39152__boxed_2281_, v_t_2276_, v_init_2277_, v___y_2278_, v___y_2279_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec_ref(v_t_2276_);
return v_res_2282_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__0(void){
_start:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2283_ = lean_unsigned_to_nat(32u);
v___x_2284_ = lean_mk_empty_array_with_capacity(v___x_2283_);
v___x_2285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2284_);
return v___x_2285_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1(void){
_start:
{
size_t v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2286_ = ((size_t)5ULL);
v___x_2287_ = lean_unsigned_to_nat(0u);
v___x_2288_ = lean_unsigned_to_nat(32u);
v___x_2289_ = lean_mk_empty_array_with_capacity(v___x_2288_);
v___x_2290_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__0);
v___x_2291_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2291_, 0, v___x_2290_);
lean_ctor_set(v___x_2291_, 1, v___x_2289_);
lean_ctor_set(v___x_2291_, 2, v___x_2287_);
lean_ctor_set(v___x_2291_, 3, v___x_2287_);
lean_ctor_set_usize(v___x_2291_, 4, v___x_2286_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(lean_object* v___y_2292_){
_start:
{
lean_object* v___x_2294_; lean_object* v_traceState_2295_; lean_object* v_traces_2296_; lean_object* v___x_2297_; lean_object* v_traceState_2298_; lean_object* v_env_2299_; lean_object* v_nextMacroScope_2300_; lean_object* v_ngen_2301_; lean_object* v_auxDeclNGen_2302_; lean_object* v_cache_2303_; lean_object* v_recordedDeps_2304_; lean_object* v_messages_2305_; lean_object* v_infoState_2306_; lean_object* v_snapshotTasks_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2326_; 
v___x_2294_ = lean_st_ref_get(v___y_2292_);
v_traceState_2295_ = lean_ctor_get(v___x_2294_, 4);
lean_inc_ref(v_traceState_2295_);
lean_dec(v___x_2294_);
v_traces_2296_ = lean_ctor_get(v_traceState_2295_, 0);
lean_inc_ref(v_traces_2296_);
lean_dec_ref(v_traceState_2295_);
v___x_2297_ = lean_st_ref_take(v___y_2292_);
v_traceState_2298_ = lean_ctor_get(v___x_2297_, 4);
v_env_2299_ = lean_ctor_get(v___x_2297_, 0);
v_nextMacroScope_2300_ = lean_ctor_get(v___x_2297_, 1);
v_ngen_2301_ = lean_ctor_get(v___x_2297_, 2);
v_auxDeclNGen_2302_ = lean_ctor_get(v___x_2297_, 3);
v_cache_2303_ = lean_ctor_get(v___x_2297_, 5);
v_recordedDeps_2304_ = lean_ctor_get(v___x_2297_, 6);
v_messages_2305_ = lean_ctor_get(v___x_2297_, 7);
v_infoState_2306_ = lean_ctor_get(v___x_2297_, 8);
v_snapshotTasks_2307_ = lean_ctor_get(v___x_2297_, 9);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2309_ = v___x_2297_;
v_isShared_2310_ = v_isSharedCheck_2326_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_snapshotTasks_2307_);
lean_inc(v_infoState_2306_);
lean_inc(v_messages_2305_);
lean_inc(v_recordedDeps_2304_);
lean_inc(v_cache_2303_);
lean_inc(v_traceState_2298_);
lean_inc(v_auxDeclNGen_2302_);
lean_inc(v_ngen_2301_);
lean_inc(v_nextMacroScope_2300_);
lean_inc(v_env_2299_);
lean_dec(v___x_2297_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2326_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
uint64_t v_tid_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2324_; 
v_tid_2311_ = lean_ctor_get_uint64(v_traceState_2298_, sizeof(void*)*1);
v_isSharedCheck_2324_ = !lean_is_exclusive(v_traceState_2298_);
if (v_isSharedCheck_2324_ == 0)
{
lean_object* v_unused_2325_; 
v_unused_2325_ = lean_ctor_get(v_traceState_2298_, 0);
lean_dec(v_unused_2325_);
v___x_2313_ = v_traceState_2298_;
v_isShared_2314_ = v_isSharedCheck_2324_;
goto v_resetjp_2312_;
}
else
{
lean_dec(v_traceState_2298_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2324_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2315_; lean_object* v___x_2317_; 
v___x_2315_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1);
if (v_isShared_2314_ == 0)
{
lean_ctor_set(v___x_2313_, 0, v___x_2315_);
v___x_2317_ = v___x_2313_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v___x_2315_);
lean_ctor_set_uint64(v_reuseFailAlloc_2323_, sizeof(void*)*1, v_tid_2311_);
v___x_2317_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
lean_object* v___x_2319_; 
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 4, v___x_2317_);
v___x_2319_ = v___x_2309_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_env_2299_);
lean_ctor_set(v_reuseFailAlloc_2322_, 1, v_nextMacroScope_2300_);
lean_ctor_set(v_reuseFailAlloc_2322_, 2, v_ngen_2301_);
lean_ctor_set(v_reuseFailAlloc_2322_, 3, v_auxDeclNGen_2302_);
lean_ctor_set(v_reuseFailAlloc_2322_, 4, v___x_2317_);
lean_ctor_set(v_reuseFailAlloc_2322_, 5, v_cache_2303_);
lean_ctor_set(v_reuseFailAlloc_2322_, 6, v_recordedDeps_2304_);
lean_ctor_set(v_reuseFailAlloc_2322_, 7, v_messages_2305_);
lean_ctor_set(v_reuseFailAlloc_2322_, 8, v_infoState_2306_);
lean_ctor_set(v_reuseFailAlloc_2322_, 9, v_snapshotTasks_2307_);
v___x_2319_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2320_ = lean_st_ref_put(v___y_2292_, v___x_2319_);
v___x_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2321_, 0, v_traces_2296_);
return v___x_2321_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___boxed(lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v___y_2327_);
lean_dec(v___y_2327_);
return v_res_2329_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0(void){
_start:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2330_ = lean_box(0);
v___x_2331_ = lean_unsigned_to_nat(16u);
v___x_2332_ = lean_mk_array(v___x_2331_, v___x_2330_);
return v___x_2332_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1(void){
_start:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v_pos2traces_2335_; 
v___x_2333_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0, &l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0);
v___x_2334_ = lean_unsigned_to_nat(0u);
v_pos2traces_2335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos2traces_2335_, 0, v___x_2334_);
lean_ctor_set(v_pos2traces_2335_, 1, v___x_2333_);
return v_pos2traces_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__9(lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v_toCold_2342_; lean_object* v_options_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v_toCold_2342_ = lean_ctor_get(v___y_2336_, 0);
v_options_2343_ = lean_ctor_get(v_toCold_2342_, 2);
v___x_2344_ = l_Lean_trace_profiler_output;
v___x_2345_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14(v_options_2343_, v___x_2344_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v___x_2346_; uint8_t v___x_2347_; 
v___x_2346_ = l_Lean_trace_profiler_serve;
v___x_2347_ = l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(v_options_2343_, v___x_2346_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2348_; lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2411_; 
v___x_2348_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v___y_2337_);
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2351_ = v___x_2348_;
v_isShared_2352_ = v_isSharedCheck_2411_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2348_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2411_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
uint8_t v___x_2353_; 
v___x_2353_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_2349_);
if (v___x_2353_ == 0)
{
lean_object* v___x_2354_; lean_object* v_pos2traces_2355_; lean_object* v___x_2356_; 
lean_del_object(v___x_2351_);
v___x_2354_ = lean_unsigned_to_nat(0u);
v_pos2traces_2355_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1, &l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1);
v___x_2356_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19(v___x_2353_, v_a_2349_, v_pos2traces_2355_, v___y_2336_, v___y_2337_);
lean_dec(v_a_2349_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v_a_2357_; lean_object* v___y_2359_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2385_; lean_object* v_size_2391_; lean_object* v_buckets_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; uint8_t v___x_2395_; 
v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
lean_inc(v_a_2357_);
lean_dec_ref_known(v___x_2356_, 1);
v_size_2391_ = lean_ctor_get(v_a_2357_, 0);
lean_inc(v_size_2391_);
v_buckets_2392_ = lean_ctor_get(v_a_2357_, 1);
lean_inc_ref(v_buckets_2392_);
lean_dec(v_a_2357_);
v___x_2393_ = lean_mk_empty_array_with_capacity(v_size_2391_);
lean_dec(v_size_2391_);
v___x_2394_ = lean_array_get_size(v_buckets_2392_);
v___x_2395_ = lean_nat_dec_lt(v___x_2354_, v___x_2394_);
if (v___x_2395_ == 0)
{
lean_dec_ref(v_buckets_2392_);
v___y_2385_ = v___x_2393_;
goto v___jp_2384_;
}
else
{
size_t v___x_2396_; size_t v___x_2397_; lean_object* v___x_2398_; 
v___x_2396_ = ((size_t)0ULL);
v___x_2397_ = lean_usize_of_nat(v___x_2394_);
v___x_2398_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__23(v_buckets_2392_, v___x_2396_, v___x_2397_, v___x_2393_);
lean_dec_ref(v_buckets_2392_);
v___y_2385_ = v___x_2398_;
goto v___jp_2384_;
}
v___jp_2358_:
{
lean_object* v___x_2360_; size_t v_sz_2361_; size_t v___x_2362_; lean_object* v___x_2363_; 
v___x_2360_ = lean_box(0);
v_sz_2361_ = lean_array_size(v___y_2359_);
v___x_2362_ = ((size_t)0ULL);
v___x_2363_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20(v___x_2347_, v___y_2359_, v_sz_2361_, v___x_2362_, v___x_2360_, v___y_2336_, v___y_2337_);
lean_dec_ref(v___y_2359_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2370_ == 0)
{
lean_object* v_unused_2371_; 
v_unused_2371_ = lean_ctor_get(v___x_2363_, 0);
lean_dec(v_unused_2371_);
v___x_2365_ = v___x_2363_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_dec(v___x_2363_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 0, v___x_2360_);
v___x_2368_ = v___x_2365_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2360_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
else
{
return v___x_2363_;
}
}
v___jp_2372_:
{
lean_object* v___x_2377_; 
v___x_2377_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(v___y_2375_, v___y_2374_, v___y_2373_, v___y_2376_);
lean_dec(v___y_2376_);
lean_dec(v___y_2375_);
v___y_2359_ = v___x_2377_;
goto v___jp_2358_;
}
v___jp_2378_:
{
uint8_t v___x_2383_; 
v___x_2383_ = lean_nat_dec_le(v___y_2382_, v___y_2380_);
if (v___x_2383_ == 0)
{
lean_dec(v___y_2380_);
lean_inc(v___y_2382_);
v___y_2373_ = v___y_2382_;
v___y_2374_ = v___y_2379_;
v___y_2375_ = v___y_2381_;
v___y_2376_ = v___y_2382_;
goto v___jp_2372_;
}
else
{
v___y_2373_ = v___y_2382_;
v___y_2374_ = v___y_2379_;
v___y_2375_ = v___y_2381_;
v___y_2376_ = v___y_2380_;
goto v___jp_2372_;
}
}
v___jp_2384_:
{
lean_object* v___x_2386_; uint8_t v___x_2387_; 
v___x_2386_ = lean_array_get_size(v___y_2385_);
v___x_2387_ = lean_nat_dec_eq(v___x_2386_, v___x_2354_);
if (v___x_2387_ == 0)
{
lean_object* v___x_2388_; lean_object* v___x_2389_; uint8_t v___x_2390_; 
v___x_2388_ = lean_unsigned_to_nat(1u);
v___x_2389_ = lean_nat_sub(v___x_2386_, v___x_2388_);
v___x_2390_ = lean_nat_dec_le(v___x_2354_, v___x_2389_);
if (v___x_2390_ == 0)
{
lean_inc(v___x_2389_);
v___y_2379_ = v___y_2385_;
v___y_2380_ = v___x_2389_;
v___y_2381_ = v___x_2386_;
v___y_2382_ = v___x_2389_;
goto v___jp_2378_;
}
else
{
v___y_2379_ = v___y_2385_;
v___y_2380_ = v___x_2389_;
v___y_2381_ = v___x_2386_;
v___y_2382_ = v___x_2354_;
goto v___jp_2378_;
}
}
else
{
v___y_2359_ = v___y_2385_;
goto v___jp_2358_;
}
}
}
else
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2406_; 
v_a_2399_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2401_ = v___x_2356_;
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2356_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2404_; 
if (v_isShared_2402_ == 0)
{
v___x_2404_ = v___x_2401_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_a_2399_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
else
{
lean_object* v___x_2407_; lean_object* v___x_2409_; 
lean_dec(v_a_2349_);
v___x_2407_ = lean_box(0);
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 0, v___x_2407_);
v___x_2409_ = v___x_2351_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___x_2407_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
else
{
goto v___jp_2339_;
}
}
else
{
lean_dec_ref_known(v___x_2345_, 1);
goto v___jp_2339_;
}
v___jp_2339_:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2340_ = lean_box(0);
v___x_2341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2340_);
return v___x_2341_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__9___boxed(lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l_Lean_addTraceAsMessages___at___00main_spec__9(v___y_2412_, v___y_2413_);
lean_dec(v___y_2413_);
lean_dec_ref(v___y_2412_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10(lean_object* v_as_2416_, size_t v_sz_2417_, size_t v_i_2418_, lean_object* v_b_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
uint8_t v___x_2423_; 
v___x_2423_ = lean_usize_dec_lt(v_i_2418_, v_sz_2417_);
if (v___x_2423_ == 0)
{
lean_object* v___x_2424_; 
v___x_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2424_, 0, v_b_2419_);
return v___x_2424_;
}
else
{
lean_object* v___x_2425_; lean_object* v_a_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2425_ = lean_box(0);
v_a_2426_ = lean_array_uget_borrowed(v_as_2416_, v_i_2418_);
v___x_2427_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2420_);
lean_inc(v_a_2426_);
v___x_2428_ = l_Lean_Compiler_LCNF_resumeCompilation(v_a_2426_, v___x_2427_, v___y_2420_, v___y_2421_);
if (lean_obj_tag(v___x_2428_) == 0)
{
lean_object* v___x_2429_; 
lean_dec_ref_known(v___x_2428_, 1);
v___x_2429_ = l_Lean_addTraceAsMessages___at___00main_spec__9(v___y_2420_, v___y_2421_);
if (lean_obj_tag(v___x_2429_) == 0)
{
size_t v___x_2430_; size_t v___x_2431_; 
lean_dec_ref_known(v___x_2429_, 1);
v___x_2430_ = ((size_t)1ULL);
v___x_2431_ = lean_usize_add(v_i_2418_, v___x_2430_);
v_i_2418_ = v___x_2431_;
v_b_2419_ = v___x_2425_;
goto _start;
}
else
{
return v___x_2429_;
}
}
else
{
lean_object* v_a_2433_; lean_object* v___x_2434_; 
v_a_2433_ = lean_ctor_get(v___x_2428_, 0);
lean_inc(v_a_2433_);
lean_dec_ref_known(v___x_2428_, 1);
v___x_2434_ = l_Lean_addTraceAsMessages___at___00main_spec__9(v___y_2420_, v___y_2421_);
if (lean_obj_tag(v___x_2434_) == 0)
{
lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2441_; 
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2441_ == 0)
{
lean_object* v_unused_2442_; 
v_unused_2442_ = lean_ctor_get(v___x_2434_, 0);
lean_dec(v_unused_2442_);
v___x_2436_ = v___x_2434_;
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
else
{
lean_dec(v___x_2434_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2439_; 
if (v_isShared_2437_ == 0)
{
lean_ctor_set_tag(v___x_2436_, 1);
lean_ctor_set(v___x_2436_, 0, v_a_2433_);
v___x_2439_ = v___x_2436_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_a_2433_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
else
{
lean_dec(v_a_2433_);
return v___x_2434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10___boxed(lean_object* v_as_2443_, lean_object* v_sz_2444_, lean_object* v_i_2445_, lean_object* v_b_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
size_t v_sz_boxed_2450_; size_t v_i_boxed_2451_; lean_object* v_res_2452_; 
v_sz_boxed_2450_ = lean_unbox_usize(v_sz_2444_);
lean_dec(v_sz_2444_);
v_i_boxed_2451_ = lean_unbox_usize(v_i_2445_);
lean_dec(v_i_2445_);
v_res_2452_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10(v_as_2443_, v_sz_boxed_2450_, v_i_boxed_2451_, v_b_2446_, v___y_2447_, v___y_2448_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec_ref(v_as_2443_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg(lean_object* v_as_2453_, size_t v_sz_2454_, size_t v_i_2455_, lean_object* v_b_2456_, lean_object* v___y_2457_){
_start:
{
uint8_t v___x_2459_; 
v___x_2459_ = lean_usize_dec_lt(v_i_2455_, v_sz_2454_);
if (v___x_2459_ == 0)
{
lean_object* v___x_2460_; 
v___x_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2460_, 0, v_b_2456_);
return v___x_2460_;
}
else
{
uint8_t v___x_2461_; lean_object* v_a_2462_; lean_object* v___x_2463_; lean_object* v_ref_2464_; lean_object* v___x_2465_; 
lean_dec_ref(v_b_2456_);
v___x_2461_ = 0;
v_a_2462_ = lean_array_uget_borrowed(v_as_2453_, v_i_2455_);
lean_inc(v_a_2462_);
v___x_2463_ = l_Lean_Message_toString(v_a_2462_, v___x_2461_);
v_ref_2464_ = lean_ctor_get(v___y_2457_, 2);
v___x_2465_ = l_IO_eprintln___at___00main_spec__6(v___x_2463_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v___x_2466_; size_t v___x_2467_; size_t v___x_2468_; 
lean_dec_ref_known(v___x_2465_, 1);
v___x_2466_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___closed__0));
v___x_2467_ = ((size_t)1ULL);
v___x_2468_ = lean_usize_add(v_i_2455_, v___x_2467_);
v_i_2455_ = v___x_2468_;
v_b_2456_ = v___x_2466_;
goto _start;
}
else
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2481_; 
v_a_2470_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2472_ = v___x_2465_;
v_isShared_2473_ = v_isSharedCheck_2481_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2465_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2481_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2479_; 
v___x_2474_ = lean_io_error_to_string(v_a_2470_);
v___x_2475_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2474_);
v___x_2476_ = l_Lean_MessageData_ofFormat(v___x_2475_);
lean_inc(v_ref_2464_);
v___x_2477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2477_, 0, v_ref_2464_);
lean_ctor_set(v___x_2477_, 1, v___x_2476_);
if (v_isShared_2473_ == 0)
{
lean_ctor_set(v___x_2472_, 0, v___x_2477_);
v___x_2479_ = v___x_2472_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v___x_2477_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg___boxed(lean_object* v_as_2482_, lean_object* v_sz_2483_, lean_object* v_i_2484_, lean_object* v_b_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_){
_start:
{
size_t v_sz_boxed_2488_; size_t v_i_boxed_2489_; lean_object* v_res_2490_; 
v_sz_boxed_2488_ = lean_unbox_usize(v_sz_2483_);
lean_dec(v_sz_2483_);
v_i_boxed_2489_ = lean_unbox_usize(v_i_2484_);
lean_dec(v_i_2484_);
v_res_2490_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg(v_as_2482_, v_sz_boxed_2488_, v_i_boxed_2489_, v_b_2485_, v___y_2486_);
lean_dec_ref(v___y_2486_);
lean_dec_ref(v_as_2482_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38(lean_object* v_as_2491_, size_t v_sz_2492_, size_t v_i_2493_, lean_object* v_b_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
uint8_t v___x_2498_; 
v___x_2498_ = lean_usize_dec_lt(v_i_2493_, v_sz_2492_);
if (v___x_2498_ == 0)
{
lean_object* v___x_2499_; 
v___x_2499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2499_, 0, v_b_2494_);
return v___x_2499_;
}
else
{
uint8_t v___x_2500_; lean_object* v_a_2501_; lean_object* v___x_2502_; lean_object* v_ref_2503_; lean_object* v___x_2504_; 
lean_dec_ref(v_b_2494_);
v___x_2500_ = 0;
v_a_2501_ = lean_array_uget_borrowed(v_as_2491_, v_i_2493_);
lean_inc(v_a_2501_);
v___x_2502_ = l_Lean_Message_toString(v_a_2501_, v___x_2500_);
v_ref_2503_ = lean_ctor_get(v___y_2495_, 2);
v___x_2504_ = l_IO_eprintln___at___00main_spec__6(v___x_2502_);
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v___x_2505_; size_t v___x_2506_; size_t v___x_2507_; lean_object* v___x_2508_; 
lean_dec_ref_known(v___x_2504_, 1);
v___x_2505_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___closed__0));
v___x_2506_ = ((size_t)1ULL);
v___x_2507_ = lean_usize_add(v_i_2493_, v___x_2506_);
v___x_2508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg(v_as_2491_, v_sz_2492_, v___x_2507_, v___x_2505_, v___y_2495_);
return v___x_2508_;
}
else
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2520_; 
v_a_2509_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2511_ = v___x_2504_;
v_isShared_2512_ = v_isSharedCheck_2520_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2504_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2520_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2518_; 
v___x_2513_ = lean_io_error_to_string(v_a_2509_);
v___x_2514_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2513_);
v___x_2515_ = l_Lean_MessageData_ofFormat(v___x_2514_);
lean_inc(v_ref_2503_);
v___x_2516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2516_, 0, v_ref_2503_);
lean_ctor_set(v___x_2516_, 1, v___x_2515_);
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 0, v___x_2516_);
v___x_2518_ = v___x_2511_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v___x_2516_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38___boxed(lean_object* v_as_2521_, lean_object* v_sz_2522_, lean_object* v_i_2523_, lean_object* v_b_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
size_t v_sz_boxed_2528_; size_t v_i_boxed_2529_; lean_object* v_res_2530_; 
v_sz_boxed_2528_ = lean_unbox_usize(v_sz_2522_);
lean_dec(v_sz_2522_);
v_i_boxed_2529_ = lean_unbox_usize(v_i_2523_);
lean_dec(v_i_2523_);
v_res_2530_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38(v_as_2521_, v_sz_boxed_2528_, v_i_boxed_2529_, v_b_2524_, v___y_2525_, v___y_2526_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec_ref(v_as_2521_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26(lean_object* v_init_2531_, lean_object* v_n_2532_, lean_object* v_b_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_){
_start:
{
if (lean_obj_tag(v_n_2532_) == 0)
{
lean_object* v_cs_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; size_t v_sz_2540_; size_t v___x_2541_; lean_object* v___x_2542_; 
v_cs_2537_ = lean_ctor_get(v_n_2532_, 0);
v___x_2538_ = lean_box(0);
v___x_2539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2538_);
lean_ctor_set(v___x_2539_, 1, v_b_2533_);
v_sz_2540_ = lean_array_size(v_cs_2537_);
v___x_2541_ = ((size_t)0ULL);
v___x_2542_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__37(v_init_2531_, v_cs_2537_, v_sz_2540_, v___x_2541_, v___x_2539_, v___y_2534_, v___y_2535_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2557_; 
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2545_ = v___x_2542_;
v_isShared_2546_ = v_isSharedCheck_2557_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2542_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2557_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v_fst_2547_; 
v_fst_2547_ = lean_ctor_get(v_a_2543_, 0);
if (lean_obj_tag(v_fst_2547_) == 0)
{
lean_object* v_snd_2548_; lean_object* v___x_2549_; lean_object* v___x_2551_; 
v_snd_2548_ = lean_ctor_get(v_a_2543_, 1);
lean_inc(v_snd_2548_);
lean_dec(v_a_2543_);
v___x_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2549_, 0, v_snd_2548_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 0, v___x_2549_);
v___x_2551_ = v___x_2545_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v___x_2549_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
else
{
lean_object* v_val_2553_; lean_object* v___x_2555_; 
lean_inc_ref(v_fst_2547_);
lean_dec(v_a_2543_);
v_val_2553_ = lean_ctor_get(v_fst_2547_, 0);
lean_inc(v_val_2553_);
lean_dec_ref_known(v_fst_2547_, 1);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 0, v_val_2553_);
v___x_2555_ = v___x_2545_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_val_2553_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
}
else
{
lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2565_; 
v_a_2558_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2560_ = v___x_2542_;
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2542_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2563_; 
if (v_isShared_2561_ == 0)
{
v___x_2563_ = v___x_2560_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_a_2558_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
else
{
lean_object* v_vs_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; size_t v_sz_2569_; size_t v___x_2570_; lean_object* v___x_2571_; 
v_vs_2566_ = lean_ctor_get(v_n_2532_, 0);
v___x_2567_ = lean_box(0);
v___x_2568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2567_);
lean_ctor_set(v___x_2568_, 1, v_b_2533_);
v_sz_2569_ = lean_array_size(v_vs_2566_);
v___x_2570_ = ((size_t)0ULL);
v___x_2571_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38(v_vs_2566_, v_sz_2569_, v___x_2570_, v___x_2568_, v___y_2534_, v___y_2535_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2586_; 
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2574_ = v___x_2571_;
v_isShared_2575_ = v_isSharedCheck_2586_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2571_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2586_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v_fst_2576_; 
v_fst_2576_ = lean_ctor_get(v_a_2572_, 0);
if (lean_obj_tag(v_fst_2576_) == 0)
{
lean_object* v_snd_2577_; lean_object* v___x_2578_; lean_object* v___x_2580_; 
v_snd_2577_ = lean_ctor_get(v_a_2572_, 1);
lean_inc(v_snd_2577_);
lean_dec(v_a_2572_);
v___x_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2578_, 0, v_snd_2577_);
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 0, v___x_2578_);
v___x_2580_ = v___x_2574_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2578_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
else
{
lean_object* v_val_2582_; lean_object* v___x_2584_; 
lean_inc_ref(v_fst_2576_);
lean_dec(v_a_2572_);
v_val_2582_ = lean_ctor_get(v_fst_2576_, 0);
lean_inc(v_val_2582_);
lean_dec_ref_known(v_fst_2576_, 1);
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 0, v_val_2582_);
v___x_2584_ = v___x_2574_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_val_2582_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
}
else
{
lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2594_; 
v_a_2587_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2589_ = v___x_2571_;
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v___x_2571_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2592_; 
if (v_isShared_2590_ == 0)
{
v___x_2592_ = v___x_2589_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_a_2587_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
return v___x_2592_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__37(lean_object* v_init_2595_, lean_object* v_as_2596_, size_t v_sz_2597_, size_t v_i_2598_, lean_object* v_b_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
uint8_t v___x_2603_; 
v___x_2603_ = lean_usize_dec_lt(v_i_2598_, v_sz_2597_);
if (v___x_2603_ == 0)
{
lean_object* v___x_2604_; 
v___x_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2604_, 0, v_b_2599_);
return v___x_2604_;
}
else
{
lean_object* v_snd_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2639_; 
v_snd_2605_ = lean_ctor_get(v_b_2599_, 1);
v_isSharedCheck_2639_ = !lean_is_exclusive(v_b_2599_);
if (v_isSharedCheck_2639_ == 0)
{
lean_object* v_unused_2640_; 
v_unused_2640_ = lean_ctor_get(v_b_2599_, 0);
lean_dec(v_unused_2640_);
v___x_2607_ = v_b_2599_;
v_isShared_2608_ = v_isSharedCheck_2639_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_snd_2605_);
lean_dec(v_b_2599_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2639_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2609_; lean_object* v_a_2610_; lean_object* v___x_2611_; 
v___x_2609_ = lean_box(0);
v_a_2610_ = lean_array_uget_borrowed(v_as_2596_, v_i_2598_);
lean_inc(v_snd_2605_);
v___x_2611_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26(v_init_2595_, v_a_2610_, v_snd_2605_, v___y_2600_, v___y_2601_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2630_; 
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2614_ = v___x_2611_;
v_isShared_2615_ = v_isSharedCheck_2630_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2611_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2630_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
if (lean_obj_tag(v_a_2612_) == 0)
{
lean_object* v___x_2616_; lean_object* v___x_2618_; 
v___x_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2616_, 0, v_a_2612_);
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 0, v___x_2616_);
v___x_2618_ = v___x_2607_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v___x_2616_);
lean_ctor_set(v_reuseFailAlloc_2622_, 1, v_snd_2605_);
v___x_2618_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
lean_object* v___x_2620_; 
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 0, v___x_2618_);
v___x_2620_ = v___x_2614_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v___x_2618_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
else
{
lean_object* v_a_2623_; lean_object* v___x_2625_; 
lean_del_object(v___x_2614_);
lean_dec(v_snd_2605_);
v_a_2623_ = lean_ctor_get(v_a_2612_, 0);
lean_inc(v_a_2623_);
lean_dec_ref_known(v_a_2612_, 1);
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 1, v_a_2623_);
lean_ctor_set(v___x_2607_, 0, v___x_2609_);
v___x_2625_ = v___x_2607_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v___x_2609_);
lean_ctor_set(v_reuseFailAlloc_2629_, 1, v_a_2623_);
v___x_2625_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
size_t v___x_2626_; size_t v___x_2627_; 
v___x_2626_ = ((size_t)1ULL);
v___x_2627_ = lean_usize_add(v_i_2598_, v___x_2626_);
v_i_2598_ = v___x_2627_;
v_b_2599_ = v___x_2625_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2638_; 
lean_del_object(v___x_2607_);
lean_dec(v_snd_2605_);
v_a_2631_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2633_ = v___x_2611_;
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_dec(v___x_2611_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2636_; 
if (v_isShared_2634_ == 0)
{
v___x_2636_ = v___x_2633_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2631_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__37___boxed(lean_object* v_init_2641_, lean_object* v_as_2642_, lean_object* v_sz_2643_, lean_object* v_i_2644_, lean_object* v_b_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_){
_start:
{
size_t v_sz_boxed_2649_; size_t v_i_boxed_2650_; lean_object* v_res_2651_; 
v_sz_boxed_2649_ = lean_unbox_usize(v_sz_2643_);
lean_dec(v_sz_2643_);
v_i_boxed_2650_ = lean_unbox_usize(v_i_2644_);
lean_dec(v_i_2644_);
v_res_2651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__37(v_init_2641_, v_as_2642_, v_sz_boxed_2649_, v_i_boxed_2650_, v_b_2645_, v___y_2646_, v___y_2647_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec_ref(v_as_2642_);
return v_res_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26___boxed(lean_object* v_init_2652_, lean_object* v_n_2653_, lean_object* v_b_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_){
_start:
{
lean_object* v_res_2658_; 
v_res_2658_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26(v_init_2652_, v_n_2653_, v_b_2654_, v___y_2655_, v___y_2656_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec_ref(v_n_2653_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg(lean_object* v_as_2659_, size_t v_sz_2660_, size_t v_i_2661_, lean_object* v_b_2662_, lean_object* v___y_2663_){
_start:
{
uint8_t v___x_2665_; 
v___x_2665_ = lean_usize_dec_lt(v_i_2661_, v_sz_2660_);
if (v___x_2665_ == 0)
{
lean_object* v___x_2666_; 
v___x_2666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2666_, 0, v_b_2662_);
return v___x_2666_;
}
else
{
uint8_t v___x_2667_; lean_object* v_a_2668_; lean_object* v___x_2669_; lean_object* v_ref_2670_; lean_object* v___x_2671_; 
lean_dec_ref(v_b_2662_);
v___x_2667_ = 0;
v_a_2668_ = lean_array_uget_borrowed(v_as_2659_, v_i_2661_);
lean_inc(v_a_2668_);
v___x_2669_ = l_Lean_Message_toString(v_a_2668_, v___x_2667_);
v_ref_2670_ = lean_ctor_get(v___y_2663_, 2);
v___x_2671_ = l_IO_eprintln___at___00main_spec__6(v___x_2669_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v___x_2672_; size_t v___x_2673_; size_t v___x_2674_; 
lean_dec_ref_known(v___x_2671_, 1);
v___x_2672_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___closed__0));
v___x_2673_ = ((size_t)1ULL);
v___x_2674_ = lean_usize_add(v_i_2661_, v___x_2673_);
v_i_2661_ = v___x_2674_;
v_b_2662_ = v___x_2672_;
goto _start;
}
else
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2687_; 
v_a_2676_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2678_ = v___x_2671_;
v_isShared_2679_ = v_isSharedCheck_2687_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2671_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2687_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2685_; 
v___x_2680_ = lean_io_error_to_string(v_a_2676_);
v___x_2681_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2680_);
v___x_2682_ = l_Lean_MessageData_ofFormat(v___x_2681_);
lean_inc(v_ref_2670_);
v___x_2683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2683_, 0, v_ref_2670_);
lean_ctor_set(v___x_2683_, 1, v___x_2682_);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 0, v___x_2683_);
v___x_2685_ = v___x_2678_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v___x_2683_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg___boxed(lean_object* v_as_2688_, lean_object* v_sz_2689_, lean_object* v_i_2690_, lean_object* v_b_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_){
_start:
{
size_t v_sz_boxed_2694_; size_t v_i_boxed_2695_; lean_object* v_res_2696_; 
v_sz_boxed_2694_ = lean_unbox_usize(v_sz_2689_);
lean_dec(v_sz_2689_);
v_i_boxed_2695_ = lean_unbox_usize(v_i_2690_);
lean_dec(v_i_2690_);
v_res_2696_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg(v_as_2688_, v_sz_boxed_2694_, v_i_boxed_2695_, v_b_2691_, v___y_2692_);
lean_dec_ref(v___y_2692_);
lean_dec_ref(v_as_2688_);
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27(lean_object* v_as_2697_, size_t v_sz_2698_, size_t v_i_2699_, lean_object* v_b_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_){
_start:
{
uint8_t v___x_2704_; 
v___x_2704_ = lean_usize_dec_lt(v_i_2699_, v_sz_2698_);
if (v___x_2704_ == 0)
{
lean_object* v___x_2705_; 
v___x_2705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2705_, 0, v_b_2700_);
return v___x_2705_;
}
else
{
uint8_t v___x_2706_; lean_object* v_a_2707_; lean_object* v___x_2708_; lean_object* v_ref_2709_; lean_object* v___x_2710_; 
lean_dec_ref(v_b_2700_);
v___x_2706_ = 0;
v_a_2707_ = lean_array_uget_borrowed(v_as_2697_, v_i_2699_);
lean_inc(v_a_2707_);
v___x_2708_ = l_Lean_Message_toString(v_a_2707_, v___x_2706_);
v_ref_2709_ = lean_ctor_get(v___y_2701_, 2);
v___x_2710_ = l_IO_eprintln___at___00main_spec__6(v___x_2708_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v___x_2711_; size_t v___x_2712_; size_t v___x_2713_; lean_object* v___x_2714_; 
lean_dec_ref_known(v___x_2710_, 1);
v___x_2711_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___closed__0));
v___x_2712_ = ((size_t)1ULL);
v___x_2713_ = lean_usize_add(v_i_2699_, v___x_2712_);
v___x_2714_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg(v_as_2697_, v_sz_2698_, v___x_2713_, v___x_2711_, v___y_2701_);
return v___x_2714_;
}
else
{
lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2726_; 
v_a_2715_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2717_ = v___x_2710_;
v_isShared_2718_ = v_isSharedCheck_2726_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v___x_2710_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2726_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2724_; 
v___x_2719_ = lean_io_error_to_string(v_a_2715_);
v___x_2720_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2719_);
v___x_2721_ = l_Lean_MessageData_ofFormat(v___x_2720_);
lean_inc(v_ref_2709_);
v___x_2722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2722_, 0, v_ref_2709_);
lean_ctor_set(v___x_2722_, 1, v___x_2721_);
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 0, v___x_2722_);
v___x_2724_ = v___x_2717_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2722_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27___boxed(lean_object* v_as_2727_, lean_object* v_sz_2728_, lean_object* v_i_2729_, lean_object* v_b_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
size_t v_sz_boxed_2734_; size_t v_i_boxed_2735_; lean_object* v_res_2736_; 
v_sz_boxed_2734_ = lean_unbox_usize(v_sz_2728_);
lean_dec(v_sz_2728_);
v_i_boxed_2735_ = lean_unbox_usize(v_i_2729_);
lean_dec(v_i_2729_);
v_res_2736_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27(v_as_2727_, v_sz_boxed_2734_, v_i_boxed_2735_, v_b_2730_, v___y_2731_, v___y_2732_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec_ref(v_as_2727_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__11(lean_object* v_t_2737_, lean_object* v_init_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v_root_2742_; lean_object* v_tail_2743_; lean_object* v___x_2744_; 
v_root_2742_ = lean_ctor_get(v_t_2737_, 0);
v_tail_2743_ = lean_ctor_get(v_t_2737_, 1);
v___x_2744_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26(v_init_2738_, v_root_2742_, v_init_2738_, v___y_2739_, v___y_2740_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2781_; 
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2747_ = v___x_2744_;
v_isShared_2748_ = v_isSharedCheck_2781_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_dec(v___x_2744_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2781_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
if (lean_obj_tag(v_a_2745_) == 0)
{
lean_object* v_a_2749_; lean_object* v___x_2751_; 
v_a_2749_ = lean_ctor_get(v_a_2745_, 0);
lean_inc(v_a_2749_);
lean_dec_ref_known(v_a_2745_, 1);
if (v_isShared_2748_ == 0)
{
lean_ctor_set(v___x_2747_, 0, v_a_2749_);
v___x_2751_ = v___x_2747_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_a_2749_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
else
{
lean_object* v_a_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; size_t v_sz_2756_; size_t v___x_2757_; lean_object* v___x_2758_; 
lean_del_object(v___x_2747_);
v_a_2753_ = lean_ctor_get(v_a_2745_, 0);
lean_inc(v_a_2753_);
lean_dec_ref_known(v_a_2745_, 1);
v___x_2754_ = lean_box(0);
v___x_2755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2754_);
lean_ctor_set(v___x_2755_, 1, v_a_2753_);
v_sz_2756_ = lean_array_size(v_tail_2743_);
v___x_2757_ = ((size_t)0ULL);
v___x_2758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27(v_tail_2743_, v_sz_2756_, v___x_2757_, v___x_2755_, v___y_2739_, v___y_2740_);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v_a_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2772_; 
v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2761_ = v___x_2758_;
v_isShared_2762_ = v_isSharedCheck_2772_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_a_2759_);
lean_dec(v___x_2758_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2772_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v_fst_2763_; 
v_fst_2763_ = lean_ctor_get(v_a_2759_, 0);
if (lean_obj_tag(v_fst_2763_) == 0)
{
lean_object* v_snd_2764_; lean_object* v___x_2766_; 
v_snd_2764_ = lean_ctor_get(v_a_2759_, 1);
lean_inc(v_snd_2764_);
lean_dec(v_a_2759_);
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 0, v_snd_2764_);
v___x_2766_ = v___x_2761_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_snd_2764_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
else
{
lean_object* v_val_2768_; lean_object* v___x_2770_; 
lean_inc_ref(v_fst_2763_);
lean_dec(v_a_2759_);
v_val_2768_ = lean_ctor_get(v_fst_2763_, 0);
lean_inc(v_val_2768_);
lean_dec_ref_known(v_fst_2763_, 1);
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 0, v_val_2768_);
v___x_2770_ = v___x_2761_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_val_2768_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
}
}
else
{
lean_object* v_a_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2780_; 
v_a_2773_ = lean_ctor_get(v___x_2758_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2775_ = v___x_2758_;
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_a_2773_);
lean_dec(v___x_2758_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2778_; 
if (v_isShared_2776_ == 0)
{
v___x_2778_ = v___x_2775_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_a_2773_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
}
}
}
else
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
v_a_2782_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2744_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2744_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__11___boxed(lean_object* v_t_2790_, lean_object* v_init_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l_Lean_PersistentArray_forIn___at___00main_spec__11(v_t_2790_, v_init_2791_, v___y_2792_, v___y_2793_);
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
lean_dec_ref(v_t_2790_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(lean_object* v_as_2796_, size_t v_sz_2797_, size_t v_i_2798_, lean_object* v_b_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
uint8_t v___x_2803_; 
v___x_2803_ = lean_usize_dec_lt(v_i_2798_, v_sz_2797_);
if (v___x_2803_ == 0)
{
lean_object* v___x_2804_; 
v___x_2804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2804_, 0, v_b_2799_);
return v___x_2804_;
}
else
{
lean_object* v_a_2805_; lean_object* v_declNames_2806_; lean_object* v___x_2807_; size_t v_sz_2808_; size_t v___x_2809_; lean_object* v___x_2810_; 
v_a_2805_ = lean_array_uget_borrowed(v_as_2796_, v_i_2798_);
v_declNames_2806_ = lean_ctor_get(v_a_2805_, 0);
v___x_2807_ = lean_box(0);
v_sz_2808_ = lean_array_size(v_declNames_2806_);
v___x_2809_ = ((size_t)0ULL);
v___x_2810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10(v_declNames_2806_, v_sz_2808_, v___x_2809_, v___x_2807_, v___y_2800_, v___y_2801_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v___x_2811_; 
lean_dec_ref_known(v___x_2810_, 1);
v___x_2811_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v___y_2801_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; lean_object* v_unreported_2813_; lean_object* v___x_2814_; 
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
lean_inc(v_a_2812_);
lean_dec_ref_known(v___x_2811_, 1);
v_unreported_2813_ = lean_ctor_get(v_a_2812_, 1);
lean_inc_ref(v_unreported_2813_);
lean_dec(v_a_2812_);
v___x_2814_ = l_Lean_PersistentArray_forIn___at___00main_spec__11(v_unreported_2813_, v___x_2807_, v___y_2800_, v___y_2801_);
lean_dec_ref(v_unreported_2813_);
if (lean_obj_tag(v___x_2814_) == 0)
{
size_t v___x_2815_; size_t v___x_2816_; 
lean_dec_ref_known(v___x_2814_, 1);
v___x_2815_ = ((size_t)1ULL);
v___x_2816_ = lean_usize_add(v_i_2798_, v___x_2815_);
v_i_2798_ = v___x_2816_;
v_b_2799_ = v___x_2807_;
goto _start;
}
else
{
return v___x_2814_;
}
}
else
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
v_a_2818_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2820_ = v___x_2811_;
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2811_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2823_; 
if (v_isShared_2821_ == 0)
{
v___x_2823_ = v___x_2820_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_a_2818_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
}
else
{
return v___x_2810_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___boxed(lean_object* v_as_2826_, lean_object* v_sz_2827_, lean_object* v_i_2828_, lean_object* v_b_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
size_t v_sz_boxed_2833_; size_t v_i_boxed_2834_; lean_object* v_res_2835_; 
v_sz_boxed_2833_ = lean_unbox_usize(v_sz_2827_);
lean_dec(v_sz_2827_);
v_i_boxed_2834_ = lean_unbox_usize(v_i_2828_);
lean_dec(v_i_2828_);
v_res_2835_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(v_as_2826_, v_sz_boxed_2833_, v_i_boxed_2834_, v_b_2829_, v___y_2830_, v___y_2831_);
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
lean_dec_ref(v_as_2826_);
return v_res_2835_;
}
}
static lean_object* _init_l_main___closed__1(void){
_start:
{
lean_object* v___x_2837_; 
v___x_2837_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg();
return v___x_2837_;
}
}
static lean_object* _init_l_main___closed__2(void){
_start:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2838_ = l_Lean_instInhabitedClassState_default;
v___x_2839_ = lean_box(0);
v___x_2840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2839_);
lean_ctor_set(v___x_2840_, 1, v___x_2838_);
return v___x_2840_;
}
}
static lean_object* _init_l_main___closed__3(void){
_start:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; 
v___x_2841_ = l_Lean_Meta_Match_Extension_instInhabitedState;
v___x_2842_ = lean_box(0);
v___x_2843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2842_);
lean_ctor_set(v___x_2843_, 1, v___x_2841_);
return v___x_2843_;
}
}
static lean_object* _init_l_main___closed__4(void){
_start:
{
lean_object* v___x_2844_; 
v___x_2844_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v___x_2844_;
}
}
static lean_object* _init_l_main___closed__5(void){
_start:
{
lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2845_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_2846_ = lean_box(0);
v___x_2847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2846_);
lean_ctor_set(v___x_2847_, 1, v___x_2845_);
return v___x_2847_;
}
}
static lean_object* _init_l_main___closed__6(void){
_start:
{
lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2848_ = lean_obj_once(&l_main___closed__5, &l_main___closed__5_once, _init_l_main___closed__5);
v___x_2849_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2848_);
return v___x_2849_;
}
}
static lean_object* _init_l_main___closed__7(void){
_start:
{
lean_object* v___x_2850_; 
v___x_2850_ = l_Array_instInhabited___redArg();
return v___x_2850_;
}
}
static lean_object* _init_l_main___closed__17(void){
_start:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2863_ = ((lean_object*)(l_main___closed__16));
v___x_2864_ = lean_unsigned_to_nat(27u);
v___x_2865_ = lean_unsigned_to_nat(151u);
v___x_2866_ = ((lean_object*)(l_main___closed__15));
v___x_2867_ = ((lean_object*)(l_main___closed__14));
v___x_2868_ = l_mkPanicMessageWithDecl(v___x_2867_, v___x_2866_, v___x_2865_, v___x_2864_, v___x_2863_);
return v___x_2868_;
}
}
static lean_object* _init_l_main___closed__19(void){
_start:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2870_ = ((lean_object*)(l_main___closed__16));
v___x_2871_ = lean_unsigned_to_nat(51u);
v___x_2872_ = lean_unsigned_to_nat(124u);
v___x_2873_ = ((lean_object*)(l_main___closed__15));
v___x_2874_ = ((lean_object*)(l_main___closed__14));
v___x_2875_ = l_mkPanicMessageWithDecl(v___x_2874_, v___x_2873_, v___x_2872_, v___x_2871_, v___x_2870_);
return v___x_2875_;
}
}
static lean_object* _init_l_main___closed__20(void){
_start:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2876_ = lean_unsigned_to_nat(1u);
v___x_2877_ = l_Lean_firstFrontendMacroScope;
v___x_2878_ = lean_nat_add(v___x_2877_, v___x_2876_);
return v___x_2878_;
}
}
static lean_object* _init_l_main___closed__24(void){
_start:
{
lean_object* v___x_2885_; uint64_t v___x_2886_; lean_object* v___x_2887_; 
v___x_2885_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1);
v___x_2886_ = 0ULL;
v___x_2887_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2887_, 0, v___x_2885_);
lean_ctor_set_uint64(v___x_2887_, sizeof(void*)*1, v___x_2886_);
return v___x_2887_;
}
}
static lean_object* _init_l_main___closed__25(void){
_start:
{
lean_object* v___x_2888_; 
v___x_2888_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2888_;
}
}
static lean_object* _init_l_main___closed__26(void){
_start:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2889_ = lean_obj_once(&l_main___closed__25, &l_main___closed__25_once, _init_l_main___closed__25);
v___x_2890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2889_);
return v___x_2890_;
}
}
static lean_object* _init_l_main___closed__27(void){
_start:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; 
v___x_2891_ = lean_obj_once(&l_main___closed__26, &l_main___closed__26_once, _init_l_main___closed__26);
v___x_2892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2891_);
lean_ctor_set(v___x_2892_, 1, v___x_2891_);
return v___x_2892_;
}
}
static lean_object* _init_l_main___closed__29(void){
_start:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2895_ = lean_unsigned_to_nat(0u);
v___x_2896_ = l_Lean_Options_empty;
v___x_2897_ = ((lean_object*)(l_main___closed__28));
v___x_2898_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2897_);
lean_ctor_set(v___x_2898_, 1, v___x_2896_);
lean_ctor_set(v___x_2898_, 2, v___x_2897_);
lean_ctor_set(v___x_2898_, 3, v___x_2895_);
return v___x_2898_;
}
}
static lean_object* _init_l_main___closed__30(void){
_start:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2899_ = l_Lean_NameSet_empty;
v___x_2900_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1);
v___x_2901_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2900_);
lean_ctor_set(v___x_2901_, 1, v___x_2900_);
lean_ctor_set(v___x_2901_, 2, v___x_2899_);
return v___x_2901_;
}
}
static lean_object* _init_l_main___closed__31(void){
_start:
{
lean_object* v___x_2902_; lean_object* v___x_2903_; uint8_t v___x_2904_; lean_object* v___x_2905_; 
v___x_2902_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1);
v___x_2903_ = lean_obj_once(&l_main___closed__26, &l_main___closed__26_once, _init_l_main___closed__26);
v___x_2904_ = 1;
v___x_2905_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2905_, 0, v___x_2903_);
lean_ctor_set(v___x_2905_, 1, v___x_2903_);
lean_ctor_set(v___x_2905_, 2, v___x_2902_);
lean_ctor_set_uint8(v___x_2905_, sizeof(void*)*3, v___x_2904_);
return v___x_2905_;
}
}
static uint8_t _init_l_main___closed__35(void){
_start:
{
uint8_t v___x_2910_; uint8_t v___x_2911_; uint8_t v___x_2912_; 
v___x_2910_ = 2;
v___x_2911_ = 0;
v___x_2912_ = l_Lean_instOrdOLeanLevel_ord(v___x_2911_, v___x_2910_);
return v___x_2912_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_2913_; lean_object* v___x_2914_; 
v___x_2913_ = 0;
v___x_2914_ = lean_box_uint32(v___x_2913_);
return v___x_2914_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_2915_; lean_object* v___x_2916_; 
v___x_2915_ = 1;
v___x_2916_ = lean_box_uint32(v___x_2915_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_2917_){
_start:
{
if (lean_obj_tag(v_args_2917_) == 1)
{
lean_object* v_tail_2942_; 
v_tail_2942_ = lean_ctor_get(v_args_2917_, 1);
lean_inc(v_tail_2942_);
if (lean_obj_tag(v_tail_2942_) == 1)
{
lean_object* v_tail_2943_; 
v_tail_2943_ = lean_ctor_get(v_tail_2942_, 1);
lean_inc(v_tail_2943_);
if (lean_obj_tag(v_tail_2943_) == 1)
{
lean_object* v_head_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_3677_; 
v_head_2944_ = lean_ctor_get(v_args_2917_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v_args_2917_);
if (v_isSharedCheck_3677_ == 0)
{
lean_object* v_unused_3678_; 
v_unused_3678_ = lean_ctor_get(v_args_2917_, 1);
lean_dec(v_unused_3678_);
v___x_2946_ = v_args_2917_;
v_isShared_2947_ = v_isSharedCheck_3677_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_head_2944_);
lean_dec(v_args_2917_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_3677_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v_head_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_3675_; 
v_head_2948_ = lean_ctor_get(v_tail_2942_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v_tail_2942_);
if (v_isSharedCheck_3675_ == 0)
{
lean_object* v_unused_3676_; 
v_unused_3676_ = lean_ctor_get(v_tail_2942_, 1);
lean_dec(v_unused_3676_);
v___x_2950_ = v_tail_2942_;
v_isShared_2951_ = v_isSharedCheck_3675_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_head_2948_);
lean_dec(v_tail_2942_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_3675_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v_head_2952_; lean_object* v_tail_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_3674_; 
v_head_2952_ = lean_ctor_get(v_tail_2943_, 0);
v_tail_2953_ = lean_ctor_get(v_tail_2943_, 1);
v_isSharedCheck_3674_ = !lean_is_exclusive(v_tail_2943_);
if (v_isSharedCheck_3674_ == 0)
{
v___x_2955_ = v_tail_2943_;
v_isShared_2956_ = v_isSharedCheck_3674_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_tail_2953_);
lean_inc(v_head_2952_);
lean_dec(v_tail_2943_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_3674_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2957_ = lean_obj_once(&l_main___closed__1, &l_main___closed__1_once, _init_l_main___closed__1);
v___x_2958_ = lean_box(0);
v___x_2959_ = lean_obj_once(&l_main___closed__2, &l_main___closed__2_once, _init_l_main___closed__2);
v___x_2960_ = lean_obj_once(&l_main___closed__3, &l_main___closed__3_once, _init_l_main___closed__3);
v___x_2961_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_2962_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_2963_ = lean_obj_once(&l_main___closed__7, &l_main___closed__7_once, _init_l_main___closed__7);
v___x_2964_ = lean_box(1);
v___x_2965_ = ((lean_object*)(l_main___closed__8));
v___x_2966_ = l_Lean_ModuleSetup_load(v_head_2944_);
lean_dec(v_head_2944_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v_a_2967_; lean_object* v_name_2968_; lean_object* v_package_x3f_2969_; lean_object* v_importArts_2970_; lean_object* v_options_2971_; uint8_t v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2976_; 
v_a_2967_ = lean_ctor_get(v___x_2966_, 0);
lean_inc(v_a_2967_);
lean_dec_ref_known(v___x_2966_, 1);
v_name_2968_ = lean_ctor_get(v_a_2967_, 0);
lean_inc(v_name_2968_);
v_package_x3f_2969_ = lean_ctor_get(v_a_2967_, 1);
lean_inc(v_package_x3f_2969_);
v_importArts_2970_ = lean_ctor_get(v_a_2967_, 3);
lean_inc(v_importArts_2970_);
v_options_2971_ = lean_ctor_get(v_a_2967_, 6);
lean_inc(v_options_2971_);
lean_dec(v_a_2967_);
v___x_2972_ = 0;
v___x_2973_ = l_Lean_LeanOptions_toOptions(v_options_2971_);
v___x_2974_ = lean_box(v___x_2972_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set_tag(v___x_2955_, 0);
lean_ctor_set(v___x_2955_, 1, v___x_2973_);
lean_ctor_set(v___x_2955_, 0, v___x_2974_);
v___x_2976_ = v___x_2955_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v___x_2974_);
lean_ctor_set(v_reuseFailAlloc_3665_, 1, v___x_2973_);
v___x_2976_ = v_reuseFailAlloc_3665_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
lean_object* v___x_2977_; 
v___x_2977_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_tail_2953_, v___x_2976_);
lean_dec(v_tail_2953_);
if (lean_obj_tag(v___x_2977_) == 0)
{
lean_object* v_a_2978_; lean_object* v_fst_2979_; lean_object* v_snd_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_3656_; 
v_a_2978_ = lean_ctor_get(v___x_2977_, 0);
lean_inc(v_a_2978_);
lean_dec_ref_known(v___x_2977_, 1);
v_fst_2979_ = lean_ctor_get(v_a_2978_, 0);
v_snd_2980_ = lean_ctor_get(v_a_2978_, 1);
v_isSharedCheck_3656_ = !lean_is_exclusive(v_a_2978_);
if (v_isSharedCheck_3656_ == 0)
{
v___x_2982_ = v_a_2978_;
v_isShared_2983_ = v_isSharedCheck_3656_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_snd_2980_);
lean_inc(v_fst_2979_);
lean_dec(v_a_2978_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_3656_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2984_; uint8_t v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___y_2991_; uint8_t v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; uint8_t v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v_nextMacroScope_3160_; lean_object* v_ngen_3161_; lean_object* v_auxDeclNGen_3162_; lean_object* v_traceState_3163_; lean_object* v_recordedDeps_3164_; lean_object* v_messages_3165_; lean_object* v_infoState_3166_; lean_object* v_snapshotTasks_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3195_; uint8_t v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; uint16_t v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; uint8_t v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; uint16_t v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; uint8_t v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3325_; uint8_t v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; uint16_t v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; uint8_t v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; uint8_t v___y_3351_; uint16_t v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; uint8_t v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; uint8_t v___y_3374_; uint8_t v___y_3375_; lean_object* v___y_3376_; lean_object* v___y_3377_; uint8_t v___y_3378_; lean_object* v___x_3379_; 
v___x_2984_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_2985_ = 1;
v___x_2986_ = l_Lean_Option_set___at___00Lean_Environment_realizeConst_spec__0(v_snd_2980_, v___x_2984_, v___x_2985_);
v___x_2987_ = l_Lean_maxHeartbeats;
v___x_2988_ = lean_unsigned_to_nat(0u);
v___x_2989_ = l_Lean_Option_set___at___00main_spec__3(v___x_2986_, v___x_2987_, v___x_2988_);
v___x_3379_ = lean_init_search_path();
if (lean_obj_tag(v___x_3379_) == 0)
{
lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; uint8_t v___x_3385_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; uint8_t v___x_3549_; uint8_t v___y_3551_; uint8_t v___x_3647_; 
lean_dec_ref_known(v___x_3379_, 1);
v___x_3380_ = ((lean_object*)(l_main___closed__18));
lean_inc(v_name_2968_);
v___x_3381_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_3381_, 0, v_name_2968_);
lean_ctor_set_uint8(v___x_3381_, sizeof(void*)*1, v___x_2985_);
lean_ctor_set_uint8(v___x_3381_, sizeof(void*)*1 + 1, v___x_2985_);
lean_ctor_set_uint8(v___x_3381_, sizeof(void*)*1 + 2, v___x_2972_);
v___x_3382_ = lean_unsigned_to_nat(1u);
v___x_3383_ = lean_mk_empty_array_with_capacity(v___x_3382_);
v___x_3384_ = lean_array_push(v___x_3383_, v___x_3381_);
v___x_3385_ = 0;
v___x_3549_ = 2;
v___x_3647_ = lean_uint8_once(&l_main___closed__35, &l_main___closed__35_once, _init_l_main___closed__35);
if (v___x_3647_ == 0)
{
v___y_3551_ = v___x_2985_;
goto v___jp_3550_;
}
else
{
v___y_3551_ = v___x_2972_;
goto v___jp_3550_;
}
v___jp_3386_:
{
lean_object* v___x_3395_; 
if (v_isShared_2947_ == 0)
{
lean_ctor_set_tag(v___x_2946_, 0);
lean_ctor_set(v___x_2946_, 1, v___y_3393_);
lean_ctor_set(v___x_2946_, 0, v___y_3390_);
v___x_3395_ = v___x_2946_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v___y_3390_);
lean_ctor_set(v_reuseFailAlloc_3498_, 1, v___y_3393_);
v___x_3395_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v_moduleData_3399_; lean_object* v___x_3400_; uint8_t v___x_3401_; 
v___x_3396_ = lean_box(0);
lean_inc_ref(v___y_3388_);
v___x_3397_ = l_Lean_EnvExtension_setState___redArg(v___y_3388_, v___y_3389_, v___x_3395_, v___x_3396_);
v___x_3398_ = l_Lean_Environment_header(v___x_3397_);
v_moduleData_3399_ = lean_ctor_get(v___x_3398_, 6);
lean_inc_ref(v_moduleData_3399_);
lean_dec_ref(v___x_3398_);
v___x_3400_ = lean_array_get_size(v_moduleData_3399_);
v___x_3401_ = lean_nat_dec_lt(v___y_3392_, v___x_3400_);
if (v___x_3401_ == 0)
{
lean_object* v___x_3402_; lean_object* v___x_3403_; 
lean_dec_ref(v_moduleData_3399_);
lean_dec_ref(v___x_3397_);
lean_dec(v___y_3392_);
lean_dec(v___y_3391_);
lean_dec(v___y_3387_);
lean_dec_ref(v___x_2989_);
lean_del_object(v___x_2982_);
lean_dec(v_fst_2979_);
lean_dec(v_name_2968_);
lean_dec(v_head_2952_);
lean_del_object(v___x_2950_);
lean_dec(v_head_2948_);
v___x_3402_ = lean_obj_once(&l_main___closed__19, &l_main___closed__19_once, _init_l_main___closed__19);
v___x_3403_ = l_panic___at___00main_spec__5(v___x_3402_);
return v___x_3403_;
}
else
{
lean_object* v_base_3404_; lean_object* v_private_3405_; lean_object* v_header_3406_; lean_object* v_serverBaseExts_3407_; lean_object* v_checked_3408_; lean_object* v_asyncConstsMap_3409_; lean_object* v_asyncCtx_x3f_3410_; lean_object* v_importRealizationCtx_x3f_3411_; lean_object* v_localRealizationCtxMap_3412_; lean_object* v_allRealizations_3413_; uint8_t v_isExporting_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3496_; 
v_base_3404_ = lean_ctor_get(v___x_3397_, 0);
lean_inc_ref(v_base_3404_);
v_private_3405_ = lean_ctor_get(v_base_3404_, 0);
lean_inc(v_private_3405_);
v_header_3406_ = lean_ctor_get(v_private_3405_, 7);
lean_inc_ref(v_header_3406_);
v_serverBaseExts_3407_ = lean_ctor_get(v___x_3397_, 1);
v_checked_3408_ = lean_ctor_get(v___x_3397_, 2);
v_asyncConstsMap_3409_ = lean_ctor_get(v___x_3397_, 3);
v_asyncCtx_x3f_3410_ = lean_ctor_get(v___x_3397_, 4);
v_importRealizationCtx_x3f_3411_ = lean_ctor_get(v___x_3397_, 5);
v_localRealizationCtxMap_3412_ = lean_ctor_get(v___x_3397_, 6);
v_allRealizations_3413_ = lean_ctor_get(v___x_3397_, 7);
v_isExporting_3414_ = lean_ctor_get_uint8(v___x_3397_, sizeof(void*)*8);
v_isSharedCheck_3496_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3496_ == 0)
{
lean_object* v_unused_3497_; 
v_unused_3497_ = lean_ctor_get(v___x_3397_, 0);
lean_dec(v_unused_3497_);
v___x_3416_ = v___x_3397_;
v_isShared_3417_ = v_isSharedCheck_3496_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_allRealizations_3413_);
lean_inc(v_localRealizationCtxMap_3412_);
lean_inc(v_importRealizationCtx_x3f_3411_);
lean_inc(v_asyncCtx_x3f_3410_);
lean_inc(v_asyncConstsMap_3409_);
lean_inc(v_checked_3408_);
lean_inc(v_serverBaseExts_3407_);
lean_dec(v___x_3397_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3496_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v_public_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3494_; 
v_public_3418_ = lean_ctor_get(v_base_3404_, 1);
v_isSharedCheck_3494_ = !lean_is_exclusive(v_base_3404_);
if (v_isSharedCheck_3494_ == 0)
{
lean_object* v_unused_3495_; 
v_unused_3495_ = lean_ctor_get(v_base_3404_, 0);
lean_dec(v_unused_3495_);
v___x_3420_ = v_base_3404_;
v_isShared_3421_ = v_isSharedCheck_3494_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_public_3418_);
lean_dec(v_base_3404_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3494_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v_constants_3422_; uint8_t v_quotInit_3423_; lean_object* v_diagnostics_3424_; lean_object* v_const2ModIdx_3425_; lean_object* v_extensions_3426_; lean_object* v_irBaseExts_3427_; lean_object* v_extGens_3428_; lean_object* v_trackedGen_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3492_; 
v_constants_3422_ = lean_ctor_get(v_private_3405_, 0);
v_quotInit_3423_ = lean_ctor_get_uint8(v_private_3405_, sizeof(void*)*8);
v_diagnostics_3424_ = lean_ctor_get(v_private_3405_, 1);
v_const2ModIdx_3425_ = lean_ctor_get(v_private_3405_, 2);
v_extensions_3426_ = lean_ctor_get(v_private_3405_, 3);
v_irBaseExts_3427_ = lean_ctor_get(v_private_3405_, 4);
v_extGens_3428_ = lean_ctor_get(v_private_3405_, 5);
v_trackedGen_3429_ = lean_ctor_get(v_private_3405_, 6);
v_isSharedCheck_3492_ = !lean_is_exclusive(v_private_3405_);
if (v_isSharedCheck_3492_ == 0)
{
lean_object* v_unused_3493_; 
v_unused_3493_ = lean_ctor_get(v_private_3405_, 7);
lean_dec(v_unused_3493_);
v___x_3431_ = v_private_3405_;
v_isShared_3432_ = v_isSharedCheck_3492_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_trackedGen_3429_);
lean_inc(v_extGens_3428_);
lean_inc(v_irBaseExts_3427_);
lean_inc(v_extensions_3426_);
lean_inc(v_const2ModIdx_3425_);
lean_inc(v_diagnostics_3424_);
lean_inc(v_constants_3422_);
lean_dec(v_private_3405_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3492_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
uint32_t v_trustLevel_3433_; lean_object* v_mainModule_3434_; uint8_t v_isModule_3435_; lean_object* v_regions_3436_; lean_object* v_modules_3437_; lean_object* v_moduleName2Idx_3438_; lean_object* v_importAllModules_3439_; lean_object* v_moduleData_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3490_; 
v_trustLevel_3433_ = lean_ctor_get_uint32(v_header_3406_, sizeof(void*)*7);
v_mainModule_3434_ = lean_ctor_get(v_header_3406_, 0);
v_isModule_3435_ = lean_ctor_get_uint8(v_header_3406_, sizeof(void*)*7 + 4);
v_regions_3436_ = lean_ctor_get(v_header_3406_, 2);
v_modules_3437_ = lean_ctor_get(v_header_3406_, 3);
v_moduleName2Idx_3438_ = lean_ctor_get(v_header_3406_, 4);
v_importAllModules_3439_ = lean_ctor_get(v_header_3406_, 5);
v_moduleData_3440_ = lean_ctor_get(v_header_3406_, 6);
v_isSharedCheck_3490_ = !lean_is_exclusive(v_header_3406_);
if (v_isSharedCheck_3490_ == 0)
{
lean_object* v_unused_3491_; 
v_unused_3491_ = lean_ctor_get(v_header_3406_, 1);
lean_dec(v_unused_3491_);
v___x_3442_ = v_header_3406_;
v_isShared_3443_ = v_isSharedCheck_3490_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_moduleData_3440_);
lean_inc(v_importAllModules_3439_);
lean_inc(v_moduleName2Idx_3438_);
lean_inc(v_modules_3437_);
lean_inc(v_regions_3436_);
lean_inc(v_mainModule_3434_);
lean_dec(v_header_3406_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3490_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3444_; lean_object* v_imports_3445_; lean_object* v___x_3447_; 
v___x_3444_ = lean_array_fget(v_moduleData_3399_, v___y_3392_);
lean_dec_ref(v_moduleData_3399_);
v_imports_3445_ = lean_ctor_get(v___x_3444_, 0);
lean_inc_ref(v_imports_3445_);
lean_dec(v___x_3444_);
if (v_isShared_3443_ == 0)
{
lean_ctor_set(v___x_3442_, 1, v_imports_3445_);
v___x_3447_ = v___x_3442_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(0, 7, 5);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_mainModule_3434_);
lean_ctor_set(v_reuseFailAlloc_3489_, 1, v_imports_3445_);
lean_ctor_set(v_reuseFailAlloc_3489_, 2, v_regions_3436_);
lean_ctor_set(v_reuseFailAlloc_3489_, 3, v_modules_3437_);
lean_ctor_set(v_reuseFailAlloc_3489_, 4, v_moduleName2Idx_3438_);
lean_ctor_set(v_reuseFailAlloc_3489_, 5, v_importAllModules_3439_);
lean_ctor_set(v_reuseFailAlloc_3489_, 6, v_moduleData_3440_);
lean_ctor_set_uint32(v_reuseFailAlloc_3489_, sizeof(void*)*7, v_trustLevel_3433_);
lean_ctor_set_uint8(v_reuseFailAlloc_3489_, sizeof(void*)*7 + 4, v_isModule_3435_);
v___x_3447_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
lean_object* v___x_3449_; 
if (v_isShared_3432_ == 0)
{
lean_ctor_set(v___x_3431_, 7, v___x_3447_);
v___x_3449_ = v___x_3431_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_constants_3422_);
lean_ctor_set(v_reuseFailAlloc_3488_, 1, v_diagnostics_3424_);
lean_ctor_set(v_reuseFailAlloc_3488_, 2, v_const2ModIdx_3425_);
lean_ctor_set(v_reuseFailAlloc_3488_, 3, v_extensions_3426_);
lean_ctor_set(v_reuseFailAlloc_3488_, 4, v_irBaseExts_3427_);
lean_ctor_set(v_reuseFailAlloc_3488_, 5, v_extGens_3428_);
lean_ctor_set(v_reuseFailAlloc_3488_, 6, v_trackedGen_3429_);
lean_ctor_set(v_reuseFailAlloc_3488_, 7, v___x_3447_);
lean_ctor_set_uint8(v_reuseFailAlloc_3488_, sizeof(void*)*8, v_quotInit_3423_);
v___x_3449_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
lean_object* v___x_3451_; 
if (v_isShared_3421_ == 0)
{
lean_ctor_set(v___x_3420_, 0, v___x_3449_);
v___x_3451_ = v___x_3420_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v___x_3449_);
lean_ctor_set(v_reuseFailAlloc_3487_, 1, v_public_3418_);
v___x_3451_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
lean_object* v___x_3453_; 
if (v_isShared_3417_ == 0)
{
lean_ctor_set(v___x_3416_, 0, v___x_3451_);
v___x_3453_ = v___x_3416_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v___x_3451_);
lean_ctor_set(v_reuseFailAlloc_3486_, 1, v_serverBaseExts_3407_);
lean_ctor_set(v_reuseFailAlloc_3486_, 2, v_checked_3408_);
lean_ctor_set(v_reuseFailAlloc_3486_, 3, v_asyncConstsMap_3409_);
lean_ctor_set(v_reuseFailAlloc_3486_, 4, v_asyncCtx_x3f_3410_);
lean_ctor_set(v_reuseFailAlloc_3486_, 5, v_importRealizationCtx_x3f_3411_);
lean_ctor_set(v_reuseFailAlloc_3486_, 6, v_localRealizationCtxMap_3412_);
lean_ctor_set(v_reuseFailAlloc_3486_, 7, v_allRealizations_3413_);
lean_ctor_set_uint8(v_reuseFailAlloc_3486_, sizeof(void*)*8, v_isExporting_3414_);
v___x_3453_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; uint16_t v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v_env_3480_; uint8_t v___x_3481_; uint16_t v___x_3482_; uint16_t v___x_3483_; uint16_t v___x_3484_; uint8_t v___x_3485_; 
v___x_3454_ = l_Lean_Compiler_LCNF_postponedCompileDeclsExt;
v___x_3455_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2965_, v___x_3454_, v___x_3453_, v___y_3392_, v___x_3385_);
lean_dec(v___y_3392_);
v___x_3456_ = l_Lean_instInhabitedFileMap_default;
v___x_3457_ = lean_unsigned_to_nat(1000u);
v___x_3458_ = l_Lean_Core_getMaxHeartbeats(v___x_2989_);
v___x_3459_ = l_Lean_firstFrontendMacroScope;
v___x_3460_ = lean_box(0);
v___x_3461_ = lean_box(0);
v___x_3462_ = l_Lean_OptionFlags_ofOptions(v___x_2989_);
v___x_3463_ = lean_obj_once(&l_main___closed__20, &l_main___closed__20_once, _init_l_main___closed__20);
v___x_3464_ = ((lean_object*)(l_main___closed__23));
lean_inc_n(v___y_3391_, 3);
v___x_3465_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3465_, 0, v___y_3391_);
lean_ctor_set(v___x_3465_, 1, v___x_3382_);
lean_ctor_set(v___x_3465_, 2, v___x_2958_);
v___x_3466_ = lean_obj_once(&l_main___closed__24, &l_main___closed__24_once, _init_l_main___closed__24);
v___x_3467_ = lean_obj_once(&l_main___closed__27, &l_main___closed__27_once, _init_l_main___closed__27);
v___x_3468_ = ((lean_object*)(l_main___closed__28));
v___x_3469_ = l_Lean_Options_empty;
v___x_3470_ = lean_obj_once(&l_main___closed__29, &l_main___closed__29_once, _init_l_main___closed__29);
v___x_3471_ = lean_obj_once(&l_main___closed__30, &l_main___closed__30_once, _init_l_main___closed__30);
v___x_3472_ = lean_obj_once(&l_main___closed__31, &l_main___closed__31_once, _init_l_main___closed__31);
lean_inc_ref(v___x_3465_);
v___x_3473_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3453_);
lean_ctor_set(v___x_3473_, 1, v___x_3463_);
lean_ctor_set(v___x_3473_, 2, v___x_3464_);
lean_ctor_set(v___x_3473_, 3, v___x_3465_);
lean_ctor_set(v___x_3473_, 4, v___x_3466_);
lean_ctor_set(v___x_3473_, 5, v___x_3467_);
lean_ctor_set(v___x_3473_, 6, v___x_3470_);
lean_ctor_set(v___x_3473_, 7, v___x_3471_);
lean_ctor_set(v___x_3473_, 8, v___x_3472_);
lean_ctor_set(v___x_3473_, 9, v___x_3468_);
v___x_3474_ = lean_st_mk_ref(v___x_3473_);
v___x_3475_ = l_Lean_inheritedTraceOptions;
v___x_3476_ = lean_st_ref_get(v___x_3475_);
lean_inc_ref(v___x_2989_);
lean_inc(v_head_2948_);
v___x_3477_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3477_, 0, v_head_2948_);
lean_ctor_set(v___x_3477_, 1, v___x_3456_);
lean_ctor_set(v___x_3477_, 2, v___x_2989_);
lean_ctor_set(v___x_3477_, 3, v___x_3457_);
lean_ctor_set(v___x_3477_, 4, v___y_3391_);
lean_ctor_set(v___x_3477_, 5, v___x_2958_);
lean_ctor_set(v___x_3477_, 6, v___x_2988_);
lean_ctor_set(v___x_3477_, 7, v___x_3458_);
lean_ctor_set(v___x_3477_, 8, v___y_3391_);
lean_ctor_set(v___x_3477_, 9, v___x_3459_);
lean_ctor_set(v___x_3477_, 10, v___x_3460_);
lean_ctor_set(v___x_3477_, 11, v___x_3476_);
v___x_3478_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3478_, 0, v___x_3477_);
lean_ctor_set(v___x_3478_, 1, v___x_2988_);
lean_ctor_set(v___x_3478_, 2, v___x_3461_);
lean_ctor_set_uint16(v___x_3478_, sizeof(void*)*3, v___x_3462_);
lean_ctor_set_uint8(v___x_3478_, sizeof(void*)*3 + 2, v___x_2972_);
lean_ctor_set_uint8(v___x_3478_, sizeof(void*)*3 + 3, v___x_2972_);
v___x_3479_ = lean_st_ref_get(v___x_3474_);
v_env_3480_ = lean_ctor_get(v___x_3479_, 0);
lean_inc_ref(v_env_3480_);
lean_dec(v___x_3479_);
v___x_3481_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3480_);
lean_dec_ref(v_env_3480_);
v___x_3482_ = 512;
v___x_3483_ = lean_uint16_land(v___x_3462_, v___x_3482_);
v___x_3484_ = 0;
v___x_3485_ = lean_uint16_dec_eq(v___x_3483_, v___x_3484_);
if (v___x_3485_ == 0)
{
if (v___x_3401_ == 0)
{
v___y_3353_ = v___x_3462_;
v___y_3354_ = v___x_3465_;
v___y_3355_ = v___x_3455_;
v___y_3356_ = v___x_3469_;
v___y_3357_ = v___x_3454_;
v___y_3358_ = v___x_3459_;
v___y_3359_ = v___x_3401_;
v___y_3360_ = v___x_3466_;
v___y_3361_ = v___x_3463_;
v___y_3362_ = v___x_3467_;
v___y_3363_ = v___x_3460_;
v___y_3364_ = v___x_2958_;
v___y_3365_ = v___x_3456_;
v___y_3366_ = v___y_3387_;
v___y_3367_ = v___x_3461_;
v___y_3368_ = v___x_3464_;
v___y_3369_ = v___x_3478_;
v___y_3370_ = v___x_3471_;
v___y_3371_ = v___x_3472_;
v___y_3372_ = v___x_3474_;
v___y_3373_ = v___x_3468_;
v___y_3374_ = v___x_3401_;
v___y_3375_ = v___x_3481_;
v___y_3376_ = v___x_3470_;
v___y_3377_ = v___y_3391_;
v___y_3378_ = v___x_3401_;
goto v___jp_3352_;
}
else
{
v___y_3325_ = v___x_3459_;
v___y_3326_ = v___x_3401_;
v___y_3327_ = v___x_3467_;
v___y_3328_ = v___x_3460_;
v___y_3329_ = v___x_2958_;
v___y_3330_ = v___x_3469_;
v___y_3331_ = v___x_3461_;
v___y_3332_ = v___y_3387_;
v___y_3333_ = v___x_3456_;
v___y_3334_ = v___x_3478_;
v___y_3335_ = v___x_3471_;
v___y_3336_ = v___x_3462_;
v___y_3337_ = v___x_3465_;
v___y_3338_ = v___x_3472_;
v___y_3339_ = v___x_3455_;
v___y_3340_ = v___x_3469_;
v___y_3341_ = v___x_3474_;
v___y_3342_ = v___x_3468_;
v___y_3343_ = v___x_3454_;
v___y_3344_ = v___x_3466_;
v___y_3345_ = v___x_3401_;
v___y_3346_ = v___x_3463_;
v___y_3347_ = v___x_3467_;
v___y_3348_ = v___x_3470_;
v___y_3349_ = v___y_3391_;
v___y_3350_ = v___x_3464_;
v___y_3351_ = v___x_3481_;
goto v___jp_3324_;
}
}
else
{
v___y_3353_ = v___x_3462_;
v___y_3354_ = v___x_3465_;
v___y_3355_ = v___x_3455_;
v___y_3356_ = v___x_3469_;
v___y_3357_ = v___x_3454_;
v___y_3358_ = v___x_3459_;
v___y_3359_ = v___x_3401_;
v___y_3360_ = v___x_3466_;
v___y_3361_ = v___x_3463_;
v___y_3362_ = v___x_3467_;
v___y_3363_ = v___x_3460_;
v___y_3364_ = v___x_2958_;
v___y_3365_ = v___x_3456_;
v___y_3366_ = v___y_3387_;
v___y_3367_ = v___x_3461_;
v___y_3368_ = v___x_3464_;
v___y_3369_ = v___x_3478_;
v___y_3370_ = v___x_3471_;
v___y_3371_ = v___x_3472_;
v___y_3372_ = v___x_3474_;
v___y_3373_ = v___x_3468_;
v___y_3374_ = v___x_3401_;
v___y_3375_ = v___x_3481_;
v___y_3376_ = v___x_3470_;
v___y_3377_ = v___y_3391_;
v___y_3378_ = v___x_2972_;
goto v___jp_3352_;
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
v___jp_3499_:
{
lean_object* v___x_3504_; lean_object* v_toEnvExtension_3505_; lean_object* v_asyncMode_3506_; lean_object* v___x_3507_; lean_object* v_importedEntries_3508_; lean_object* v_state_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; uint8_t v___x_3512_; 
v___x_3504_ = l_Lean_IR_declMapExt;
v_toEnvExtension_3505_ = lean_ctor_get(v___x_3504_, 0);
v_asyncMode_3506_ = lean_ctor_get(v_toEnvExtension_3505_, 2);
lean_inc(v___y_3502_);
lean_inc_ref(v___y_3503_);
v___x_3507_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2962_, v_toEnvExtension_3505_, v___y_3503_, v_asyncMode_3506_, v___y_3502_);
v_importedEntries_3508_ = lean_ctor_get(v___x_3507_, 0);
lean_inc_ref(v_importedEntries_3508_);
v_state_3509_ = lean_ctor_get(v___x_3507_, 1);
lean_inc(v_state_3509_);
lean_dec(v___x_3507_);
v___x_3510_ = lean_array_get_borrowed(v___x_2963_, v_importedEntries_3508_, v___y_3501_);
v___x_3511_ = lean_array_get_size(v___x_3510_);
v___x_3512_ = lean_nat_dec_lt(v___x_2988_, v___x_3511_);
if (v___x_3512_ == 0)
{
v___y_3387_ = v___y_3500_;
v___y_3388_ = v_toEnvExtension_3505_;
v___y_3389_ = v___y_3503_;
v___y_3390_ = v_importedEntries_3508_;
v___y_3391_ = v___y_3502_;
v___y_3392_ = v___y_3501_;
v___y_3393_ = v_state_3509_;
goto v___jp_3386_;
}
else
{
uint8_t v___x_3513_; 
v___x_3513_ = lean_nat_dec_le(v___x_3511_, v___x_3511_);
if (v___x_3513_ == 0)
{
if (v___x_3512_ == 0)
{
v___y_3387_ = v___y_3500_;
v___y_3388_ = v_toEnvExtension_3505_;
v___y_3389_ = v___y_3503_;
v___y_3390_ = v_importedEntries_3508_;
v___y_3391_ = v___y_3502_;
v___y_3392_ = v___y_3501_;
v___y_3393_ = v_state_3509_;
goto v___jp_3386_;
}
else
{
size_t v___x_3514_; size_t v___x_3515_; lean_object* v___x_3516_; 
v___x_3514_ = ((size_t)0ULL);
v___x_3515_ = lean_usize_of_nat(v___x_3511_);
lean_inc_ref(v___y_3503_);
v___x_3516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3503_, v___x_3510_, v___x_3514_, v___x_3515_, v_state_3509_);
v___y_3387_ = v___y_3500_;
v___y_3388_ = v_toEnvExtension_3505_;
v___y_3389_ = v___y_3503_;
v___y_3390_ = v_importedEntries_3508_;
v___y_3391_ = v___y_3502_;
v___y_3392_ = v___y_3501_;
v___y_3393_ = v___x_3516_;
goto v___jp_3386_;
}
}
else
{
size_t v___x_3517_; size_t v___x_3518_; lean_object* v___x_3519_; 
v___x_3517_ = ((size_t)0ULL);
v___x_3518_ = lean_usize_of_nat(v___x_3511_);
lean_inc_ref(v___y_3503_);
v___x_3519_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3503_, v___x_3510_, v___x_3517_, v___x_3518_, v_state_3509_);
v___y_3387_ = v___y_3500_;
v___y_3388_ = v_toEnvExtension_3505_;
v___y_3389_ = v___y_3503_;
v___y_3390_ = v_importedEntries_3508_;
v___y_3391_ = v___y_3502_;
v___y_3392_ = v___y_3501_;
v___y_3393_ = v___x_3519_;
goto v___jp_3386_;
}
}
}
v___jp_3520_:
{
uint8_t v___x_3527_; 
v___x_3527_ = lean_nat_dec_lt(v___x_2988_, v___y_3522_);
if (v___x_3527_ == 0)
{
lean_dec_ref(v___y_3523_);
lean_dec(v___y_3522_);
v___y_3500_ = v___y_3521_;
v___y_3501_ = v___y_3525_;
v___y_3502_ = v___y_3524_;
v___y_3503_ = v___y_3526_;
goto v___jp_3499_;
}
else
{
uint8_t v___x_3528_; 
v___x_3528_ = lean_nat_dec_le(v___y_3522_, v___y_3522_);
if (v___x_3528_ == 0)
{
if (v___x_3527_ == 0)
{
lean_dec_ref(v___y_3523_);
lean_dec(v___y_3522_);
v___y_3500_ = v___y_3521_;
v___y_3501_ = v___y_3525_;
v___y_3502_ = v___y_3524_;
v___y_3503_ = v___y_3526_;
goto v___jp_3499_;
}
else
{
size_t v___x_3529_; size_t v___x_3530_; lean_object* v___x_3531_; 
v___x_3529_ = ((size_t)0ULL);
v___x_3530_ = lean_usize_of_nat(v___y_3522_);
lean_dec(v___y_3522_);
v___x_3531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3523_, v___x_3529_, v___x_3530_, v___y_3526_);
lean_dec_ref(v___y_3523_);
v___y_3500_ = v___y_3521_;
v___y_3501_ = v___y_3525_;
v___y_3502_ = v___y_3524_;
v___y_3503_ = v___x_3531_;
goto v___jp_3499_;
}
}
else
{
size_t v___x_3532_; size_t v___x_3533_; lean_object* v___x_3534_; 
v___x_3532_ = ((size_t)0ULL);
v___x_3533_ = lean_usize_of_nat(v___y_3522_);
lean_dec(v___y_3522_);
v___x_3534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3523_, v___x_3532_, v___x_3533_, v___y_3526_);
lean_dec_ref(v___y_3523_);
v___y_3500_ = v___y_3521_;
v___y_3501_ = v___y_3525_;
v___y_3502_ = v___y_3524_;
v___y_3503_ = v___x_3534_;
goto v___jp_3499_;
}
}
}
v___jp_3535_:
{
lean_object* v___x_3540_; uint8_t v___x_3541_; 
v___x_3540_ = lean_array_get_size(v___y_3539_);
v___x_3541_ = lean_nat_dec_lt(v___x_2988_, v___x_3540_);
if (v___x_3541_ == 0)
{
lean_inc(v___y_3536_);
v___y_3521_ = v___y_3536_;
v___y_3522_ = v___x_3540_;
v___y_3523_ = v___y_3539_;
v___y_3524_ = v___y_3536_;
v___y_3525_ = v___y_3538_;
v___y_3526_ = v___y_3537_;
goto v___jp_3520_;
}
else
{
uint8_t v___x_3542_; 
v___x_3542_ = lean_nat_dec_le(v___x_3540_, v___x_3540_);
if (v___x_3542_ == 0)
{
if (v___x_3541_ == 0)
{
lean_inc(v___y_3536_);
v___y_3521_ = v___y_3536_;
v___y_3522_ = v___x_3540_;
v___y_3523_ = v___y_3539_;
v___y_3524_ = v___y_3536_;
v___y_3525_ = v___y_3538_;
v___y_3526_ = v___y_3537_;
goto v___jp_3520_;
}
else
{
size_t v___x_3543_; size_t v___x_3544_; lean_object* v___x_3545_; 
v___x_3543_ = ((size_t)0ULL);
v___x_3544_ = lean_usize_of_nat(v___x_3540_);
v___x_3545_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3539_, v___x_3543_, v___x_3544_, v___y_3537_);
lean_inc(v___y_3536_);
v___y_3521_ = v___y_3536_;
v___y_3522_ = v___x_3540_;
v___y_3523_ = v___y_3539_;
v___y_3524_ = v___y_3536_;
v___y_3525_ = v___y_3538_;
v___y_3526_ = v___x_3545_;
goto v___jp_3520_;
}
}
else
{
size_t v___x_3546_; size_t v___x_3547_; lean_object* v___x_3548_; 
v___x_3546_ = ((size_t)0ULL);
v___x_3547_ = lean_usize_of_nat(v___x_3540_);
v___x_3548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3539_, v___x_3546_, v___x_3547_, v___y_3537_);
lean_inc(v___y_3536_);
v___y_3521_ = v___y_3536_;
v___y_3522_ = v___x_3540_;
v___y_3523_ = v___y_3539_;
v___y_3524_ = v___y_3536_;
v___y_3525_ = v___y_3538_;
v___y_3526_ = v___x_3548_;
goto v___jp_3520_;
}
}
}
v___jp_3550_:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___f_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3552_ = l_Lean_instInhabitedImportState_default;
v___x_3553_ = lean_box(v___x_3385_);
v___x_3554_ = lean_box(v___y_3551_);
v___x_3555_ = lean_box(v___x_2985_);
v___x_3556_ = lean_box(v___x_3549_);
v___x_3557_ = lean_box(v___x_2972_);
lean_inc_ref(v___x_2989_);
lean_inc(v_name_2968_);
v___f_3558_ = lean_alloc_closure((void*)(l_main___lam__0___boxed), 11, 10);
lean_closure_set(v___f_3558_, 0, v___x_3552_);
lean_closure_set(v___f_3558_, 1, v___x_3384_);
lean_closure_set(v___f_3558_, 2, v___x_3553_);
lean_closure_set(v___f_3558_, 3, v_importArts_2970_);
lean_closure_set(v___f_3558_, 4, v___x_3554_);
lean_closure_set(v___f_3558_, 5, v___x_3555_);
lean_closure_set(v___f_3558_, 6, v_name_2968_);
lean_closure_set(v___f_3558_, 7, v___x_3556_);
lean_closure_set(v___f_3558_, 8, v___x_2989_);
lean_closure_set(v___f_3558_, 9, v___x_3557_);
v___x_3559_ = lean_alloc_closure((void*)(l_Lean_withImporting___boxed), 3, 2);
lean_closure_set(v___x_3559_, 0, lean_box(0));
lean_closure_set(v___x_3559_, 1, v___f_3558_);
v___x_3560_ = lean_box(0);
v___x_3561_ = l_Lean_profileitIOUnsafe___redArg(v___x_3380_, v___x_2989_, v___x_3559_, v___x_3560_);
if (lean_obj_tag(v___x_3561_) == 0)
{
lean_object* v_a_3562_; lean_object* v___x_3563_; lean_object* v_ext_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
v_a_3562_ = lean_ctor_get(v___x_3561_, 0);
lean_inc(v_a_3562_);
lean_dec_ref_known(v___x_3561_, 1);
v___x_3563_ = l_Lean_Compiler_CSimp_ext;
v_ext_3564_ = lean_ctor_get(v___x_3563_, 1);
lean_inc(v_name_2968_);
v___x_3565_ = l_Lean_Environment_setMainModule(v_a_3562_, v_name_2968_);
v___x_3566_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v___x_3567_ = l_Lean_PersistentEnvExtension_setState___redArg(v___x_3566_, v___x_3565_, v_package_x3f_2969_);
lean_inc_ref(v_ext_3564_);
v___x_3568_ = l_main___elam__0___redArg(v___x_3560_, v___x_2957_, v_ext_3564_, v___x_3567_);
if (lean_obj_tag(v___x_3568_) == 0)
{
lean_object* v_a_3569_; lean_object* v___x_3570_; lean_object* v_ext_3571_; lean_object* v___x_3572_; 
v_a_3569_ = lean_ctor_get(v___x_3568_, 0);
lean_inc(v_a_3569_);
lean_dec_ref_known(v___x_3568_, 1);
v___x_3570_ = l_Lean_Meta_instanceExtension;
v_ext_3571_ = lean_ctor_get(v___x_3570_, 1);
lean_inc_ref(v_ext_3571_);
v___x_3572_ = l_main___elam__0___redArg(v___x_3560_, v___x_2957_, v_ext_3571_, v_a_3569_);
if (lean_obj_tag(v___x_3572_) == 0)
{
lean_object* v_a_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
v_a_3573_ = lean_ctor_get(v___x_3572_, 0);
lean_inc(v_a_3573_);
lean_dec_ref_known(v___x_3572_, 1);
v___x_3574_ = l_Lean_classExtension;
v___x_3575_ = l_main___elam__0___redArg(v___x_3560_, v___x_2959_, v___x_3574_, v_a_3573_);
if (lean_obj_tag(v___x_3575_) == 0)
{
lean_object* v_a_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; 
v_a_3576_ = lean_ctor_get(v___x_3575_, 0);
lean_inc(v_a_3576_);
lean_dec_ref_known(v___x_3575_, 1);
v___x_3577_ = l_Lean_Meta_Match_Extension_extension;
v___x_3578_ = l_main___elam__0___redArg(v___x_3560_, v___x_2960_, v___x_3577_, v_a_3576_);
if (lean_obj_tag(v___x_3578_) == 0)
{
lean_object* v_a_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3606_; 
v_a_3579_ = lean_ctor_get(v___x_3578_, 0);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3578_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3581_ = v___x_3578_;
v_isShared_3582_ = v_isSharedCheck_3606_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_a_3579_);
lean_dec(v___x_3578_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3606_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3583_; 
v___x_3583_ = l_Lean_Environment_getModuleIdx_x3f(v_a_3579_, v_name_2968_);
if (lean_obj_tag(v___x_3583_) == 1)
{
lean_object* v_val_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; uint8_t v___x_3589_; 
lean_del_object(v___x_3581_);
v_val_3584_ = lean_ctor_get(v___x_3583_, 0);
lean_inc(v_val_3584_);
lean_dec_ref_known(v___x_3583_, 1);
v___x_3585_ = l_Lean_Compiler_LCNF_impureSigExt;
v___x_3586_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2961_, v___x_3585_, v_a_3579_, v_val_3584_, v___x_3385_);
v___x_3587_ = lean_array_get_size(v___x_3586_);
v___x_3588_ = ((lean_object*)(l_main___closed__32));
v___x_3589_ = lean_nat_dec_lt(v___x_2988_, v___x_3587_);
if (v___x_3589_ == 0)
{
lean_dec_ref(v___x_3586_);
v___y_3536_ = v___x_3560_;
v___y_3537_ = v_a_3579_;
v___y_3538_ = v_val_3584_;
v___y_3539_ = v___x_3588_;
goto v___jp_3535_;
}
else
{
uint8_t v___x_3590_; 
v___x_3590_ = lean_nat_dec_le(v___x_3587_, v___x_3587_);
if (v___x_3590_ == 0)
{
if (v___x_3589_ == 0)
{
lean_dec_ref(v___x_3586_);
v___y_3536_ = v___x_3560_;
v___y_3537_ = v_a_3579_;
v___y_3538_ = v_val_3584_;
v___y_3539_ = v___x_3588_;
goto v___jp_3535_;
}
else
{
size_t v___x_3591_; size_t v___x_3592_; lean_object* v___x_3593_; 
v___x_3591_ = ((size_t)0ULL);
v___x_3592_ = lean_usize_of_nat(v___x_3587_);
lean_inc(v_a_3579_);
v___x_3593_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_a_3579_, v___x_3586_, v___x_3591_, v___x_3592_, v___x_3588_);
lean_dec_ref(v___x_3586_);
v___y_3536_ = v___x_3560_;
v___y_3537_ = v_a_3579_;
v___y_3538_ = v_val_3584_;
v___y_3539_ = v___x_3593_;
goto v___jp_3535_;
}
}
else
{
size_t v___x_3594_; size_t v___x_3595_; lean_object* v___x_3596_; 
v___x_3594_ = ((size_t)0ULL);
v___x_3595_ = lean_usize_of_nat(v___x_3587_);
lean_inc(v_a_3579_);
v___x_3596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_a_3579_, v___x_3586_, v___x_3594_, v___x_3595_, v___x_3588_);
lean_dec_ref(v___x_3586_);
v___y_3536_ = v___x_3560_;
v___y_3537_ = v_a_3579_;
v___y_3538_ = v_val_3584_;
v___y_3539_ = v___x_3596_;
goto v___jp_3535_;
}
}
}
else
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3604_; 
lean_dec(v___x_3583_);
lean_dec(v_a_3579_);
lean_dec_ref(v___x_2989_);
lean_del_object(v___x_2982_);
lean_dec(v_fst_2979_);
lean_dec(v_head_2952_);
lean_del_object(v___x_2950_);
lean_dec(v_head_2948_);
lean_del_object(v___x_2946_);
v___x_3597_ = ((lean_object*)(l_main___closed__33));
v___x_3598_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2968_, v___x_2985_);
v___x_3599_ = lean_string_append(v___x_3597_, v___x_3598_);
lean_dec_ref(v___x_3598_);
v___x_3600_ = ((lean_object*)(l_main___closed__34));
v___x_3601_ = lean_string_append(v___x_3599_, v___x_3600_);
v___x_3602_ = lean_mk_io_user_error(v___x_3601_);
if (v_isShared_3582_ == 0)
{
lean_ctor_set_tag(v___x_3581_, 1);
lean_ctor_set(v___x_3581_, 0, v___x_3602_);
v___x_3604_ = v___x_3581_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v___x_3602_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
}
}
else
{
lean_object* v_a_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3614_; 
lean_dec_ref(v___x_2989_);
lean_del_object(v___x_2982_);
lean_dec(v_fst_2979_);
lean_dec(v_name_2968_);
lean_dec(v_head_2952_);
lean_del_object(v___x_2950_);
lean_dec(v_head_2948_);
lean_del_object(v___x_2946_);
v_a_3607_ = lean_ctor_get(v___x_3578_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3578_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3609_ = v___x_3578_;
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_a_3607_);
lean_dec(v___x_3578_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3612_; 
if (v_isShared_3610_ == 0)
{
v___x_3612_ = v___x_3609_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_a_3607_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
return v___x_3612_;
}
}
}
}
else
{
lean_object* v_a_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3622_; 
lean_dec_ref(v___x_2989_);
lean_del_object(v___x_2982_);
lean_dec(v_fst_2979_);
lean_dec(v_name_2968_);
lean_dec(v_head_2952_);
lean_del_object(v___x_2950_);
lean_dec(v_head_2948_);
lean_del_object(v___x_2946_);
v_a_3615_ = lean_ctor_get(v___x_3575_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3575_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3617_ = v___x_3575_;
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_a_3615_);
lean_dec(v___x_3575_);
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
else
{
lean_object* v_a_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3630_; 
lean_dec_ref(v___x_2989_);
lean_del_object(v___x_2982_);
lean_dec(v_fst_2979_);
lean_dec(v_name_2968_);
lean_dec(v_head_2952_);
lean_del_object(v___x_2950_);
lean_dec(v_head_2948_);
lean_del_object(v___x_2946_);
v_a_3623_ = lean_ctor_get(v___x_3572_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3625_ = v___x_3572_;
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_a_3623_);
lean_dec(v___x_3572_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3628_; 
if (v_isShared_3626_ == 0)
{
v___x_3628_ = v___x_3625_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_a_3623_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
}
}
else
{
lean_object* v_a_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3638_; 
lean_dec_ref(v___x_2989_);
lean_del_object(v___x_2982_);
lean_dec(v_fst_2979_);
lean_dec(v_name_2968_);
lean_dec(v_head_2952_);
lean_del_object(v___x_2950_);
lean_dec(v_head_2948_);
lean_del_object(v___x_2946_);
v_a_3631_ = lean_ctor_get(v___x_3568_, 0);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3568_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3633_ = v___x_3568_;
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_a_3631_);
lean_dec(v___x_3568_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v___x_3636_; 
if (v_isShared_3634_ == 0)
{
v___x_3636_ = v___x_3633_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_a_3631_);
v___x_3636_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
return v___x_3636_;
}
}
}
}
else
{
lean_object* v_a_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3646_; 
lean_dec_ref(v___x_2989_);
lean_del_object(v___x_2982_);
lean_dec(v_fst_2979_);
lean_dec(v_package_x3f_2969_);
lean_dec(v_name_2968_);
lean_dec(v_head_2952_);
lean_del_object(v___x_2950_);
lean_dec(v_head_2948_);
lean_del_object(v___x_2946_);
v_a_3639_ = lean_ctor_get(v___x_3561_, 0);
v_isSharedCheck_3646_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3646_ == 0)
{
v___x_3641_ = v___x_3561_;
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_a_3639_);
lean_dec(v___x_3561_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3644_; 
if (v_isShared_3642_ == 0)
{
v___x_3644_ = v___x_3641_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v_a_3639_);
v___x_3644_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
return v___x_3644_;
}
}
}
}
}
else
{
lean_object* v_a_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3655_; 
lean_dec_ref(v___x_2989_);
lean_del_object(v___x_2982_);
lean_dec(v_fst_2979_);
lean_dec(v_importArts_2970_);
lean_dec(v_package_x3f_2969_);
lean_dec(v_name_2968_);
lean_dec(v_head_2952_);
lean_del_object(v___x_2950_);
lean_dec(v_head_2948_);
lean_del_object(v___x_2946_);
v_a_3648_ = lean_ctor_get(v___x_3379_, 0);
v_isSharedCheck_3655_ = !lean_is_exclusive(v___x_3379_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3650_ = v___x_3379_;
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_a_3648_);
lean_dec(v___x_3379_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v___x_3653_; 
if (v_isShared_3651_ == 0)
{
v___x_3653_ = v___x_3650_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v_a_3648_);
v___x_3653_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
return v___x_3653_;
}
}
}
v___jp_2990_:
{
lean_object* v___x_3012_; lean_object* v_messages_3013_; lean_object* v_env_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3139_; 
v___x_3012_ = lean_st_ref_get(v___y_3009_);
lean_dec(v___y_3009_);
v_messages_3013_ = lean_ctor_get(v___x_3012_, 7);
v_env_3014_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3139_ == 0)
{
lean_object* v_unused_3140_; lean_object* v_unused_3141_; lean_object* v_unused_3142_; lean_object* v_unused_3143_; lean_object* v_unused_3144_; lean_object* v_unused_3145_; lean_object* v_unused_3146_; lean_object* v_unused_3147_; 
v_unused_3140_ = lean_ctor_get(v___x_3012_, 9);
lean_dec(v_unused_3140_);
v_unused_3141_ = lean_ctor_get(v___x_3012_, 8);
lean_dec(v_unused_3141_);
v_unused_3142_ = lean_ctor_get(v___x_3012_, 6);
lean_dec(v_unused_3142_);
v_unused_3143_ = lean_ctor_get(v___x_3012_, 5);
lean_dec(v_unused_3143_);
v_unused_3144_ = lean_ctor_get(v___x_3012_, 4);
lean_dec(v_unused_3144_);
v_unused_3145_ = lean_ctor_get(v___x_3012_, 3);
lean_dec(v_unused_3145_);
v_unused_3146_ = lean_ctor_get(v___x_3012_, 2);
lean_dec(v_unused_3146_);
v_unused_3147_ = lean_ctor_get(v___x_3012_, 1);
lean_dec(v_unused_3147_);
v___x_3016_ = v___x_3012_;
v_isShared_3017_ = v_isSharedCheck_3139_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_messages_3013_);
lean_inc(v_env_3014_);
lean_dec(v___x_3012_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3139_;
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
lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3129_; 
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3129_ == 0)
{
lean_object* v_unused_3130_; 
v_unused_3130_ = lean_ctor_get(v___x_3020_, 0);
lean_dec(v_unused_3130_);
v___x_3022_ = v___x_3020_;
v_isShared_3023_ = v_isSharedCheck_3129_;
goto v_resetjp_3021_;
}
else
{
lean_dec(v___x_3020_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3129_;
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
lean_inc(v_head_2948_);
v___x_3026_ = l_System_FilePath_addExtension(v_head_2948_, v___x_3025_);
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
if (v_isShared_2983_ == 0)
{
lean_ctor_set(v___x_2982_, 1, v_a_3028_);
lean_ctor_set(v___x_2982_, 0, v___x_3026_);
v___x_3035_ = v___x_2982_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v___x_3026_);
lean_ctor_set(v_reuseFailAlloc_3108_, 1, v_a_3028_);
v___x_3035_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
lean_object* v___x_3037_; 
lean_inc(v_head_2948_);
if (v_isShared_2951_ == 0)
{
lean_ctor_set_tag(v___x_2950_, 0);
lean_ctor_set(v___x_2950_, 1, v_a_3030_);
v___x_3037_ = v___x_2950_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_head_2948_);
lean_ctor_set(v_reuseFailAlloc_3107_, 1, v_a_3030_);
v___x_3037_ = v_reuseFailAlloc_3107_;
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
v___x_3044_ = lean_io_prim_handle_mk(v_head_2952_, v___x_3043_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; uint16_t v___x_3048_; lean_object* v___x_3050_; 
lean_dec(v_head_2952_);
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
lean_inc(v_a_3045_);
lean_dec_ref_known(v___x_3044_, 1);
v___x_3046_ = ((lean_object*)(l_main___closed__12));
v___x_3047_ = l_Lean_Core_getMaxHeartbeats(v___y_3006_);
v___x_3048_ = l_Lean_OptionFlags_ofOptions(v___y_3006_);
lean_inc_ref(v___y_3007_);
lean_inc_ref(v___y_3005_);
lean_inc_ref(v___y_3000_);
lean_inc_ref(v___y_3008_);
lean_inc_ref(v___y_3003_);
lean_inc_ref(v___y_3001_);
lean_inc_ref(v___y_3011_);
lean_inc(v___y_3002_);
lean_inc_ref(v_env_3014_);
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 9, v___y_3007_);
lean_ctor_set(v___x_3016_, 8, v___y_3005_);
lean_ctor_set(v___x_3016_, 7, v___y_3000_);
lean_ctor_set(v___x_3016_, 6, v___y_3008_);
lean_ctor_set(v___x_3016_, 5, v___y_3003_);
lean_ctor_set(v___x_3016_, 4, v___y_3001_);
lean_ctor_set(v___x_3016_, 3, v___y_3004_);
lean_ctor_set(v___x_3016_, 2, v___y_3011_);
lean_ctor_set(v___x_3016_, 1, v___y_3002_);
v___x_3050_ = v___x_3016_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_env_3014_);
lean_ctor_set(v_reuseFailAlloc_3076_, 1, v___y_3002_);
lean_ctor_set(v_reuseFailAlloc_3076_, 2, v___y_3011_);
lean_ctor_set(v_reuseFailAlloc_3076_, 3, v___y_3004_);
lean_ctor_set(v_reuseFailAlloc_3076_, 4, v___y_3001_);
lean_ctor_set(v_reuseFailAlloc_3076_, 5, v___y_3003_);
lean_ctor_set(v_reuseFailAlloc_3076_, 6, v___y_3008_);
lean_ctor_set(v_reuseFailAlloc_3076_, 7, v___y_3000_);
lean_ctor_set(v_reuseFailAlloc_3076_, 8, v___y_3005_);
lean_ctor_set(v_reuseFailAlloc_3076_, 9, v___y_3007_);
v___x_3050_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___f_3055_; lean_object* v___x_3056_; 
v___x_3051_ = lean_box(v___x_3048_);
v___x_3052_ = lean_box(v___y_2992_);
v___x_3053_ = lean_box(v___x_2972_);
v___x_3054_ = lean_box(v___x_3024_);
lean_inc(v___y_2997_);
lean_inc(v___y_2994_);
lean_inc(v___y_2991_);
lean_inc(v___y_2995_);
lean_inc_ref(v___y_2999_);
lean_inc_ref(v___y_2993_);
lean_inc_ref(v___y_2996_);
v___f_3055_ = lean_alloc_closure((void*)(l_main___lam__1___boxed), 19, 18);
lean_closure_set(v___f_3055_, 0, v___x_3050_);
lean_closure_set(v___f_3055_, 1, v___y_2996_);
lean_closure_set(v___f_3055_, 2, v___x_3051_);
lean_closure_set(v___f_3055_, 3, v_name_2968_);
lean_closure_set(v___f_3055_, 4, v_a_3045_);
lean_closure_set(v___f_3055_, 5, v___x_3052_);
lean_closure_set(v___f_3055_, 6, v___y_2993_);
lean_closure_set(v___f_3055_, 7, v_head_2948_);
lean_closure_set(v___f_3055_, 8, v___y_2999_);
lean_closure_set(v___f_3055_, 9, v___y_2998_);
lean_closure_set(v___f_3055_, 10, v___y_2995_);
lean_closure_set(v___f_3055_, 11, v___x_3047_);
lean_closure_set(v___f_3055_, 12, v___y_2991_);
lean_closure_set(v___f_3055_, 13, v___y_2994_);
lean_closure_set(v___f_3055_, 14, v___x_2988_);
lean_closure_set(v___f_3055_, 15, v___y_2997_);
lean_closure_set(v___f_3055_, 16, v___x_3053_);
lean_closure_set(v___f_3055_, 17, v___x_3054_);
v___x_3056_ = l_Lean_profileitIOUnsafe___redArg(v___x_3046_, v___x_2989_, v___f_3055_, v___y_3010_);
lean_dec_ref(v___x_2989_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v___x_3057_; uint8_t v___x_3058_; 
lean_dec_ref_known(v___x_3056_, 1);
v___x_3057_ = lean_display_cumulative_profiling_times();
v___x_3058_ = lean_unbox(v_fst_2979_);
lean_dec(v_fst_2979_);
if (v___x_3058_ == 0)
{
lean_dec_ref(v_env_3014_);
goto v___jp_2919_;
}
else
{
lean_object* v___x_3059_; 
v___x_3059_ = l_Lean_Environment_displayStats(v_env_3014_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_dec_ref_known(v___x_3059_, 1);
goto v___jp_2919_;
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
lean_dec_ref(v_env_3014_);
lean_dec(v_fst_2979_);
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
lean_dec_ref_known(v___x_3044_, 1);
lean_del_object(v___x_3016_);
lean_dec_ref(v_env_3014_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_2998_);
lean_dec_ref(v___x_2989_);
lean_dec(v_fst_2979_);
lean_dec(v_name_2968_);
lean_dec(v_head_2948_);
v___x_3077_ = ((lean_object*)(l_main___closed__13));
v___x_3078_ = lean_string_append(v___x_3077_, v_head_2952_);
lean_dec(v_head_2952_);
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
v___x_3085_ = l_main___boxed__const__2;
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
lean_del_object(v___x_3016_);
lean_dec_ref(v_env_3014_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_2998_);
lean_dec_ref(v___x_2989_);
lean_dec(v_fst_2979_);
lean_dec(v_name_2968_);
lean_dec(v_head_2952_);
lean_dec(v_head_2948_);
v_a_3099_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3101_ = v___x_3042_;
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_a_3099_);
lean_dec(v___x_3042_);
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
lean_dec(v_a_3028_);
lean_dec_ref(v___x_3026_);
lean_del_object(v___x_3016_);
lean_dec_ref(v_env_3014_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_2998_);
lean_dec_ref(v___x_2989_);
lean_del_object(v___x_2982_);
lean_dec(v_fst_2979_);
lean_dec(v_name_2968_);
lean_dec(v_head_2952_);
lean_del_object(v___x_2950_);
lean_dec(v_head_2948_);
v_a_3109_ = lean_ctor_get(v___x_3029_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3029_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3111_ = v___x_3029_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_3029_);
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
lean_dec_ref(v___x_3026_);
lean_del_object(v___x_3016_);
lean_dec_ref(v_env_3014_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_2998_);
lean_dec_ref(v___x_2989_);
lean_del_object(v___x_2982_);
lean_dec(v_fst_2979_);
lean_dec(v_name_2968_);
lean_dec(v_head_2952_);
lean_del_object(v___x_2950_);
lean_dec(v_head_2948_);
v_a_3117_ = lean_ctor_get(v___x_3027_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3119_ = v___x_3027_;
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_3027_);
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
lean_del_object(v___x_3016_);
lean_dec_ref(v_env_3014_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_2998_);
lean_dec_ref(v___x_2989_);
lean_del_object(v___x_2982_);
lean_dec(v_fst_2979_);
lean_dec(v_name_2968_);
lean_dec(v_head_2952_);
lean_del_object(v___x_2950_);
lean_dec(v_head_2948_);
v___x_3125_ = l_main___boxed__const__2;
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 0, v___x_3125_);
v___x_3127_ = v___x_3022_;
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
lean_del_object(v___x_3016_);
lean_dec_ref(v_env_3014_);
lean_dec_ref(v_messages_3013_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_2998_);
lean_dec_ref(v___x_2989_);
lean_del_object(v___x_2982_);
lean_dec(v_fst_2979_);
lean_dec(v_name_2968_);
lean_dec(v_head_2952_);
lean_del_object(v___x_2950_);
lean_dec(v_head_2948_);
v_a_3131_ = lean_ctor_get(v___x_3020_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3133_ = v___x_3020_;
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3020_);
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
v___jp_3148_:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; size_t v_sz_3185_; size_t v___x_3186_; lean_object* v___x_3187_; 
lean_inc_ref(v___y_3175_);
v___x_3182_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3182_, 0, v___y_3181_);
lean_ctor_set(v___x_3182_, 1, v_nextMacroScope_3160_);
lean_ctor_set(v___x_3182_, 2, v_ngen_3161_);
lean_ctor_set(v___x_3182_, 3, v_auxDeclNGen_3162_);
lean_ctor_set(v___x_3182_, 4, v_traceState_3163_);
lean_ctor_set(v___x_3182_, 5, v___y_3175_);
lean_ctor_set(v___x_3182_, 6, v_recordedDeps_3164_);
lean_ctor_set(v___x_3182_, 7, v_messages_3165_);
lean_ctor_set(v___x_3182_, 8, v_infoState_3166_);
lean_ctor_set(v___x_3182_, 9, v_snapshotTasks_3167_);
v___x_3183_ = lean_st_ref_put(v___y_3176_, v___x_3182_);
v___x_3184_ = lean_box(0);
v_sz_3185_ = lean_array_size(v___y_3169_);
v___x_3186_ = ((size_t)0ULL);
v___x_3187_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(v___y_3169_, v_sz_3185_, v___x_3186_, v___x_3184_, v___y_3179_, v___y_3176_);
lean_dec_ref(v___y_3169_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_dec_ref_known(v___x_3187_, 1);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3176_);
v___y_2991_ = v___y_3150_;
v___y_2992_ = v___y_3149_;
v___y_2993_ = v___y_3151_;
v___y_2994_ = v___y_3152_;
v___y_2995_ = v___y_3154_;
v___y_2996_ = v___y_3153_;
v___y_2997_ = v___y_3157_;
v___y_2998_ = v___y_3156_;
v___y_2999_ = v___y_3155_;
v___y_3000_ = v___y_3158_;
v___y_3001_ = v___y_3173_;
v___y_3002_ = v___y_3174_;
v___y_3003_ = v___y_3175_;
v___y_3004_ = v___y_3159_;
v___y_3005_ = v___y_3168_;
v___y_3006_ = v___y_3170_;
v___y_3007_ = v___y_3172_;
v___y_3008_ = v___y_3177_;
v___y_3009_ = v___y_3171_;
v___y_3010_ = v___y_3178_;
v___y_3011_ = v___y_3180_;
goto v___jp_2990_;
}
else
{
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_dec_ref_known(v___x_3187_, 1);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3176_);
v___y_2991_ = v___y_3150_;
v___y_2992_ = v___y_3149_;
v___y_2993_ = v___y_3151_;
v___y_2994_ = v___y_3152_;
v___y_2995_ = v___y_3154_;
v___y_2996_ = v___y_3153_;
v___y_2997_ = v___y_3157_;
v___y_2998_ = v___y_3156_;
v___y_2999_ = v___y_3155_;
v___y_3000_ = v___y_3158_;
v___y_3001_ = v___y_3173_;
v___y_3002_ = v___y_3174_;
v___y_3003_ = v___y_3175_;
v___y_3004_ = v___y_3159_;
v___y_3005_ = v___y_3168_;
v___y_3006_ = v___y_3170_;
v___y_3007_ = v___y_3172_;
v___y_3008_ = v___y_3177_;
v___y_3009_ = v___y_3171_;
v___y_3010_ = v___y_3178_;
v___y_3011_ = v___y_3180_;
goto v___jp_2990_;
}
else
{
lean_object* v_a_3188_; uint8_t v___x_3189_; 
v_a_3188_ = lean_ctor_get(v___x_3187_, 0);
lean_inc(v_a_3188_);
lean_dec_ref_known(v___x_3187_, 1);
v___x_3189_ = l_Lean_Exception_isInterrupt(v_a_3188_);
if (v___x_3189_ == 0)
{
lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3190_ = l_Lean_Exception_toMessageData(v_a_3188_);
v___x_3191_ = l_Lean_logError___at___00main_spec__13(v___x_3190_, v___y_3179_, v___y_3176_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3179_);
if (lean_obj_tag(v___x_3191_) == 0)
{
lean_dec_ref_known(v___x_3191_, 1);
v___y_2991_ = v___y_3150_;
v___y_2992_ = v___y_3149_;
v___y_2993_ = v___y_3151_;
v___y_2994_ = v___y_3152_;
v___y_2995_ = v___y_3154_;
v___y_2996_ = v___y_3153_;
v___y_2997_ = v___y_3157_;
v___y_2998_ = v___y_3156_;
v___y_2999_ = v___y_3155_;
v___y_3000_ = v___y_3158_;
v___y_3001_ = v___y_3173_;
v___y_3002_ = v___y_3174_;
v___y_3003_ = v___y_3175_;
v___y_3004_ = v___y_3159_;
v___y_3005_ = v___y_3168_;
v___y_3006_ = v___y_3170_;
v___y_3007_ = v___y_3172_;
v___y_3008_ = v___y_3177_;
v___y_3009_ = v___y_3171_;
v___y_3010_ = v___y_3178_;
v___y_3011_ = v___y_3180_;
goto v___jp_2990_;
}
else
{
lean_object* v___x_3192_; lean_object* v___x_3193_; 
lean_dec_ref_known(v___x_3191_, 1);
lean_dec(v___y_3178_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3159_);
lean_dec(v___y_3156_);
lean_dec_ref(v___x_2989_);
lean_del_object(v___x_2982_);
lean_dec(v_fst_2979_);
lean_dec(v_name_2968_);
lean_dec(v_head_2952_);
lean_del_object(v___x_2950_);
lean_dec(v_head_2948_);
v___x_3192_ = lean_obj_once(&l_main___closed__17, &l_main___closed__17_once, _init_l_main___closed__17);
v___x_3193_ = l_panic___at___00main_spec__5(v___x_3192_);
return v___x_3193_;
}
}
else
{
lean_dec(v_a_3188_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3176_);
v___y_2991_ = v___y_3150_;
v___y_2992_ = v___y_3149_;
v___y_2993_ = v___y_3151_;
v___y_2994_ = v___y_3152_;
v___y_2995_ = v___y_3154_;
v___y_2996_ = v___y_3153_;
v___y_2997_ = v___y_3157_;
v___y_2998_ = v___y_3156_;
v___y_2999_ = v___y_3155_;
v___y_3000_ = v___y_3158_;
v___y_3001_ = v___y_3173_;
v___y_3002_ = v___y_3174_;
v___y_3003_ = v___y_3175_;
v___y_3004_ = v___y_3159_;
v___y_3005_ = v___y_3168_;
v___y_3006_ = v___y_3170_;
v___y_3007_ = v___y_3172_;
v___y_3008_ = v___y_3177_;
v___y_3009_ = v___y_3171_;
v___y_3010_ = v___y_3178_;
v___y_3011_ = v___y_3180_;
goto v___jp_2990_;
}
}
}
}
v___jp_3194_:
{
lean_object* v_toCold_3221_; lean_object* v_currRecDepth_3222_; lean_object* v_ref_3223_; uint8_t v_suppressElabErrors_3224_; uint8_t v_isRecordingDeps_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3276_; 
v_toCold_3221_ = lean_ctor_get(v___y_3219_, 0);
v_currRecDepth_3222_ = lean_ctor_get(v___y_3219_, 1);
v_ref_3223_ = lean_ctor_get(v___y_3219_, 2);
v_suppressElabErrors_3224_ = lean_ctor_get_uint8(v___y_3219_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3225_ = lean_ctor_get_uint8(v___y_3219_, sizeof(void*)*3 + 3);
v_isSharedCheck_3276_ = !lean_is_exclusive(v___y_3219_);
if (v_isSharedCheck_3276_ == 0)
{
v___x_3227_ = v___y_3219_;
v_isShared_3228_ = v_isSharedCheck_3276_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_ref_3223_);
lean_inc(v_currRecDepth_3222_);
lean_inc(v_toCold_3221_);
lean_dec(v___y_3219_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3276_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v_fileName_3229_; lean_object* v_fileMap_3230_; lean_object* v_currNamespace_3231_; lean_object* v_openDecls_3232_; lean_object* v_initHeartbeats_3233_; lean_object* v_maxHeartbeats_3234_; lean_object* v_quotContext_3235_; lean_object* v_currMacroScope_3236_; lean_object* v_cancelTk_x3f_3237_; lean_object* v_inheritedTraceOptions_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3273_; 
v_fileName_3229_ = lean_ctor_get(v_toCold_3221_, 0);
v_fileMap_3230_ = lean_ctor_get(v_toCold_3221_, 1);
v_currNamespace_3231_ = lean_ctor_get(v_toCold_3221_, 4);
v_openDecls_3232_ = lean_ctor_get(v_toCold_3221_, 5);
v_initHeartbeats_3233_ = lean_ctor_get(v_toCold_3221_, 6);
v_maxHeartbeats_3234_ = lean_ctor_get(v_toCold_3221_, 7);
v_quotContext_3235_ = lean_ctor_get(v_toCold_3221_, 8);
v_currMacroScope_3236_ = lean_ctor_get(v_toCold_3221_, 9);
v_cancelTk_x3f_3237_ = lean_ctor_get(v_toCold_3221_, 10);
v_inheritedTraceOptions_3238_ = lean_ctor_get(v_toCold_3221_, 11);
v_isSharedCheck_3273_ = !lean_is_exclusive(v_toCold_3221_);
if (v_isSharedCheck_3273_ == 0)
{
lean_object* v_unused_3274_; lean_object* v_unused_3275_; 
v_unused_3274_ = lean_ctor_get(v_toCold_3221_, 3);
lean_dec(v_unused_3274_);
v_unused_3275_ = lean_ctor_get(v_toCold_3221_, 2);
lean_dec(v_unused_3275_);
v___x_3240_ = v_toCold_3221_;
v_isShared_3241_ = v_isSharedCheck_3273_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_inheritedTraceOptions_3238_);
lean_inc(v_cancelTk_x3f_3237_);
lean_inc(v_currMacroScope_3236_);
lean_inc(v_quotContext_3235_);
lean_inc(v_maxHeartbeats_3234_);
lean_inc(v_initHeartbeats_3233_);
lean_inc(v_openDecls_3232_);
lean_inc(v_currNamespace_3231_);
lean_inc(v_fileMap_3230_);
lean_inc(v_fileName_3229_);
lean_dec(v_toCold_3221_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3273_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3245_; 
v___x_3242_ = l_Lean_maxRecDepth;
v___x_3243_ = l_Lean_Option_get___at___00main_spec__8(v___x_2989_, v___x_3242_);
lean_inc_ref(v___x_2989_);
if (v_isShared_3241_ == 0)
{
lean_ctor_set(v___x_3240_, 3, v___x_3243_);
lean_ctor_set(v___x_3240_, 2, v___x_2989_);
v___x_3245_ = v___x_3240_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_fileName_3229_);
lean_ctor_set(v_reuseFailAlloc_3272_, 1, v_fileMap_3230_);
lean_ctor_set(v_reuseFailAlloc_3272_, 2, v___x_2989_);
lean_ctor_set(v_reuseFailAlloc_3272_, 3, v___x_3243_);
lean_ctor_set(v_reuseFailAlloc_3272_, 4, v_currNamespace_3231_);
lean_ctor_set(v_reuseFailAlloc_3272_, 5, v_openDecls_3232_);
lean_ctor_set(v_reuseFailAlloc_3272_, 6, v_initHeartbeats_3233_);
lean_ctor_set(v_reuseFailAlloc_3272_, 7, v_maxHeartbeats_3234_);
lean_ctor_set(v_reuseFailAlloc_3272_, 8, v_quotContext_3235_);
lean_ctor_set(v_reuseFailAlloc_3272_, 9, v_currMacroScope_3236_);
lean_ctor_set(v_reuseFailAlloc_3272_, 10, v_cancelTk_x3f_3237_);
lean_ctor_set(v_reuseFailAlloc_3272_, 11, v_inheritedTraceOptions_3238_);
v___x_3245_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
lean_object* v___x_3247_; 
if (v_isShared_3228_ == 0)
{
lean_ctor_set(v___x_3227_, 0, v___x_3245_);
v___x_3247_ = v___x_3227_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v___x_3245_);
lean_ctor_set(v_reuseFailAlloc_3271_, 1, v_currRecDepth_3222_);
lean_ctor_set(v_reuseFailAlloc_3271_, 2, v_ref_3223_);
lean_ctor_set_uint8(v_reuseFailAlloc_3271_, sizeof(void*)*3 + 2, v_suppressElabErrors_3224_);
lean_ctor_set_uint8(v_reuseFailAlloc_3271_, sizeof(void*)*3 + 3, v_isRecordingDeps_3225_);
v___x_3247_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
lean_object* v___x_3248_; lean_object* v_env_3249_; lean_object* v_nextMacroScope_3250_; lean_object* v_ngen_3251_; lean_object* v_auxDeclNGen_3252_; lean_object* v_traceState_3253_; lean_object* v_recordedDeps_3254_; lean_object* v_messages_3255_; lean_object* v_infoState_3256_; lean_object* v_snapshotTasks_3257_; lean_object* v___x_3258_; uint8_t v___x_3259_; 
lean_ctor_set_uint16(v___x_3247_, sizeof(void*)*3, v___y_3205_);
v___x_3248_ = lean_st_ref_take(v___y_3220_);
v_env_3249_ = lean_ctor_get(v___x_3248_, 0);
lean_inc_ref(v_env_3249_);
v_nextMacroScope_3250_ = lean_ctor_get(v___x_3248_, 1);
lean_inc(v_nextMacroScope_3250_);
v_ngen_3251_ = lean_ctor_get(v___x_3248_, 2);
lean_inc_ref(v_ngen_3251_);
v_auxDeclNGen_3252_ = lean_ctor_get(v___x_3248_, 3);
lean_inc_ref(v_auxDeclNGen_3252_);
v_traceState_3253_ = lean_ctor_get(v___x_3248_, 4);
lean_inc_ref(v_traceState_3253_);
v_recordedDeps_3254_ = lean_ctor_get(v___x_3248_, 6);
lean_inc_ref(v_recordedDeps_3254_);
v_messages_3255_ = lean_ctor_get(v___x_3248_, 7);
lean_inc_ref(v_messages_3255_);
v_infoState_3256_ = lean_ctor_get(v___x_3248_, 8);
lean_inc_ref(v_infoState_3256_);
v_snapshotTasks_3257_ = lean_ctor_get(v___x_3248_, 9);
lean_inc_ref(v_snapshotTasks_3257_);
lean_dec(v___x_3248_);
v___x_3258_ = lean_array_get_size(v___y_3208_);
v___x_3259_ = lean_nat_dec_lt(v___x_2988_, v___x_3258_);
if (v___x_3259_ == 0)
{
lean_object* v___x_3260_; 
lean_inc_ref(v___y_3212_);
v___x_3260_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3212_, v_env_3249_, v___x_2964_);
v___y_3149_ = v___y_3196_;
v___y_3150_ = v___y_3195_;
v___y_3151_ = v___y_3197_;
v___y_3152_ = v___y_3198_;
v___y_3153_ = v___y_3200_;
v___y_3154_ = v___y_3199_;
v___y_3155_ = v___y_3203_;
v___y_3156_ = v___y_3202_;
v___y_3157_ = v___y_3201_;
v___y_3158_ = v___y_3204_;
v___y_3159_ = v___y_3206_;
v_nextMacroScope_3160_ = v_nextMacroScope_3250_;
v_ngen_3161_ = v_ngen_3251_;
v_auxDeclNGen_3162_ = v_auxDeclNGen_3252_;
v_traceState_3163_ = v_traceState_3253_;
v_recordedDeps_3164_ = v_recordedDeps_3254_;
v_messages_3165_ = v_messages_3255_;
v_infoState_3166_ = v_infoState_3256_;
v_snapshotTasks_3167_ = v_snapshotTasks_3257_;
v___y_3168_ = v___y_3207_;
v___y_3169_ = v___y_3208_;
v___y_3170_ = v___y_3209_;
v___y_3171_ = v___y_3210_;
v___y_3172_ = v___y_3211_;
v___y_3173_ = v___y_3213_;
v___y_3174_ = v___y_3214_;
v___y_3175_ = v___y_3215_;
v___y_3176_ = v___y_3220_;
v___y_3177_ = v___y_3216_;
v___y_3178_ = v___y_3217_;
v___y_3179_ = v___x_3247_;
v___y_3180_ = v___y_3218_;
v___y_3181_ = v___x_3260_;
goto v___jp_3148_;
}
else
{
uint8_t v___x_3261_; 
v___x_3261_ = lean_nat_dec_le(v___x_3258_, v___x_3258_);
if (v___x_3261_ == 0)
{
if (v___x_3259_ == 0)
{
lean_object* v___x_3262_; 
lean_inc_ref(v___y_3212_);
v___x_3262_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3212_, v_env_3249_, v___x_2964_);
v___y_3149_ = v___y_3196_;
v___y_3150_ = v___y_3195_;
v___y_3151_ = v___y_3197_;
v___y_3152_ = v___y_3198_;
v___y_3153_ = v___y_3200_;
v___y_3154_ = v___y_3199_;
v___y_3155_ = v___y_3203_;
v___y_3156_ = v___y_3202_;
v___y_3157_ = v___y_3201_;
v___y_3158_ = v___y_3204_;
v___y_3159_ = v___y_3206_;
v_nextMacroScope_3160_ = v_nextMacroScope_3250_;
v_ngen_3161_ = v_ngen_3251_;
v_auxDeclNGen_3162_ = v_auxDeclNGen_3252_;
v_traceState_3163_ = v_traceState_3253_;
v_recordedDeps_3164_ = v_recordedDeps_3254_;
v_messages_3165_ = v_messages_3255_;
v_infoState_3166_ = v_infoState_3256_;
v_snapshotTasks_3167_ = v_snapshotTasks_3257_;
v___y_3168_ = v___y_3207_;
v___y_3169_ = v___y_3208_;
v___y_3170_ = v___y_3209_;
v___y_3171_ = v___y_3210_;
v___y_3172_ = v___y_3211_;
v___y_3173_ = v___y_3213_;
v___y_3174_ = v___y_3214_;
v___y_3175_ = v___y_3215_;
v___y_3176_ = v___y_3220_;
v___y_3177_ = v___y_3216_;
v___y_3178_ = v___y_3217_;
v___y_3179_ = v___x_3247_;
v___y_3180_ = v___y_3218_;
v___y_3181_ = v___x_3262_;
goto v___jp_3148_;
}
else
{
size_t v___x_3263_; size_t v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3263_ = ((size_t)0ULL);
v___x_3264_ = lean_usize_of_nat(v___x_3258_);
v___x_3265_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(v___y_3208_, v___x_3263_, v___x_3264_, v___x_2964_);
lean_inc_ref(v___y_3212_);
v___x_3266_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3212_, v_env_3249_, v___x_3265_);
v___y_3149_ = v___y_3196_;
v___y_3150_ = v___y_3195_;
v___y_3151_ = v___y_3197_;
v___y_3152_ = v___y_3198_;
v___y_3153_ = v___y_3200_;
v___y_3154_ = v___y_3199_;
v___y_3155_ = v___y_3203_;
v___y_3156_ = v___y_3202_;
v___y_3157_ = v___y_3201_;
v___y_3158_ = v___y_3204_;
v___y_3159_ = v___y_3206_;
v_nextMacroScope_3160_ = v_nextMacroScope_3250_;
v_ngen_3161_ = v_ngen_3251_;
v_auxDeclNGen_3162_ = v_auxDeclNGen_3252_;
v_traceState_3163_ = v_traceState_3253_;
v_recordedDeps_3164_ = v_recordedDeps_3254_;
v_messages_3165_ = v_messages_3255_;
v_infoState_3166_ = v_infoState_3256_;
v_snapshotTasks_3167_ = v_snapshotTasks_3257_;
v___y_3168_ = v___y_3207_;
v___y_3169_ = v___y_3208_;
v___y_3170_ = v___y_3209_;
v___y_3171_ = v___y_3210_;
v___y_3172_ = v___y_3211_;
v___y_3173_ = v___y_3213_;
v___y_3174_ = v___y_3214_;
v___y_3175_ = v___y_3215_;
v___y_3176_ = v___y_3220_;
v___y_3177_ = v___y_3216_;
v___y_3178_ = v___y_3217_;
v___y_3179_ = v___x_3247_;
v___y_3180_ = v___y_3218_;
v___y_3181_ = v___x_3266_;
goto v___jp_3148_;
}
}
else
{
size_t v___x_3267_; size_t v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___x_3267_ = ((size_t)0ULL);
v___x_3268_ = lean_usize_of_nat(v___x_3258_);
v___x_3269_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(v___y_3208_, v___x_3267_, v___x_3268_, v___x_2964_);
lean_inc_ref(v___y_3212_);
v___x_3270_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3212_, v_env_3249_, v___x_3269_);
v___y_3149_ = v___y_3196_;
v___y_3150_ = v___y_3195_;
v___y_3151_ = v___y_3197_;
v___y_3152_ = v___y_3198_;
v___y_3153_ = v___y_3200_;
v___y_3154_ = v___y_3199_;
v___y_3155_ = v___y_3203_;
v___y_3156_ = v___y_3202_;
v___y_3157_ = v___y_3201_;
v___y_3158_ = v___y_3204_;
v___y_3159_ = v___y_3206_;
v_nextMacroScope_3160_ = v_nextMacroScope_3250_;
v_ngen_3161_ = v_ngen_3251_;
v_auxDeclNGen_3162_ = v_auxDeclNGen_3252_;
v_traceState_3163_ = v_traceState_3253_;
v_recordedDeps_3164_ = v_recordedDeps_3254_;
v_messages_3165_ = v_messages_3255_;
v_infoState_3166_ = v_infoState_3256_;
v_snapshotTasks_3167_ = v_snapshotTasks_3257_;
v___y_3168_ = v___y_3207_;
v___y_3169_ = v___y_3208_;
v___y_3170_ = v___y_3209_;
v___y_3171_ = v___y_3210_;
v___y_3172_ = v___y_3211_;
v___y_3173_ = v___y_3213_;
v___y_3174_ = v___y_3214_;
v___y_3175_ = v___y_3215_;
v___y_3176_ = v___y_3220_;
v___y_3177_ = v___y_3216_;
v___y_3178_ = v___y_3217_;
v___y_3179_ = v___x_3247_;
v___y_3180_ = v___y_3218_;
v___y_3181_ = v___x_3270_;
goto v___jp_3148_;
}
}
}
}
}
}
}
v___jp_3277_:
{
lean_object* v___x_3304_; lean_object* v_env_3305_; lean_object* v_nextMacroScope_3306_; lean_object* v_ngen_3307_; lean_object* v_auxDeclNGen_3308_; lean_object* v_traceState_3309_; lean_object* v_recordedDeps_3310_; lean_object* v_messages_3311_; lean_object* v_infoState_3312_; lean_object* v_snapshotTasks_3313_; lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3322_; 
v___x_3304_ = lean_st_ref_take(v___y_3294_);
v_env_3305_ = lean_ctor_get(v___x_3304_, 0);
v_nextMacroScope_3306_ = lean_ctor_get(v___x_3304_, 1);
v_ngen_3307_ = lean_ctor_get(v___x_3304_, 2);
v_auxDeclNGen_3308_ = lean_ctor_get(v___x_3304_, 3);
v_traceState_3309_ = lean_ctor_get(v___x_3304_, 4);
v_recordedDeps_3310_ = lean_ctor_get(v___x_3304_, 6);
v_messages_3311_ = lean_ctor_get(v___x_3304_, 7);
v_infoState_3312_ = lean_ctor_get(v___x_3304_, 8);
v_snapshotTasks_3313_ = lean_ctor_get(v___x_3304_, 9);
v_isSharedCheck_3322_ = !lean_is_exclusive(v___x_3304_);
if (v_isSharedCheck_3322_ == 0)
{
lean_object* v_unused_3323_; 
v_unused_3323_ = lean_ctor_get(v___x_3304_, 5);
lean_dec(v_unused_3323_);
v___x_3315_ = v___x_3304_;
v_isShared_3316_ = v_isSharedCheck_3322_;
goto v_resetjp_3314_;
}
else
{
lean_inc(v_snapshotTasks_3313_);
lean_inc(v_infoState_3312_);
lean_inc(v_messages_3311_);
lean_inc(v_recordedDeps_3310_);
lean_inc(v_traceState_3309_);
lean_inc(v_auxDeclNGen_3308_);
lean_inc(v_ngen_3307_);
lean_inc(v_nextMacroScope_3306_);
lean_inc(v_env_3305_);
lean_dec(v___x_3304_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3322_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v___x_3317_; lean_object* v___x_3319_; 
v___x_3317_ = l_Lean_Kernel_enableDiag(v_env_3305_, v___y_3298_);
lean_inc_ref(v___y_3300_);
if (v_isShared_3316_ == 0)
{
lean_ctor_set(v___x_3315_, 5, v___y_3300_);
lean_ctor_set(v___x_3315_, 0, v___x_3317_);
v___x_3319_ = v___x_3315_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v___x_3317_);
lean_ctor_set(v_reuseFailAlloc_3321_, 1, v_nextMacroScope_3306_);
lean_ctor_set(v_reuseFailAlloc_3321_, 2, v_ngen_3307_);
lean_ctor_set(v_reuseFailAlloc_3321_, 3, v_auxDeclNGen_3308_);
lean_ctor_set(v_reuseFailAlloc_3321_, 4, v_traceState_3309_);
lean_ctor_set(v_reuseFailAlloc_3321_, 5, v___y_3300_);
lean_ctor_set(v_reuseFailAlloc_3321_, 6, v_recordedDeps_3310_);
lean_ctor_set(v_reuseFailAlloc_3321_, 7, v_messages_3311_);
lean_ctor_set(v_reuseFailAlloc_3321_, 8, v_infoState_3312_);
lean_ctor_set(v_reuseFailAlloc_3321_, 9, v_snapshotTasks_3313_);
v___x_3319_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
lean_object* v___x_3320_; 
v___x_3320_ = lean_st_ref_put(v___y_3294_, v___x_3319_);
lean_inc(v___y_3294_);
v___y_3195_ = v___y_3279_;
v___y_3196_ = v___y_3278_;
v___y_3197_ = v___y_3280_;
v___y_3198_ = v___y_3281_;
v___y_3199_ = v___y_3283_;
v___y_3200_ = v___y_3282_;
v___y_3201_ = v___y_3286_;
v___y_3202_ = v___y_3285_;
v___y_3203_ = v___y_3284_;
v___y_3204_ = v___y_3288_;
v___y_3205_ = v___y_3289_;
v___y_3206_ = v___y_3290_;
v___y_3207_ = v___y_3291_;
v___y_3208_ = v___y_3292_;
v___y_3209_ = v___y_3293_;
v___y_3210_ = v___y_3294_;
v___y_3211_ = v___y_3295_;
v___y_3212_ = v___y_3296_;
v___y_3213_ = v___y_3297_;
v___y_3214_ = v___y_3299_;
v___y_3215_ = v___y_3300_;
v___y_3216_ = v___y_3301_;
v___y_3217_ = v___y_3302_;
v___y_3218_ = v___y_3303_;
v___y_3219_ = v___y_3287_;
v___y_3220_ = v___y_3294_;
goto v___jp_3194_;
}
}
}
v___jp_3324_:
{
if (v___y_3351_ == 0)
{
v___y_3278_ = v___y_3326_;
v___y_3279_ = v___y_3325_;
v___y_3280_ = v___y_3327_;
v___y_3281_ = v___y_3328_;
v___y_3282_ = v___y_3330_;
v___y_3283_ = v___y_3329_;
v___y_3284_ = v___y_3333_;
v___y_3285_ = v___y_3332_;
v___y_3286_ = v___y_3331_;
v___y_3287_ = v___y_3334_;
v___y_3288_ = v___y_3335_;
v___y_3289_ = v___y_3336_;
v___y_3290_ = v___y_3337_;
v___y_3291_ = v___y_3338_;
v___y_3292_ = v___y_3339_;
v___y_3293_ = v___y_3340_;
v___y_3294_ = v___y_3341_;
v___y_3295_ = v___y_3342_;
v___y_3296_ = v___y_3343_;
v___y_3297_ = v___y_3344_;
v___y_3298_ = v___y_3345_;
v___y_3299_ = v___y_3346_;
v___y_3300_ = v___y_3347_;
v___y_3301_ = v___y_3348_;
v___y_3302_ = v___y_3349_;
v___y_3303_ = v___y_3350_;
goto v___jp_3277_;
}
else
{
lean_inc(v___y_3341_);
v___y_3195_ = v___y_3325_;
v___y_3196_ = v___y_3326_;
v___y_3197_ = v___y_3327_;
v___y_3198_ = v___y_3328_;
v___y_3199_ = v___y_3329_;
v___y_3200_ = v___y_3330_;
v___y_3201_ = v___y_3331_;
v___y_3202_ = v___y_3332_;
v___y_3203_ = v___y_3333_;
v___y_3204_ = v___y_3335_;
v___y_3205_ = v___y_3336_;
v___y_3206_ = v___y_3337_;
v___y_3207_ = v___y_3338_;
v___y_3208_ = v___y_3339_;
v___y_3209_ = v___y_3340_;
v___y_3210_ = v___y_3341_;
v___y_3211_ = v___y_3342_;
v___y_3212_ = v___y_3343_;
v___y_3213_ = v___y_3344_;
v___y_3214_ = v___y_3346_;
v___y_3215_ = v___y_3347_;
v___y_3216_ = v___y_3348_;
v___y_3217_ = v___y_3349_;
v___y_3218_ = v___y_3350_;
v___y_3219_ = v___y_3334_;
v___y_3220_ = v___y_3341_;
goto v___jp_3194_;
}
}
v___jp_3352_:
{
if (v___y_3375_ == 0)
{
v___y_3325_ = v___y_3358_;
v___y_3326_ = v___y_3359_;
v___y_3327_ = v___y_3362_;
v___y_3328_ = v___y_3363_;
v___y_3329_ = v___y_3364_;
v___y_3330_ = v___y_3356_;
v___y_3331_ = v___y_3367_;
v___y_3332_ = v___y_3366_;
v___y_3333_ = v___y_3365_;
v___y_3334_ = v___y_3369_;
v___y_3335_ = v___y_3370_;
v___y_3336_ = v___y_3353_;
v___y_3337_ = v___y_3354_;
v___y_3338_ = v___y_3371_;
v___y_3339_ = v___y_3355_;
v___y_3340_ = v___y_3356_;
v___y_3341_ = v___y_3372_;
v___y_3342_ = v___y_3373_;
v___y_3343_ = v___y_3357_;
v___y_3344_ = v___y_3360_;
v___y_3345_ = v___y_3378_;
v___y_3346_ = v___y_3361_;
v___y_3347_ = v___y_3362_;
v___y_3348_ = v___y_3376_;
v___y_3349_ = v___y_3377_;
v___y_3350_ = v___y_3368_;
v___y_3351_ = v___y_3374_;
goto v___jp_3324_;
}
else
{
v___y_3278_ = v___y_3359_;
v___y_3279_ = v___y_3358_;
v___y_3280_ = v___y_3362_;
v___y_3281_ = v___y_3363_;
v___y_3282_ = v___y_3356_;
v___y_3283_ = v___y_3364_;
v___y_3284_ = v___y_3365_;
v___y_3285_ = v___y_3366_;
v___y_3286_ = v___y_3367_;
v___y_3287_ = v___y_3369_;
v___y_3288_ = v___y_3370_;
v___y_3289_ = v___y_3353_;
v___y_3290_ = v___y_3354_;
v___y_3291_ = v___y_3371_;
v___y_3292_ = v___y_3355_;
v___y_3293_ = v___y_3356_;
v___y_3294_ = v___y_3372_;
v___y_3295_ = v___y_3373_;
v___y_3296_ = v___y_3357_;
v___y_3297_ = v___y_3360_;
v___y_3298_ = v___y_3378_;
v___y_3299_ = v___y_3361_;
v___y_3300_ = v___y_3362_;
v___y_3301_ = v___y_3376_;
v___y_3302_ = v___y_3377_;
v___y_3303_ = v___y_3368_;
goto v___jp_3277_;
}
}
}
}
else
{
lean_object* v_a_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3664_; 
lean_dec(v_importArts_2970_);
lean_dec(v_package_x3f_2969_);
lean_dec(v_name_2968_);
lean_dec(v_head_2952_);
lean_del_object(v___x_2950_);
lean_dec(v_head_2948_);
lean_del_object(v___x_2946_);
v_a_3657_ = lean_ctor_get(v___x_2977_, 0);
v_isSharedCheck_3664_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3659_ = v___x_2977_;
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_a_3657_);
lean_dec(v___x_2977_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3662_; 
if (v_isShared_3660_ == 0)
{
v___x_3662_ = v___x_3659_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_a_3657_);
v___x_3662_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
return v___x_3662_;
}
}
}
}
}
else
{
lean_object* v_a_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3673_; 
lean_del_object(v___x_2955_);
lean_dec(v_tail_2953_);
lean_dec(v_head_2952_);
lean_del_object(v___x_2950_);
lean_dec(v_head_2948_);
lean_del_object(v___x_2946_);
v_a_3666_ = lean_ctor_get(v___x_2966_, 0);
v_isSharedCheck_3673_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3668_ = v___x_2966_;
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_a_3666_);
lean_dec(v___x_2966_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___x_3671_; 
if (v_isShared_3669_ == 0)
{
v___x_3671_ = v___x_3668_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v_a_3666_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
}
}
}
}
}
else
{
lean_dec(v_tail_2943_);
lean_dec_ref_known(v_tail_2942_, 2);
lean_dec_ref_known(v_args_2917_, 2);
goto v___jp_2922_;
}
}
else
{
lean_dec_ref_known(v_args_2917_, 2);
lean_dec(v_tail_2942_);
goto v___jp_2922_;
}
}
else
{
lean_dec(v_args_2917_);
goto v___jp_2922_;
}
v___jp_2919_:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2920_ = l_main___boxed__const__1;
v___x_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2920_);
return v___x_2921_;
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
v___x_2928_ = l_main___boxed__const__2;
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
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_3679_, lean_object* v_a_3680_){
_start:
{
lean_object* v_res_3681_; 
v_res_3681_ = _lean_main(v_args_3679_);
return v_res_3681_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1(lean_object* v_as_3682_, lean_object* v_as_x27_3683_, lean_object* v_b_3684_, lean_object* v_a_3685_){
_start:
{
lean_object* v___x_3687_; 
v___x_3687_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_3683_, v_b_3684_);
return v___x_3687_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___boxed(lean_object* v_as_3688_, lean_object* v_as_x27_3689_, lean_object* v_b_3690_, lean_object* v_a_3691_, lean_object* v___y_3692_){
_start:
{
lean_object* v_res_3693_; 
v_res_3693_ = l_List_forIn_x27_loop___at___00main_spec__1(v_as_3688_, v_as_x27_3689_, v_b_3690_, v_a_3691_);
lean_dec(v_as_x27_3689_);
lean_dec(v_as_3688_);
return v_res_3693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16(lean_object* v___y_3694_, lean_object* v___y_3695_){
_start:
{
lean_object* v___x_3697_; 
v___x_3697_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v___y_3695_);
return v___x_3697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___boxed(lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_){
_start:
{
lean_object* v_res_3701_; 
v_res_3701_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16(v___y_3698_, v___y_3699_);
lean_dec(v___y_3699_);
lean_dec_ref(v___y_3698_);
return v_res_3701_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17(lean_object* v_00_u03b2_3702_, lean_object* v_m_3703_, lean_object* v_a_3704_, lean_object* v_fallback_3705_){
_start:
{
lean_object* v___x_3706_; 
v___x_3706_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_m_3703_, v_a_3704_, v_fallback_3705_);
return v___x_3706_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___boxed(lean_object* v_00_u03b2_3707_, lean_object* v_m_3708_, lean_object* v_a_3709_, lean_object* v_fallback_3710_){
_start:
{
lean_object* v_res_3711_; 
v_res_3711_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17(v_00_u03b2_3707_, v_m_3708_, v_a_3709_, v_fallback_3710_);
lean_dec(v_fallback_3710_);
lean_dec_ref(v_a_3709_);
lean_dec_ref(v_m_3708_);
return v_res_3711_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18(lean_object* v_00_u03b2_3712_, lean_object* v_m_3713_, lean_object* v_a_3714_, lean_object* v_b_3715_){
_start:
{
lean_object* v___x_3716_; 
v___x_3716_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(v_m_3713_, v_a_3714_, v_b_3715_);
return v___x_3716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21(lean_object* v_n_3717_, lean_object* v_as_3718_, lean_object* v_lo_3719_, lean_object* v_hi_3720_, lean_object* v_w_3721_, lean_object* v_hlo_3722_, lean_object* v_hhi_3723_){
_start:
{
lean_object* v___x_3724_; 
v___x_3724_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(v_n_3717_, v_as_3718_, v_lo_3719_, v_hi_3720_);
return v___x_3724_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___boxed(lean_object* v_n_3725_, lean_object* v_as_3726_, lean_object* v_lo_3727_, lean_object* v_hi_3728_, lean_object* v_w_3729_, lean_object* v_hlo_3730_, lean_object* v_hhi_3731_){
_start:
{
lean_object* v_res_3732_; 
v_res_3732_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21(v_n_3725_, v_as_3726_, v_lo_3727_, v_hi_3728_, v_w_3729_, v_hlo_3730_, v_hhi_3731_);
lean_dec(v_hi_3728_);
lean_dec(v_n_3725_);
return v_res_3732_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21(lean_object* v_00_u03b2_3733_, lean_object* v_a_3734_, lean_object* v_fallback_3735_, lean_object* v_x_3736_){
_start:
{
lean_object* v___x_3737_; 
v___x_3737_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg(v_a_3734_, v_fallback_3735_, v_x_3736_);
return v___x_3737_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___boxed(lean_object* v_00_u03b2_3738_, lean_object* v_a_3739_, lean_object* v_fallback_3740_, lean_object* v_x_3741_){
_start:
{
lean_object* v_res_3742_; 
v_res_3742_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21(v_00_u03b2_3738_, v_a_3739_, v_fallback_3740_, v_x_3741_);
lean_dec(v_x_3741_);
lean_dec(v_fallback_3740_);
lean_dec_ref(v_a_3739_);
return v_res_3742_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23(lean_object* v_00_u03b2_3743_, lean_object* v_a_3744_, lean_object* v_x_3745_){
_start:
{
uint8_t v___x_3746_; 
v___x_3746_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg(v_a_3744_, v_x_3745_);
return v___x_3746_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___boxed(lean_object* v_00_u03b2_3747_, lean_object* v_a_3748_, lean_object* v_x_3749_){
_start:
{
uint8_t v_res_3750_; lean_object* v_r_3751_; 
v_res_3750_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23(v_00_u03b2_3747_, v_a_3748_, v_x_3749_);
lean_dec(v_x_3749_);
lean_dec_ref(v_a_3748_);
v_r_3751_ = lean_box(v_res_3750_);
return v_r_3751_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24(lean_object* v_00_u03b2_3752_, lean_object* v_data_3753_){
_start:
{
lean_object* v___x_3754_; 
v___x_3754_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24___redArg(v_data_3753_);
return v___x_3754_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25(lean_object* v_00_u03b2_3755_, lean_object* v_a_3756_, lean_object* v_b_3757_, lean_object* v_x_3758_){
_start:
{
lean_object* v___x_3759_; 
v___x_3759_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25___redArg(v_a_3756_, v_b_3757_, v_x_3758_);
return v___x_3759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31(lean_object* v_n_3760_, lean_object* v_lo_3761_, lean_object* v_hi_3762_, lean_object* v_hhi_3763_, lean_object* v_pivot_3764_, lean_object* v_as_3765_, lean_object* v_i_3766_, lean_object* v_k_3767_, lean_object* v_ilo_3768_, lean_object* v_ik_3769_, lean_object* v_w_3770_){
_start:
{
lean_object* v___x_3771_; 
v___x_3771_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg(v_hi_3762_, v_pivot_3764_, v_as_3765_, v_i_3766_, v_k_3767_);
return v___x_3771_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___boxed(lean_object* v_n_3772_, lean_object* v_lo_3773_, lean_object* v_hi_3774_, lean_object* v_hhi_3775_, lean_object* v_pivot_3776_, lean_object* v_as_3777_, lean_object* v_i_3778_, lean_object* v_k_3779_, lean_object* v_ilo_3780_, lean_object* v_ik_3781_, lean_object* v_w_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31(v_n_3772_, v_lo_3773_, v_hi_3774_, v_hhi_3775_, v_pivot_3776_, v_as_3777_, v_i_3778_, v_k_3779_, v_ilo_3780_, v_ik_3781_, v_w_3782_);
lean_dec_ref(v_pivot_3776_);
lean_dec(v_hi_3774_);
lean_dec(v_lo_3773_);
lean_dec(v_n_3772_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40(lean_object* v_as_3784_, size_t v_sz_3785_, size_t v_i_3786_, lean_object* v_b_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_){
_start:
{
lean_object* v___x_3791_; 
v___x_3791_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg(v_as_3784_, v_sz_3785_, v_i_3786_, v_b_3787_, v___y_3788_);
return v___x_3791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___boxed(lean_object* v_as_3792_, lean_object* v_sz_3793_, lean_object* v_i_3794_, lean_object* v_b_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_){
_start:
{
size_t v_sz_boxed_3799_; size_t v_i_boxed_3800_; lean_object* v_res_3801_; 
v_sz_boxed_3799_ = lean_unbox_usize(v_sz_3793_);
lean_dec(v_sz_3793_);
v_i_boxed_3800_ = lean_unbox_usize(v_i_3794_);
lean_dec(v_i_3794_);
v_res_3801_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40(v_as_3792_, v_sz_boxed_3799_, v_i_boxed_3800_, v_b_3795_, v___y_3796_, v___y_3797_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
lean_dec_ref(v_as_3792_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35(lean_object* v_00_u03b2_3802_, lean_object* v_i_3803_, lean_object* v_source_3804_, lean_object* v_target_3805_){
_start:
{
lean_object* v___x_3806_; 
v___x_3806_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35___redArg(v_i_3803_, v_source_3804_, v_target_3805_);
return v___x_3806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42(uint8_t v___x_3807_, lean_object* v_as_3808_, size_t v_sz_3809_, size_t v_i_3810_, lean_object* v_b_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_){
_start:
{
lean_object* v___x_3815_; 
v___x_3815_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg(v___x_3807_, v_as_3808_, v_sz_3809_, v_i_3810_, v_b_3811_, v___y_3812_);
return v___x_3815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___boxed(lean_object* v___x_3816_, lean_object* v_as_3817_, lean_object* v_sz_3818_, lean_object* v_i_3819_, lean_object* v_b_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_){
_start:
{
uint8_t v___x_41851__boxed_3824_; size_t v_sz_boxed_3825_; size_t v_i_boxed_3826_; lean_object* v_res_3827_; 
v___x_41851__boxed_3824_ = lean_unbox(v___x_3816_);
v_sz_boxed_3825_ = lean_unbox_usize(v_sz_3818_);
lean_dec(v_sz_3818_);
v_i_boxed_3826_ = lean_unbox_usize(v_i_3819_);
lean_dec(v_i_3819_);
v_res_3827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42(v___x_41851__boxed_3824_, v_as_3817_, v_sz_boxed_3825_, v_i_boxed_3826_, v_b_3820_, v___y_3821_, v___y_3822_);
lean_dec(v___y_3822_);
lean_dec_ref(v___y_3821_);
lean_dec_ref(v_as_3817_);
return v_res_3827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51(lean_object* v_as_3828_, size_t v_sz_3829_, size_t v_i_3830_, lean_object* v_b_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_){
_start:
{
lean_object* v___x_3835_; 
v___x_3835_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg(v_as_3828_, v_sz_3829_, v_i_3830_, v_b_3831_, v___y_3832_);
return v___x_3835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___boxed(lean_object* v_as_3836_, lean_object* v_sz_3837_, lean_object* v_i_3838_, lean_object* v_b_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_){
_start:
{
size_t v_sz_boxed_3843_; size_t v_i_boxed_3844_; lean_object* v_res_3845_; 
v_sz_boxed_3843_ = lean_unbox_usize(v_sz_3837_);
lean_dec(v_sz_3837_);
v_i_boxed_3844_ = lean_unbox_usize(v_i_3838_);
lean_dec(v_i_3838_);
v_res_3845_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51(v_as_3836_, v_sz_boxed_3843_, v_i_boxed_3844_, v_b_3839_, v___y_3840_, v___y_3841_);
lean_dec(v___y_3841_);
lean_dec_ref(v___y_3840_);
lean_dec_ref(v_as_3836_);
return v_res_3845_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35_spec__44(lean_object* v_00_u03b2_3846_, lean_object* v_x_3847_, lean_object* v_x_3848_){
_start:
{
lean_object* v___x_3849_; 
v___x_3849_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35_spec__44___redArg(v_x_3847_, v_x_3848_);
return v___x_3849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49(uint8_t v___x_3850_, lean_object* v_as_3851_, size_t v_sz_3852_, size_t v_i_3853_, lean_object* v_b_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_){
_start:
{
lean_object* v___x_3858_; 
v___x_3858_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg(v___x_3850_, v_as_3851_, v_sz_3852_, v_i_3853_, v_b_3854_, v___y_3855_);
return v___x_3858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___boxed(lean_object* v___x_3859_, lean_object* v_as_3860_, lean_object* v_sz_3861_, lean_object* v_i_3862_, lean_object* v_b_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_){
_start:
{
uint8_t v___x_41882__boxed_3867_; size_t v_sz_boxed_3868_; size_t v_i_boxed_3869_; lean_object* v_res_3870_; 
v___x_41882__boxed_3867_ = lean_unbox(v___x_3859_);
v_sz_boxed_3868_ = lean_unbox_usize(v_sz_3861_);
lean_dec(v_sz_3861_);
v_i_boxed_3869_ = lean_unbox_usize(v_i_3862_);
lean_dec(v_i_3862_);
v_res_3870_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49(v___x_41882__boxed_3867_, v_as_3860_, v_sz_boxed_3868_, v_i_boxed_3869_, v_b_3863_, v___y_3864_, v___y_3865_);
lean_dec(v___y_3865_);
lean_dec_ref(v___y_3864_);
lean_dec_ref(v_as_3860_);
return v_res_3870_;
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
